"""无界面、无账号凭据：只读检索嘉立创公开目录，不下单、不替换元件。"""
from pathlib import Path
import concurrent.futures, csv, datetime, hashlib, json, runpy, sys, zipfile
import requests

sys.dont_write_bytecode = True
BASE = Path(__file__).resolve().parents[2]/'FOC驱动与储能'
LIB = BASE.parent/'公共/库'
DOCS = BASE/'文档'
TOOLS = BASE/'工具'
SEARCH = 'https://jlcpcb.com/api/overseas-pcb-order/v1/shoppingCart/smtGood/selectSmtComponentList'
CAD = 'https://easyeda.com/api/products/{code}/components'
SOURCE = 'https://github.com/uPesy/easyeda2kicad.py/blob/master/easyeda2kicad/easyeda/easyeda_api.py'
HEADERS = {'Accept': 'application/json', 'User-Agent': 'FOC-design-library-audit/1.0'}

def search(mpn, refs):
    row = {'原型号': mpn, '位号': refs, '状态': '待查询', '匹配': [], '候选': []}
    try:
        r = requests.post(SEARCH, json={'keyword': mpn, 'currentPage': 1, 'pageSize': 20}, headers=HEADERS, timeout=25)
        row['HTTP状态'] = r.status_code
        r.raise_for_status()
        body = r.json()
        if body.get('code') != 200:
            row['状态'] = '接口返回失败'; row['接口代码'] = body.get('code'); return row
        info = (body.get('data') or {}).get('componentPageInfo') or {}
        row['搜索总数'] = info.get('total', 0)
        for p in info.get('list') or []:
            item = {'型号': p.get('componentModelEn', ''), '立创编号': p.get('componentCode', ''),
                    '厂家': p.get('componentBrandEn', ''), '目录封装': p.get('componentSpecificationEn', ''),
                    '数据手册': p.get('dataManualUrl', ''), '商品链接': p.get('lcscGoodsUrl', '')}
            dest = '匹配' if item['型号'].strip().casefold() == mpn.strip().casefold() else '候选'
            row[dest].append(item)
        row['状态'] = '型号精确匹配' if row['匹配'] else '仅候选待核对' if row['候选'] else '本接口未检出'
    except Exception as exc:
        row['状态'] = '请求失败'; row['错误类型'] = type(exc).__name__
    return row

def catalog_eligible(p):
    if p.get('custom_footprint'):
        return False  # 按原厂尺寸自建；不伪造在线库命中。
    # 封装身份与电路放行分别记录：只为有完整厂家型号和已核针脚的候选查库。
    if p.get('installation','板上') == '待设计':
        return bool(p.get('mpn') and not p['mpn'].startswith('待选') and
                    p.get('manufacturer') not in (None,'','待选') and
                    p.get('pinmap_metadata',{}).get('assignment_verified') is True)
    return p.get('catalog_lookup') is not False and bool(p.get('mpn'))


def main():
    parts = runpy.run_path(str(BASE/'设计数据.py'))['PARTS']
    grouped = {}
    for p in parts:
        # 未定型号的候选模块保留真实设计引脚，但不伪装成已选器件去查询采购库。
        if not catalog_eligible(p):
            continue
        grouped.setdefault(p['mpn'], []).append(p['ref'])
    prior=LIB/'嘉立创元件匹配.json'
    digest=hashlib.sha256((BASE/'设计数据.py').read_bytes()).hexdigest()
    cached=json.loads(prior.read_text(encoding='utf-8')) if prior.exists() else {}
    previous={r['原型号']:r for r in cached.get('型号结果',[])} if '--refresh' not in sys.argv else {}
    rows=[]
    pending=[]
    for mpn,refs in grouped.items():
        if mpn in previous:
            row=previous[mpn]; row['位号']=refs; rows.append(row)
        else: pending.append((mpn,refs))
    if pending:
        with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
            jobs = [pool.submit(search, mpn, refs) for mpn, refs in pending]
            for i, job in enumerate(concurrent.futures.as_completed(jobs), 1):
                rows.append(job.result())
                if i % 20 == 0: print(f'完成 {i}/{len(jobs)} 个型号', flush=True)
    rows.sort(key=lambda x: x['原型号'])
    aliases={'Infineon':'Infineon Technologies','Sensata':'Sensata Tech','OMRON':'Omron Electronics',
             'Vishay':'Vishay Intertech','Murata':'Murata Electronics'}
    for row in rows:
        makers={p.get('manufacturer') for p in parts if p['ref'] in row['位号'] and p.get('manufacturer')}
        if len(makers)>1:
            raise ValueError(f"{row['原型号']}: 同型号位号厂家不一致: {sorted(makers)}")
        maker=next(iter(makers), '')
        row['指定厂家']=maker or '未指定'
        wanted=aliases.get(maker,maker).casefold()
        selected=[m for m in row['匹配'] if m['厂家'].casefold()==wanted]
        row['选定匹配']=selected[0] if len(selected)==1 else None
    oldraw={}
    if (LIB/'嘉立创库数据.zip').exists():
        with zipfile.ZipFile(LIB/'嘉立创库数据.zip') as z:
            oldraw={name:z.read(name) for name in z.namelist()}
    def fetch(row):
        match=row.get('选定匹配')
        if not match:
            row.pop('库数据',None)
            return row,None
        code=match['立创编号']; url=CAD.format(code=code)
        old=row.get('库数据',{})
        name=f'元件_{code}.json'
        if old.get('URL')==url and '--refresh' not in sys.argv:
            if name in oldraw: return row,(name,oldraw[name])
            if '--retry-failed' not in sys.argv and old.get('结果')!='已下载原始符号和封装': return row,None
        item={'URL':url,'结果':'未取得','引脚编号一致':False}
        row['库数据']=item
        try:
            response=requests.get(url,headers=HEADERS,timeout=25)
            item['HTTP状态']=response.status_code
            if response.status_code!=200: return row,None
            payload=response.json(); a=payload.get('result') or {}
            if not payload.get('success'): return row,None
            sd=a.get('dataStr') or {}; pd=(a.get('packageDetail') or {}).get('dataStr') or {}
            if isinstance(sd,str): sd=json.loads(sd)
            if isinstance(pd,str): pd=json.loads(pd)
            pins={}
            for shape in sd.get('shape',[]):
                if shape.startswith('P~'):
                    fields=shape.split('^^')
                    number=fields[4].split('~')[4]; name=fields[3].split('~')[4]
                    pins[number]=name
            pads=sorted({s.split('~')[8] for s in pd.get('shape',[]) if s.startswith('PAD~')})
            actual=(sd.get('head') or {}).get('c_para') or {}
            item.update(结果='已下载原始符号和封装' if pins and pads else '返回数据不完整',
                        符号UUID=a.get('uuid'),封装UUID=(a.get('packageDetail') or {}).get('uuid'),
                        封装名=(a.get('packageDetail') or {}).get('title'),
                        库内厂家型号=actual.get('Manufacturer Part',''),库内供应商编号=actual.get('Supplier Part',''),
                        符号引脚=pins,封装焊盘=pads)
            identity=(item['库内厂家型号'].casefold()==row['原型号'].casefold() and item['库内供应商编号']==code)
            expected=[set(p['pins']) for p in parts if p['ref'] in row['位号']]
            item['型号编号一致']=identity
            item['引脚编号一致']=bool(pins and pads and all(x==set(pins)==set(pads) for x in expected))
            item['核验边界']='仅检查型号、C编号及引脚/焊盘编号集合；未审核功能映射、极性、封装尺寸或焊接工艺。'
            raw=json.dumps(payload,ensure_ascii=False).encode('utf-8')
            item['原始数据SHA256']=hashlib.sha256(raw).hexdigest()
            return row,(f'元件_{code}.json',raw)
        except Exception as exc:
            item['错误类型']=type(exc).__name__
            return row,None
    archive=dict(oldraw)
    with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
        for i,(row,raw) in enumerate(pool.map(fetch,rows),1):
            if raw: archive[raw[0]]=raw[1]
            if i%20==0: print(f'已检查库数据 {i}/{len(rows)}',flush=True)
    with zipfile.ZipFile(LIB/'嘉立创库数据.zip','w',zipfile.ZIP_DEFLATED) as z:
        for name,raw in sorted(archive.items()):z.writestr(name,raw)
    result = {'查询时间': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              '设计源SHA256': hashlib.sha256((BASE/'设计数据.py').read_bytes()).hexdigest(),
              '目录接口': SEARCH, '接口用法来源': SOURCE,
              '官方编辑器扩展API': 'https://prodocs.lceda.cn/cn/api/reference/pro-api.lib_device.search.html',
              '限制': '查询完整型号的板上/明确板外器件，并为有厂家型号及已核引脚表的待设计候选确认封装；不改变候选装配状态。精确匹配仅指完整型号；下载后核对型号及引脚/焊盘编号集合，不代表功能映射、极性及尺寸已经审核；不自动替代。未检出不代表嘉立创全部库均没有该型号。',
              '唯一型号数': len(rows), '电气位号数': len(parts),
              '精确匹配型号数': sum(bool(x['匹配']) for x in rows),
              '精确匹配位号数': sum(len(x['位号']) for x in rows if x['匹配']),
              '型号厂家精确匹配数':sum(bool(x.get('选定匹配')) for x in rows),
              '已保存库数据数':len(archive),'库型号和编号集合一致型号数':sum(x.get('库数据',{}).get('型号编号一致',False) and x.get('库数据',{}).get('引脚编号一致',False) for x in rows),
              '型号结果': rows}
    (LIB/'嘉立创元件匹配.json').write_text(json.dumps(result, ensure_ascii=False, indent=2), encoding='utf-8')
    with (LIB/'嘉立创元件匹配.csv').open('w', encoding='utf-8-sig', newline='') as f:
        w = csv.writer(f); w.writerow(['位号','原型号','状态','立创编号','目录型号','厂家','目录封装','库数据状态','编号集合一致','核验边界'])
        for row in rows:
            matches = [row.get('选定匹配') or {}]
            for item in matches:
                cad=row.get('库数据',{})
                w.writerow([','.join(row['位号']),row['原型号'],row['状态'],item.get('立创编号',''),item.get('型号',''),item.get('厂家',''),item.get('目录封装',''),cad.get('结果','未获取'),cad.get('引脚编号一致',False),'引脚功能、极性和尺寸待人工审核'])
    print(json.dumps({k:result[k] for k in ['唯一型号数','精确匹配型号数','精确匹配位号数','已保存库数据数','库型号和编号集合一致型号数']}, ensure_ascii=False))

def refresh_cached():
    """仅重绑已核验的相同完整型号；新增型号必须走在线查询。"""
    parts=runpy.run_path(str(BASE/'设计数据.py'))['PARTS']
    path=LIB/'嘉立创元件匹配.json'
    result=json.loads(path.read_text(encoding='utf-8'))
    rows={r['原型号']:r for r in result['型号结果']}
    current={p['mpn'] for p in parts if catalog_eligible(p)}
    assert current==set(rows), '存在新增/删除型号，必须在线重新查询'
    for row in rows.values():
        selected=[p for p in parts if p['mpn']==row['原型号'] and
                  catalog_eligible(p)]
        assert len({p.get('manufacturer') for p in selected if p.get('manufacturer')})<=1
        row['位号']=[p['ref'] for p in selected]
    result.update(设计源SHA256=hashlib.sha256((BASE/'设计数据.py').read_bytes()).hexdigest(),
                  电气位号数=len(parts),
                  精确匹配位号数=sum(len(r['位号']) for r in rows.values() if r['匹配']),
                  离线重绑定='仅对允许目录绑定的相同完整型号复用既有原始库与查询时间；候选封装查询不构成电路或制造放行，未重新查询库存/价格')
    path.write_text(json.dumps(result,ensure_ascii=False,indent=2),encoding='utf-8')
    with (LIB/'嘉立创元件匹配.csv').open('w',encoding='utf-8-sig',newline='') as f:
        w=csv.writer(f);w.writerow(['位号','原型号','状态','立创编号','目录型号','厂家','目录封装','库数据状态','编号集合一致','核验边界'])
        for row in rows.values():
            item=row.get('选定匹配') or {};cad=row.get('库数据',{})
            w.writerow([','.join(row['位号']),row['原型号'],row['状态'],item.get('立创编号',''),item.get('型号',''),item.get('厂家',''),item.get('目录封装',''),cad.get('结果','未获取'),cad.get('引脚编号一致',False),'原查询库复用；新增型号须在线查询'])
    print('已按相同型号重绑缓存库：',len(parts),'位号')

if __name__ == '__main__':
    if hasattr(sys.stdout, 'reconfigure'): sys.stdout.reconfigure(encoding='utf-8')
    if '--离线重绑定' in sys.argv: refresh_cached()
    else: main()
