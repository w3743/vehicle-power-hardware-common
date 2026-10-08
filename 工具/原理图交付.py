"""构建嘉立创文件夹工程，并通过本机客户端核验实际加载的全部连接。

python 硬件/公共/工具/原理图交付.py --构建 硬件/FOC驱动与储能/导出/电机驱动原理图.epro2
python 硬件/公共/工具/原理图交付.py --检查
python 硬件/公共/工具/原理图交付.py --检查原生工程
中间网表和客户端输出仅存本机缓存；工作目录只保留一个核验报告。
"""
from pathlib import Path
from html.parser import HTMLParser
from contextlib import closing
import argparse, collections, hashlib, html, json, re, runpy, sqlite3, subprocess, tempfile, time, zipfile
import base64, shutil, copy, math

BASE = Path(__file__).resolve().parents[2]/'FOC驱动与储能'
EXPORT=BASE/'导出'
REPORT=BASE/'核验'
CACHE = Path.home() / '.cache/电机驱动设计归档/原理图交付'
EXCHANGE = Path.home() / '.cache/电机驱动设计归档/原理图转换/交付转换中间.epro2'
NAME = '电机驱动原理图'
PROJECT = BASE / '原生工程'
# Detailed ISCH_DrcError records are documented only since EDA 4.2.
# 4.1.60 must not treat its old count-only response as classified violations.
ERC_CODE = '''const passed=await eda.sch_Drc.check(true,false,false);
if(typeof passed!=="boolean")throw new Error("官方ERC布尔返回类型异常");
return {passed,summary:passed?[]:[{type:"checkFailed",count:1,
countMeaning:"一次整体ERC检查未通过；不是错误数量"}],messages:[],observed:[],
detailSource:"4.1.60 documented boolean overload; per-rule errors/counts unavailable; detailed overload since EDA 4.2"};'''

# 特殊符号必须落在导线顶点；只落在线段内部会在重开时失去符号关联。
STANDARD_NODE_CODE = r'''const ports=[...(await eda.sch_PrimitiveComponent.getAll("netport")),...(await eda.sch_PrimitiveComponent.getAll("netflag"))];
const anchors=[];
for(const p of ports){const pins=await eda.sch_PrimitiveComponent.getAllPinsByPrimitiveId(p.getState_PrimitiveId());
 for(const pin of pins)anchors.push({x:Math.round(pin.x/5)*5,y:Math.round(pin.y/5)*5,net:p.getState_Net()});}
const changed=[];
for(const w of await eda.sch_PrimitiveWire.getAll()){
 const net=w.getState_Net(),id=w.getState_PrimitiveId();
 const line=w.getState_Line().map(v=>{const p=Math.round(v/5)*5;if(Math.abs(p-v)>1e-5)throw new Error("导线离网格:"+id);return p;});
 if(!Array.isArray(line)||line.length%4)throw new Error("导线线段结构变化");
 const segments=[];let split=false;
 for(let i=0;i<line.length;i+=4){const [x1,y1,x2,y2]=line.slice(i,i+4);
  if(x1!==x2&&y1!==y2)throw new Error("存在非正交导线:"+JSON.stringify({id,net,line}));
  const points=[{x:x1,y:y1},{x:x2,y:y2}];
  for(const p of anchors)if(p.net===net&&((x1===x2&&p.x===x1&&p.y>Math.min(y1,y2)&&p.y<Math.max(y1,y2))||(y1===y2&&p.y===y1&&p.x>Math.min(x1,x2)&&p.x<Math.max(x1,x2)))){
   if(!points.some(q=>q.x===p.x&&q.y===p.y))points.push(p);}
  points.sort((a,b)=>x1===x2?(a.y-b.y)*Math.sign(y2-y1):(a.x-b.x)*Math.sign(x2-x1));
  split ||= points.length>2;
  for(let j=1;j<points.length;j++)segments.push([points[j-1].x,points[j-1].y,points[j].x,points[j].y]);
 }
 if(split){await eda.sch_PrimitiveWire.modify(id,{line:segments,net,color:w.getState_Color(),lineWidth:w.getState_LineWidth(),lineType:w.getState_LineType()});changed.push(id);}
 const attr=(await eda.sch_PrimitiveAttribute.getAll(id)).find(a=>a.getState_Key()==="Name");
 const attached=anchors.some(p=>p.net===net&&segments.some(([x1,y1,x2,y2])=>(x1===x2&&p.x===x1&&p.y>=Math.min(y1,y2)&&p.y<=Math.max(y1,y2))||(y1===y2&&p.y===y1&&p.x>=Math.min(x1,x2)&&p.x<=Math.max(x1,x2))));
 if(attr&&attached&&(attr.getState_ValueVisible()||attr.getState_KeyVisible()))await eda.sch_PrimitiveAttribute.modify(attr.getState_PrimitiveId(),{valueVisible:false,keyVisible:false});
}
await eda.sch_Document.save();return {splitWires:changed.length,symbols:ports.length};'''


def normalize_standard_nodes(invoke, checkpoint=None):
    """Same node/attribute checks in bounded API batches for large one-page boards."""
    ports=invoke('return [...(await eda.sch_PrimitiveComponent.getAll("netport")),...(await eda.sch_PrimitiveComponent.getAll("netflag"))].map(p=>({id:p.getState_PrimitiveId(),net:p.getState_Net()}));')
    anchors=[]
    for start in range(0,len(ports),64):
        anchors.extend(invoke('const ports='+json.dumps(ports[start:start+64])+';const out=[];for(const p of ports){const pins=await eda.sch_PrimitiveComponent.getAllPinsByPrimitiveId(p.id);if(!pins)throw new Error("缺少实际符号锚点:"+p.id);for(const pin of pins)out.push({x:Math.round(pin.x/5)*5,y:Math.round(pin.y/5)*5,net:p.net});}return out;'))
    wires=invoke('return (await eda.sch_PrimitiveWire.getAll()).map(w=>({id:w.getState_PrimitiveId(),net:w.getState_Net()}));')
    assert len({w['id'] for w in wires})==len(wires)
    body=STANDARD_NODE_CODE[STANDARD_NODE_CODE.index('const changed=[];'):]
    body=body.replace('for(const w of await eda.sch_PrimitiveWire.getAll()){',
        'const wires=await eda.sch_PrimitiveWire.get(ids);if(wires.length!==ids.length)throw new Error("批量导线缺失");for(const w of wires){')
    body=body.replace('await eda.sch_Document.save();return {splitWires:changed.length,symbols:ports.length};',
        'return {splitWires:changed.length,wires:wires.length};')
    changed=0;seen=0
    for start in range(0,len(wires),64):
        batch=wires[start:start+64];nets={w['net'] for w in batch}
        payload=CACHE/'当前节点批次.json'
        payload.write_text(json.dumps({'ids':[w['id'] for w in batch],
            'anchors':[p for p in anchors if p['net'] in nets]},ensure_ascii=False),encoding='utf8')
        code='const {ids,anchors}=JSON.parse(await (await eda.sys_FileSystem.readFileFromFileSystem('+json.dumps(payload.as_posix())+')).text());'+body
        result=invoke(code);changed+=result['splitWires'];seen+=result['wires']
        if start%256==0:print('官方单页节点分批',seen,'/',len(wires),flush=True)
        if checkpoint and seen%128==0 and seen<len(wires):
            assert invoke('return await eda.sch_Document.save();') is True
            checkpoint()
    assert seen==len(wires)
    assert invoke('return await eda.sch_Document.save();') is True
    return {'splitWires':changed,'symbols':len(ports),'wires':seen,'batchSize':64}


class SpanParser(HTMLParser):
    def __init__(self):
        super().__init__(); self.attrs = []; self.text = []
    def handle_starttag(self, tag, attrs):
        if tag == 'span': self.attrs.append(dict(attrs))
    def handle_data(self, data):
        self.text.append(data)


def erc_details(messages, index):
    result = []
    for message in messages:
        parser = SpanParser(); parser.feed(message['msg'])
        desc = ''.join(parser.text)
        params = next(a for a in parser.attrs if a.get('class') == 'i18n')
        refs = SpanParser(); refs.feed(html.unescape(params.get('i18n-params-objectid', '')))
        objects = []
        # 名称文字与链接逐个解析，避免从格式化HTML猜位号。
        for link in re.findall(r'<span\b[^>]*>.*?</span>', html.unescape(params.get('i18n-params-objectid', '')), flags=re.S):
            item = SpanParser(); item.feed(link); a = item.attrs[0]
            page = a.get('data-log-find-sheet', '')
            objects.append({'对象': ''.join(item.text), '页面': index['profile']['sheets'].get(page, {}).get('title', page),
                            '页UUID': page, '图元ID': a.get('data-log-find-id', ''), '图元类型': a.get('data-log-find-type', '')})
        rules = {'Component {objectID} lacks of property "Footprint".': '缺少封装',
                 'Net object is not aligned to the schematic grid. {ObjectID}': '电气对象离网格',
                 'The wire {objectID} is a single network connected to only one component pin.': '单引脚网络'}
        result.append({'等级': message['type'], '规则': rules.get(desc, desc), '对象文本': ''.join(refs.text), '对象': objects})
    return result


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def record_json(value):
    # 竖线是专业版记录分隔符，库source及自定义正文中的竖线必须JSON转义。
    return json.dumps(value,ensure_ascii=False,separators=(',',':')).replace('|',r'\u007C')


def cross_schematic_boundary(detail, index, files, expected):
    """仅解释真实跨SCH端子形成的单引脚网络；不豁免孤立或错接网络。"""
    if detail['规则']!='单引脚网络' or len(detail['对象'])!=1:return None
    obj=detail['对象'][0];page_uuid=obj['页UUID'];page_info=index['profile']['sheets'].get(page_uuid)
    if not page_info:return None
    document=None;ref_sch={}
    for path in files:
        rows=[];kind=None;uid=None
        for _,(a,b) in records(path.read_text(encoding='utf-8')):
            if a['type']=='DOCHEAD':kind=b['docType'];uid=b['uuid']
            if kind=='SCH_PAGE':rows.append((a,b))
        if not rows:continue
        info=index['profile']['sheets'].get(uid)
        if not info:continue
        attrs={}
        for a,b in rows:
            if a['type']=='ATTR':attrs.setdefault(b['parentId'],{})[b['key']]=b['value']
        for a,b in rows:
            if a['type']=='COMPONENT' and 'Designator' in attrs.get(a['id'],{}):
                ref_sch[attrs[a['id']]['Designator']]=info['schematic_uuid']
        if uid==page_uuid:document=(rows,attrs)
    if not document:return None
    rows,attrs=document;ident=obj['图元ID'];net=attrs.get(ident,{}).get('NET')
    if not net:
        row=next(((a,b) for a,b in rows if a.get('id')==ident),None)
        if row and row[0]['type']=='LINE':net=attrs.get(row[1].get('lineGroup'),{}).get('NET')
        elif row and row[0]['type']=='ATTR' and row[1]['key']=='NET':net=row[1]['value']
    if not net:
        # 无导线文字时，按本组真实线段与原生符号锚点确定该边界网络。
        group=ident
        row=next(((a,b) for a,b in rows if a.get('id')==ident),None)
        if row and row[0]['type']=='LINE':group=row[1].get('lineGroup')
        elif row and row[0]['type']=='ATTR':group=row[1].get('parentId')
        lines=[b for a,b in rows if a['type']=='LINE' and b.get('lineGroup')==group]
        def on_line(x,y,line):
            return (line['startX']==line['endX']==x and min(line['startY'],line['endY'])<=y<=max(line['startY'],line['endY'])) or (line['startY']==line['endY']==y and min(line['startX'],line['endX'])<=x<=max(line['startX'],line['endX']))
        names=set()
        for a,b in rows:
            if a['type']!='COMPONENT' or not any(on_line(b['x'],b['y'],l) for l in lines):continue
            props=attrs.get(a['id'],{})
            if 'Global Net Name' in props:names.add(props['Global Net Name'])
            elif 'Name' in props and 'Designator' not in props:names.add(props['Name'])
        if len(names)==1:net=names.pop()
    if not net:return None
    here=page_info['schematic_uuid'];local=[];remote=[]
    for (ref,pin),wanted in sorted(expected.items()):
        if wanted!=net or ref not in ref_sch:continue
        sch=ref_sch[ref];item={'原理图':index['profile']['schematics'][sch]['name'],'端子':ref+'.'+pin}
        (local if sch==here else remote).append(item)
    if not local or not remote:return None
    return {'网络':net,'本图端子':local,'其他原理图端子':remote,'对象图元回读':True,
            '说明':'该实体板/系统接线SCH仅呈现跨边界的一端；其他SCH存在设计源确认的同名端子，未在PCB内直接短接不同板'}


def records(text):
    # splitlines() 还会切开 JSON 字符串内的 U+2028 等字符，必须仅按 LF 分行。
    for line in text.split('\n'):
        line=line.strip()
        if line:
            # 空body墓碑可能以“头||”结束，须先取分隔符，再处理记录结束符。
            # 先removesuffix会误删分隔符的一半，导致有效客户端PCB无法读取。
            head,body=line.split('||', 1)
            body=body.removesuffix('|')
            # 客户端保存可能带删除图元的墓碑记录，不把它当作现存图元。
            if not body:continue
            yield line.removesuffix('|') + '|', (json.loads(head),json.loads(body))


def deduplicate_wire_lines(rows):
    """去掉同一线组内完全重合的线段，避免客户端自动画出假交点。"""
    seen=set();removed=set();result=[];kind=None
    for a,b in rows:
        if a['type']=='DOCHEAD':kind=b['docType'];seen.clear()
        if kind=='SCH_PAGE' and a['type']=='LINE' and b.get('lineGroup'):
            endpoints=tuple(sorted(((b['startX'],b['startY']),(b['endX'],b['endY']))))
            key=(b['lineGroup'],endpoints,b.get('strokeColor'),b.get('strokeWidth'),b.get('strokeStyle'))
            if key in seen:
                removed.add(a['id']);continue
            seen.add(key)
        result.append((a,b))
    assert not any(a['type']=='ATTR' and b.get('parentId') in removed for a,b in rows), '重复线段附有独立属性，需单独审查'
    return result,len(removed)


def wire_geometry(files, expected, nc):
    """逐页核验真实导线、标签锚点、引脚和NC；网络范围由各板SCH划分。"""
    docs={};current=None
    for path in files:
        for _,(a,b) in records(path.read_text(encoding='utf-8')):
            if a['type']=='DOCHEAD':
                current={'kind':b['docType'],'rows':[]};docs[b['uuid']]=current
            current['rows'].append((a,b))
    def attributes(rows):
        result={}
        for a,b in rows:
            if a['type']=='ATTR':result.setdefault(b['parentId'],{})[b['key']]=b['value']
        return result
    def grid(x,y):
        assert abs(x/5-round(x/5))<1e-5 and abs(y/5-round(y/5))<1e-5
        return round(x/5),round(y/5)
    checker=runpy.run_path(str(BASE/'工具/分板原理图.py'))['board_geometry_check']
    def netport(props):
        device=docs.get(props.get('Device'),{}).get('rows',[])
        meta=next((b for a,b in device if a['type']=='META'),{})
        return meta.get('title','').startswith('Netport-')
    seen=set();seen_nc=set();results=[]
    for document in docs.values():
        if document['kind']!='SCH_PAGE':continue
        page=document['rows'];attrs=attributes(page);wires={a['id'] for a,b in page if a['type']=='WIRE'}
        _,duplicates=deduplicate_wire_lines([({'type':'DOCHEAD'},{'docType':'SCH_PAGE'}),*page])
        assert duplicates==0, '重复导线会使客户端自动产生非分叉交点'
        visible=[b for a,b in page if a['type']=='ATTR' and b['key']=='NET' and b.get('valueVisible')]
        segments=[(grid(b['startX'],b['startY']),grid(b['endX'],b['endY']),attrs[b['lineGroup']]['NET'])
                  for a,b in page if a['type']=='LINE' and b.get('lineGroup') in wires]
        labels=[]
        for label in visible:
            # 网络文字位置与电气锚点不同；现代格式的标签挂在WIRE上。
            parent=label['parentId']
            assert parent in wires, ('未识别的网络标签宿主',parent)
            lines=[b for a,b in page if a['type']=='LINE' and b.get('lineGroup')==parent]
            assert lines, ('网络标签缺少真实导线',label['value'])
            labels.append((grid(lines[0]['startX'],lines[0]['startY']),label['value']))
        pins={};blank={}
        for a,b in page:
            if a['type']!='COMPONENT':continue
            props=attrs[a['id']]
            if 'Global Net Name' in props:
                # 官方文件夹导出及页面保存后，符号、引脚、导线处于同一坐标系。
                name=next(v for h,v in page if h['type']=='ATTR' and v.get('parentId')==a['id'] and v.get('key')=='Name')
                assert name.get('fontSize') is not None and 0<float(name['fontSize'])<=15, ('标准电源标签字号异常',props['Global Net Name'],name.get('fontSize'))
                labels.append((grid(b['x'],b['y']),props['Global Net Name']))
            if netport(props):
                assert props.get('Name'), ('标准网络端口没有名称',a['id'])
                labels.append((grid(b['x'],b['y']),props['Name']))
            if 'Designator' not in props:continue  # 网络标识符不属于设计器件。
            ref=props['Designator'];symbol=docs[props['Symbol']]['rows'];pa=attributes(symbol)
            angle=math.radians(b.get('rotation',0));c,s=math.cos(angle),math.sin(angle)
            for sa,sb in symbol:
                if sa['type']!='PIN' or sb['partId']!=b['partId']:continue
                key=(ref,str(pa[sa['id']]['Pin Number']))
                x,y=sb['x'],sb['y']
                if b.get('isMirror'):x=-x
                xy=grid(b['x']+x*c-y*s,b['y']+x*s+y*c)
                assert key not in seen and key not in seen_nc, ('跨页重复引脚',key)
                if key in expected:pins[key]=(xy,expected[key]);seen.add(key)
                else:assert key in nc,key;blank[key]=xy;seen_nc.add(key)
        stats,_=checker(segments,pins,blank,labels=labels)
        meta=next(b for a,b in page if a['type']=='META')
        results.append({'页面':meta['title'],**stats,'可见网络标签':len(visible),
                        '精确重复导线记录':duplicates,
                        '标准电源标签字号核验':True,
                        '标准网络端口':sum(a['type']=='COMPONENT' and netport(attrs.get(a['id'],{})) for a,b in page),
                        '内置电源地符号':sum(a['type']=='COMPONENT' and 'Global Net Name' in attrs.get(a['id'],{}) for a,b in page)})
    assert seen==set(expected) and seen_nc==nc, '逐页几何核验未覆盖全部设计引脚'
    return {'逐页':results,'页数':len(results),'连接引脚':len(seen),'NC引脚':len(seen_nc),
            '可见网络标签':sum(p['可见网络标签'] for p in results),'客户端保存文件几何核验':True}


def build(source, target=None):
    """将转换源按实体板重组；保持已有PCB文件、UUID和几何原样。"""
    target = Path(target or PROJECT).resolve();source=Path(source).resolve()
    previous_path=target/(NAME+'.eprj3')
    previous=json.loads(previous_path.read_text(encoding='utf-8')) if previous_path.exists() else None
    with zipfile.ZipFile(source) as z:
        assert z.testzip() is None
        entries={n:z.read(n) for n in z.namelist()}
    epru=next(n for n in entries if n.endswith('.epru'))
    docs=[]
    for _,(a,b) in records(entries[epru].decode('utf-8')):
        if a['type']=='DOCHEAD':docs.append({'head':b,'rows':[]})
        docs[-1]['rows'].append((a,b))
        if a['type']=='META':docs[-1]['meta']=b
    # 转换器会按同型号复用DEVICE；待设计器件不可继承另一块板的真实封装。
    binding_doc=json.loads((BASE.parent/'公共/库/封装绑定.json').read_text(encoding='utf-8'))
    assert binding_doc['设计源SHA256']==sha(BASE/'设计数据.py')
    bindings={b['位号']:b for b in binding_doc['位号绑定']}
    devices={d['head']['uuid']:d for d in docs if d['head']['docType']=='DEVICE'}
    no_footprint={}
    for page in [d for d in docs if d['head']['docType']=='SCH_PAGE']:
        attrs={}
        for a,b in page['rows']:
            if a['type']=='ATTR':attrs.setdefault(b['parentId'],{})[b['key']]=b
        for props in attrs.values():
            if 'Designator' not in props or 'Device' not in props:continue
            ref=props['Designator']['value'];binding=bindings[ref]
            if binding['封装']:continue
            old_id=props['Device']['value'];device=devices[old_id]
            if not device['meta']['attributes'].get('Footprint'):continue
            if old_id not in no_footprint:
                clone=copy.deepcopy(device)
                clone['head']['uuid']=hashlib.sha256((old_id+'|NO_FOOTPRINT').encode()).hexdigest()[:16]
                clone['meta']['attributes']['Footprint']=''
                no_footprint[old_id]=clone;docs.append(clone)
            props['Device']['value']=no_footprint[old_id]['head']['uuid']
            if 'Footprint' in props:props['Footprint']['value']=''
    audit_path=REPORT/'器件必要性审查.json'
    if audit_path.exists():
        audit=json.loads(audit_path.read_text(encoding='utf8'))
        assert audit['设计源SHA256']==sha(BASE/'设计数据.py'), '器件审查已过期，停止复用'
        findings={r['位号']:r for r in audit['逐器件']}
        covered=set()
        for page in [d for d in docs if d['head']['docType']=='SCH_PAGE']:
            props={}
            for a,b in page['rows']:
                if a['type']=='ATTR':props.setdefault(b['parentId'],{})[b['key']]=(a,b)
            ticket=max(a.get('ticket',0) for a,b in page['rows'])
            for ident,attrs in props.items():
                if 'Designator' not in attrs:continue
                ref=attrs['Designator'][1]['value'];r=findings[ref];covered.add(ref)
                for ordinal,(key,value) in enumerate((('审查结论',r['处理']),('器件作用',r['作用']),
                                                      ('独立必要性',r['独立必要性']),('删并前提',r['删并条件及未知']))):
                    if key in attrs:
                        attrs[key][1]['value']=value
                    else:
                        ticket+=1
                        a,b=copy.deepcopy(attrs['Manufacturer Part'])
                        a.update(id=ident+'_audit'+str(ordinal),ticket=ticket)
                        b.update(key=key,value=value,keyVisible=False,valueVisible=False,parentId=ident)
                        page['rows'].append((a,b))
        assert covered==findings.keys(), '器件审查未完整写入原生属性'
    # 库UUID根据实际内容生成，避免转换器复用编号命中旧客户端库缓存。
    aliases={}
    def mapped(value):
        if isinstance(value,str):return aliases.get(value,value)
        if isinstance(value,list):return [mapped(v) for v in value]
        if isinstance(value,dict):return {aliases.get(k,k):mapped(v) for k,v in value.items()}
        return value
    for classes in [('BLOB','FONT','FOOTPRINT'),('SYMBOL',),('DEVICE',)]:
        for doc in docs:
            head=doc['head']
            if head['docType'] not in classes:continue
            data=[]
            for a,b in doc['rows']:
                value=mapped(b)
                if a['type']=='DOCHEAD':value={k:v for k,v in value.items() if k!='uuid'}
                data.append((a['type'],a.get('id',''),value))
            aliases[head['uuid']]=hashlib.sha256(json.dumps(data,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()[:16]
    for doc in docs:
        doc['rows']=[(mapped(a),mapped(b)) for a,b in doc['rows']]
        doc['head']=doc['rows'][0][1]
        if 'meta' in doc:doc['meta']=next(b for a,b in doc['rows'] if a['type']=='META')
    groups=('驱动主板','辅助电源板','中央稳压模块','系统接线')
    pages=[d for d in docs if d['head']['docType']=='SCH_PAGE']
    assert pages, '没有原理图页面'
    by_group={name:[] for name in groups}
    for page in pages:
        title=page['meta']['title']
        group=next((name for name in groups if title==name or title.startswith(name+'-')),None)
        assert group, ('页面名称必须包含实体板/系统接线前缀',title)
        by_group[group].append(page)
    assert all(by_group.values()), '缺少实体板或系统接线原理图'
    old_profile=(previous or {}).get('profile',{})
    old_boards={v.get('title',v.get('name')):k for k,v in old_profile.get('boards',{}).items()}
    old_sch={v['name']:k for k,v in old_profile.get('schematics',{}).items()}
    def stable(kind,name):return hashlib.sha256((NAME+'|'+kind+'|'+name).encode()).hexdigest()[:16]
    prototype_sch=next(d for d in docs if d['head']['docType']=='SCH')
    prototype_board=next(d for d in docs if d['head']['docType']=='BOARD')
    rebuilt=[];profile={k:{} for k in ('boards','schematics','sheets','pcbs','panels','blockSymbols','simSchematics','simulations')}
    sequence=0
    for order,name in enumerate(groups,1):
        sch_uuid=old_sch.get(name,stable('SCH',name))
        board_uuid=old_boards.get(name,stable('BOARD',name)) if name!='系统接线' else ''
        if board_uuid:
            board=copy.deepcopy(prototype_board)
            board['head']['uuid']=board_uuid
            board['meta'].update(title=name,zIndex=order)
            rebuilt.append(board)
            profile['boards'][board_uuid]={'uuid':board_uuid,**board['meta'],'name':name}
        sch=copy.deepcopy(prototype_sch);sch['head']['uuid']=sch_uuid
        sch['meta'].update(title=name,board=board_uuid,zIndex=order)
        rebuilt.append(sch)
        profile['schematics'][sch_uuid]={'uuid':sch_uuid,'name':name,'board':board_uuid,'source':sch['meta'].get('source','')}
        for page in sorted(by_group[name],key=lambda p:p['meta']['title']):
            sequence+=1;page['meta'].update(schematic=sch_uuid,zIndex=sequence)
            # 每页UUID随内容变化，避免客户端同路径旧页缓存。
            data=[(a,b) for a,b in page['rows'] if a['type']!='DOCHEAD']
            page['head']['uuid']=hashlib.sha256(json.dumps(data,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()[:16]
            uid=page['head']['uuid'];meta=page['meta']
            profile['sheets'][uid]={'uuid':uid,'title':meta['title'],'schematic_uuid':sch_uuid,'zIndex':sequence,'source':meta.get('source','')}
    docs=[d for d in docs if d['head']['docType'] not in ('BOARD','SCH','SCH_PAGE','PCB')]+rebuilt+pages
    # PCB完全保留，不在重排原理图时重新生成、移动或删除器件。
    preserved_hashes={}
    for uid,pcb in old_profile.get('pcbs',{}).items():
        old_board=old_profile['boards'][pcb['board']]
        name=old_board.get('title',old_board.get('name'))
        assert name in groups[:-1], ('未知PCB板，停止重建',name)
        assert pcb['board']==old_boards[name]
        profile['pcbs'][uid]=copy.deepcopy(pcb)
    if target.exists():
        preserved_hashes={p.relative_to(target):sha(p) for p in (target/'pcb').rglob('*') if p.is_file()}
    def lines(doc):
        return [record_json(a)+'||'+record_json(b)+'|' for a,b in doc['rows']]
    library={d['head']['uuid']:d for d in docs if d['head']['docType'] in ('DEVICE','SYMBOL','FOOTPRINT','BLOB','FONT')}
    outputs={}
    for doc in rebuilt:
        if doc['head']['docType']=='SCH':
            title=doc['meta']['title'];outputs[Path('sch')/title/(title+'.ecfg')]='\n'.join(lines(doc))+'\n'
    for page in pages:
        needed={b['value'] for a,b in page['rows'] if a['type']=='ATTR' and b['key'] in ('Device','Symbol','Footprint') and b['value']}
        for uid in list(needed):
            if uid in library and library[uid]['head']['docType']=='DEVICE':
                needed.update(v for k,v in library[uid]['meta']['attributes'].items() if k in ('Symbol','Footprint') and v)
        assert needed<=library.keys(),needed-library.keys()
        name=profile['schematics'][page['meta']['schematic']]['name'];title=page['meta']['title']
        assert all('/' not in x and '\\' not in x and x not in ('.','..') for x in (name,title))
        blocks=[lib for lib in library.values() if lib['head']['uuid'] in needed]+[page]
        outputs[Path('sch')/name/(title+'.esch2')]='\n'.join(line for block in blocks for line in lines(block))+'\n'
    config=next(d['meta'] for d in docs if d['head']['docType']=='CONFIG')
    first=min(profile['sheets'].values(),key=lambda p:p['zIndex'])['uuid']
    # epru也供原生导入使用，必须与新页UUID同步，不能只修文件夹工程索引。
    config['defaultSheet']=first
    index={'name':NAME,'content':'','archive':False,'cbb_project':0,'ticket':1,'g_ticket':1,
           'boards':[],'pcb_count':len(profile['pcbs']),'format':'folder','profile':profile,'default_sheet':first,
           'config':{**config,'defaultSheet':first,'settings':{}}}
    outputs[Path(NAME+'.eprj3')]=json.dumps(index,ensure_ascii=False,indent=2)+'\n'
    if target.exists():
        old={p.relative_to(target) for p in target.rglob('*') if p.is_file()}
        known=set()
        for page in old_profile.get('sheets',{}).values():
            name=old_profile['schematics'][page['schematic_uuid']]['name']
            known.add(Path('sch')/name/(page['title']+'.esch2'))
        for sch in old_profile.get('schematics',{}).values():known.add(Path('sch')/sch['name']/(sch['name']+'.ecfg'))
        preserved={p for p in old if p in preserved_hashes or p.suffix=='.evar'}
        obsolete=old-preserved-outputs.keys()
        assert obsolete<=known, ('工程含未知文件，停止覆盖',sorted(map(str,obsolete-known)))
        if obsolete:
            CACHE.mkdir(parents=True,exist_ok=True)
            backup=CACHE/('图页调整前-'+sha(previous_path)[:12]+'.zip')
            with zipfile.ZipFile(backup,'w',zipfile.ZIP_DEFLATED) as z:
                for p in target.rglob('*'):
                    if p.is_file():z.write(p,p.relative_to(target))
            with zipfile.ZipFile(backup) as z:assert z.testzip() is None
            for name in obsolete:
                p=(target/name).resolve();assert p.is_relative_to(target) and p.suffix in ('.esch2','.ecfg')
                p.unlink()
            for folder in sorted((target/'sch').rglob('*'),key=lambda p:len(p.parts),reverse=True):
                if folder.is_dir() and not any(folder.iterdir()):folder.rmdir()
    for name,text in outputs.items():
        p=target/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text,encoding='utf-8',newline='\n')
    assert all(sha(target/name)==digest for name,digest in preserved_hashes.items()), 'PCB内容发生变化'
    entries[epru]=('\n'.join(line for doc in docs for line in lines(doc))+'\n').encode('utf-8')
    config_defaults=[b.get('defaultSheet') for doc in docs if doc['head']['docType']=='CONFIG'
                     for a,b in doc['rows'] if a['type']=='META']
    assert config_defaults==[first] and first in profile['sheets'], '交换工程默认页引用无效'
    # 按相同分板结构更新交换文件；后续原生工程从此文件导入。
    with zipfile.ZipFile(source,'w',zipfile.ZIP_DEFLATED) as z:
        for name,data in entries.items():z.writestr(name,data)
    return target/(NAME+'.eprj3')


def cli(exe, *args):
    # Windows首次启动的后台owner会继承stdout管道，communicate可能永久等待EOF。
    # 用缓存文件收集输出，只等待CLI进程退出；不等待owner关闭继承的句柄。
    CACHE.mkdir(parents=True, exist_ok=True)
    paths = []
    try:
        with tempfile.NamedTemporaryFile(mode='w+', encoding='utf-8', dir=CACHE, prefix='CLI-', delete=False) as out, \
             tempfile.NamedTemporaryFile(mode='w+', encoding='utf-8', dir=CACHE, prefix='CLI-', delete=False) as err:
            paths = [Path(out.name), Path(err.name)]
            # 客户端/库检索可能生成临时数据库；工作目录固定到缓存，避免污染工程。
            run = subprocess.run([str(exe), *args], stdout=out, stderr=err, timeout=120, cwd=CACHE)
            out.seek(0); stdout = out.read()
            err.seek(0); stderr = err.read()
        assert run.returncode == 0, {'CLI_exit_code':run.returncode,'action':args[0] if args else None,'stdout':stdout[:6000],'stderr':stderr[:6000]}
        result = json.loads(stdout)
        assert result['ok'], result
        return result
    finally:
        for p in paths:
            try: p.unlink()
            except PermissionError: pass  # 首次owner仍持有缓存句柄；不影响工程或后续CLI。


def wait_for_project(invoke, require_documents=True, attempts=30):
    """新路径重开先确认实际项目已挂载，不以固定延时推定就绪。"""
    ready=None
    for _ in range(attempts):
        # 文件夹工程挂载初期有currentProject对象，但projectId尚未赋值；
        # 此时调用项目管理RPC可能悬挂，先读取同步状态再请求真实工程树。
        state=invoke('return {id:globalThis.gVars?.currentProject?.projectId};')
        if not state.get('id'):
            ready=state;time.sleep(.5);continue
        ready=invoke('return {info:await eda.dmt_Project.getCurrentProjectInfo(),id:globalThis.gVars.currentProject?.projectId};')
        info=ready.get('info')
        if info and ready.get('id')==info['uuid'] and (info.get('data') or not require_documents):return info
        time.sleep(.5)
    raise AssertionError(('客户端实际工程未就绪',ready))


def open_document(invoke, page_uuid):
    tab=invoke('return await eda.dmt_EditorControl.openDocument('+json.dumps(page_uuid)+');')
    for _ in range(10):
        if tab:break
        time.sleep(.5)
        tab=invoke('return await eda.dmt_EditorControl.openDocument('+json.dumps(page_uuid)+');')
    assert tab, ('客户端未打开页面',page_uuid)
    assert invoke('return await eda.dmt_EditorControl.activateDocument('+json.dumps(tab)+');') is True
    return tab


def invoke_on_page(invoke, page_uuid, parking_uuid, code):
    """One serial CLI call per page, with explicit focus and loaded-part checks."""
    return invoke('''const page='''+json.dumps(page_uuid)+''',parking='''+json.dumps(parking_uuid)+''';
async function focus(uuid,loaded){
 const tab=await eda.dmt_EditorControl.openDocument(uuid);
 if(!tab||await eda.dmt_EditorControl.activateDocument(tab)!==true)throw new Error("图页打开/激活失败:"+uuid);
 for(let i=0;i<20;i++){
  const p=await eda.dmt_Schematic.getCurrentSchematicPageInfo();
  if(p?.uuid===uuid&&(!loaded||(await eda.sch_PrimitiveComponent.getAll("part")).length>0))return tab;
  await new Promise(r=>setTimeout(r,250));
 }
 throw new Error("图页焦点或器件加载未就绪:"+uuid);
}
const tab=await focus(page,true);
const value=await(async()=>{'''+code+'''})();
if(page!==parking){await focus(parking,false);if(await eda.dmt_EditorControl.closeDocument(tab)!==true)throw new Error("图页关闭失败");}
return value;''')


def edit_native_text(invoke, page_uuid, primitive_id, expected_content, content):
    """仅用公开文字创建/删除和文档保存；持久化须独立关闭重开核验。"""
    assert all(isinstance(v,str) and v for v in (page_uuid,primitive_id)), '图页和文字ID须非空'
    assert all(isinstance(v,str) for v in (expected_content,content)), '文字内容必须是字符串'
    assert content, '4.1.60文本API不支持空内容；停止修改'
    open_document(invoke,page_uuid)
    result=invoke('''const version=await eda.sys_Environment.getEditorCurrentVersion();
if(version!=="4.1.60")throw new Error("文本事务兼容仅验证过4.1.60:"+version);
const id='''+json.dumps(primitive_id)+',before='+json.dumps(expected_content)+',content='+json.dumps(content)+''';
const original=await eda.sch_PrimitiveText.get(id);
if(!original||original.getState_Content()!==before)throw new Error("文字对象不存在或内容已变化");
const replacement=await eda.sch_PrimitiveText.create(original.getState_X(),original.getState_Y(),content,
original.getState_Rotation(),original.getState_TextColor(),original.getState_FontName(),original.getState_FontSize(),
original.getState_Bold(),original.getState_Italic(),original.getState_UnderLine(),original.getState_AlignMode());
if(!replacement||replacement.getState_Content()!==content)throw new Error("替换文字创建失败，原件保留");
if(await eda.sch_PrimitiveText.delete(id)!==true)throw new Error("替换文字后旧文字删除失败");
const changed=await eda.sch_PrimitiveText.get(replacement.getState_PrimitiveId());
if(!changed||changed.getState_Content()!==content)throw new Error("文本修改未生效");
const saved=await eda.sch_Document.save();
if(saved!==true)throw new Error("文本保存失败");
return {version,before,content,saved,oldPrimitiveId:id,newPrimitiveId:replacement.getState_PrimitiveId(),interface:"public SCH_PrimitiveText.create/delete + SCH_Document.save",persistenceRequiresReopen:true};''')
    assert result['content']==content and result['saved'] is True, ('文本保存返回不符',result)
    time.sleep(5)
    return result


def netlist_designator_changes(before, components):
    """网表导出可能自动编号；保留UID比对，禁止把变化后的编号当作设计源。"""
    changed=[]
    for component in components.values():
        props=component['props'];uid=props.get('Unique ID')
        if uid in before and props['Designator']!=before[uid]:
            changed.append({'Unique ID':uid,'导出前':before[uid],'导出后':props['Designator']})
    return changed


def read_all_schematics(invoke, parking_title='辅助电源板'):
    """逐页保存，逐SCH读取网表/ERC；不同实体板的同名网只按名称核对。"""
    assert isinstance(parking_title,str) and parking_title, '停车页须是本板已有标题或分组前缀'
    pages=invoke('return await eda.dmt_Schematic.getAllSchematicPagesInfo();')
    assert pages, '客户端未加载原理图页'
    groups={}
    for page in pages:groups.setdefault(page['parentSchematicUuid'],[]).append(page)
    components={};refs=set();messages=[];summary={};group_results=[];rendered=[]
    parking=next((p['uuid'] for p in pages if p['name']==parking_title or p['name'].startswith(parking_title+'-')),None)
    assert parking, '指定停车页未加载；不复用其他板默认页'
    for sch,group in groups.items():
        before={}
        for page in sorted(group,key=lambda p:p['name']):
            open_document(invoke,page['uuid'])
            before.update(invoke('return Object.fromEntries((await eda.sch_PrimitiveComponent.getAll("part")).map(c=>[c.getState_UniqueId(),c.getState_Designator()]));'))
            assert invoke('return await eda.sch_Document.save();') is True
            ids=invoke('const f=await eda.sch_ManufactureData.getSvgFile("view");const d=new DOMParser().parseFromString(await f.text(),"image/svg+xml");return Array.from(d.getElementsByTagName("text")).map(t=>t.id).filter(Boolean);')
            rendered.append({'页UUID':page['uuid'],'可见文字图元ID':ids})
        # 官方制造导出会因ERC致命项拒绝生成File；先保留ERC证据，
        # 不把undefined当接口成功或用空网表绕过真实封装缺项。
        erc=invoke(ERC_CODE)
        raw=invoke(r'const f=await eda.sch_ManufactureData.getNetlistFile("客户端网表","JLCEDA");if(!f||typeof f.text!=="function")return {data:null};return {data:(await f.text()).replace(/[^\x00-\x7f]/g,c=>"\\u"+c.charCodeAt(0).toString(16).padStart(4,"0"))};')
        assert isinstance(raw.get('data'),str) and raw['data'], ('官方制造网表未生成；须先处理ERC或导出阻塞',sch,erc['summary'])
        data=json.loads(raw['data'])
        changed=netlist_designator_changes(before,data['components'])
        assert not changed, ('制造网表导出自动改变位号，停止验收；不自动改写设计源',changed)
        for ident,component in data['components'].items():
            ref=component['props']['Designator']
            assert ref not in refs, ('跨原理图重复位号',ref)
            refs.add(ref);components[sch+'|'+ident]=component
        messages.extend(erc['messages'])
        for row in erc['summary']:summary[row['type']]=summary.get(row['type'],0)+row['count']
        group_results.append({'原理图UUID':sch,'页数':len(group),'器件':len(data['components']),'ERC':erc['summary']})
        open_document(invoke,parking)
        for page in group:
            if page['uuid']!=parking:
                tab=open_document(invoke,page['uuid'])
                open_document(invoke,parking)
                assert invoke('return await eda.dmt_EditorControl.closeDocument('+json.dumps(tab)+');') is True
    return {'data':json.dumps({'components':components},ensure_ascii=True,separators=(',',':')),
            'pages':pages,'saved':True,'erc':[{'type':k,'count':v} for k,v in summary.items()],
            'ercMessages':messages,'schematics':group_results,'rendered':rendered}


def sqlite_copy(source, target):
    target.parent.mkdir(parents=True, exist_ok=True)
    # 不向已有交付数据库直接backup；有客户端占用时可无限等待或留下半成品。
    temp=target.with_name(target.name+'.copy-'+str(time.time_ns()))
    started=time.monotonic()
    def progress(status,remaining,total):
        if time.monotonic()-started>30:raise TimeoutError('数据库持续占用，保留原工程，停止复制')
    try:
        with closing(sqlite3.connect('file:' + source.as_posix() + '?mode=ro', uri=True)) as db:
            with closing(sqlite3.connect(temp)) as out:
                db.backup(out,pages=256,progress=progress,sleep=.1)
                assert out.execute('pragma integrity_check').fetchone()[0]=='ok'
        temp.replace(target)
    finally:
        if temp.exists():temp.unlink()


def _native_import_context(source, expected_refs, parking_title, project_name, cache_dir, template_path, folder_export):
    """只读参数保护；外板显式给位号/停车页/名称，避免隐式读FOC PARTS。"""
    custom=any(v is not None for v in (expected_refs,parking_title,project_name,cache_dir,template_path))
    if custom:
        assert expected_refs is not None and parking_title and project_name, '外板必须给expected_refs、parking_title和project_name'
        assert not isinstance(expected_refs,(str,bytes)), 'expected_refs必须是位号序列，不是字符串'
        refs=list(expected_refs)
        assert refs and all(isinstance(r,str) and r for r in refs) and len(set(refs))==len(refs), '预期位号须非空且无重复'
    else:
        refs=[p['ref'] for p in runpy.run_path(str(BASE/'设计数据.py'))['PARTS']]
    title=project_name or NAME
    assert title and not any(c in title for c in '<>:"/\\|?*') and not title.endswith(('.', ' ')), '工程名称必须是单个合法文件名'
    assert title.upper().split('.')[0] not in {'CON','PRN','AUX','NUL',*(f'COM{i}' for i in range(1,10)),*(f'LPT{i}' for i in range(1,10))}, '工程名称是Windows保留名'
    cache=Path(cache_dir).resolve() if cache_dir is not None else (CACHE/('单板-'+hashlib.sha256((str(source)+'|'+title).encode()).hexdigest()[:12]) if custom else CACHE)
    protected=PROJECT.resolve()
    assert not cache.is_relative_to(protected) and not protected.is_relative_to(cache), '缓存不得覆盖或包含FOC交付工程'
    assert not cache.is_relative_to(BASE.resolve()), '临时缓存不能放入硬件工作目录'
    destination=Path(folder_export).resolve() if folder_export is not None else None
    if destination is not None:
        assert not destination.exists(), '官方另存目标已经存在，停止覆盖'
        assert not destination.is_relative_to(protected) and not protected.is_relative_to(destination), '官方另存不得覆盖或包含FOC交付工程'
        assert not source.is_relative_to(destination), '官方另存目标不得包含输入交换文件'
        if template_path is not None:assert not Path(template_path).resolve().is_relative_to(destination), '另存目标不得包含空模板'
    return {'refs':sorted(refs),'parking':parking_title or '辅助电源板','name':title,
            'cache':cache,'template':Path(template_path).resolve() if template_path is not None else None,
            'destination':destination,'custom':custom}


def _native_default_page(page_titles, source_default, declared, default_page_title):
    """源有非空选择时不覆盖；缺字段/空字符串须本板显式默认页。"""
    if default_page_title is not None:
        assert isinstance(default_page_title,str) and default_page_title in page_titles.values(), '显式默认页不在本板交换工程中'
    if declared and source_default != '':
        title=page_titles.get(source_default)
        assert title, ('交换工程已声明但默认页引用无效',source_default)
        assert default_page_title is None or default_page_title==title, '显式默认页与交换工程声明矛盾'
        return title
    assert default_page_title is not None, '交换工程未声明defaultSheet；须显式给default_page_title'
    return default_page_title


def _native_uid_map(source_rows, expected_refs):
    """仅取本次SCH_PAGE元件属性；不按UID前缀推测位号。"""
    attributes={};kind=None;page=None
    for _,(a,b) in source_rows:
        if a['type']=='DOCHEAD':kind=b['docType'];page=b['uuid']
        elif kind=='SCH_PAGE' and a['type']=='ATTR':
            attributes.setdefault((page,b['parentId']),{})[b['key']]=b['value']
    mapping={};seen=set();expected=set(expected_refs)
    for props in attributes.values():
        ref=props.get('Designator')
        if not ref:continue
        uid=props.get('Unique ID')
        assert isinstance(uid,str) and uid and ref in expected, ('源Unique ID缺失或位号未知',uid,ref)
        assert uid not in mapping and ref not in seen, ('源Unique ID或位号重复/冲突',uid,ref)
        mapping[uid]=ref;seen.add(ref)
    assert seen==expected, '源Unique ID映射未精确覆盖预期位号'
    return mapping


def native_import(exe, source, native_flags=None, folder_export=None, *,
                  expected_refs=None, parking_title=None, project_name=None,
                  cache_dir=None, template_path=None, default_page_title=None,
                  native_pin_types=None):
    """仅在新缓存目录官方导入并导出；不读取上一轮网表、不覆盖交付。"""
    source = Path(source).resolve()
    context=_native_import_context(source,expected_refs,parking_title,project_name,cache_dir,template_path,folder_export)
    expected_refs=context['refs'];cache=context['cache'];folder_export=context['destination']
    assert isinstance(context['parking'],str), '停车页须是本板原理图标题或分组前缀'
    source_hash = sha(source)
    with zipfile.ZipFile(source) as z:
        assert z.testzip() is None
        epru = next(n for n in z.namelist() if n.endswith('.epru'))
        source_text=z.read(epru).decode('utf-8')
        source_rows=list(records(source_text))
        expected_pages = sum(a['type']=='DOCHEAD' and b['docType']=='SCH_PAGE' for _,(a,b) in source_rows)
        expected_titles=set();page_titles={};kind=None;doc_uuid=None;source_default='';default_declared=False
        for _,(a,b) in source_rows:
            if a['type']=='DOCHEAD':kind=b['docType'];doc_uuid=b['uuid']
            elif a['type']=='META' and kind=='SCH_PAGE':expected_titles.add(b['title']);page_titles[doc_uuid]=b['title']
            elif a['type']=='META' and kind=='CONFIG' and 'defaultSheet' in b:
                assert not default_declared or source_default==b['defaultSheet'], '交换工程存在矛盾的defaultSheet声明'
                source_default=b['defaultSheet'];default_declared=True
    assert expected_pages > 0, '交换工程没有原理图页面'
    assert len(expected_titles)==expected_pages, '原理图页面标题重复，无法可靠判定导入完成'
    first_title=_native_default_page(page_titles,source_default,default_declared,default_page_title)
    uid_map=_native_uid_map(source_rows,expected_refs)
    assert any(t==context['parking'] or t.startswith(context['parking']+'-') for t in expected_titles), '指定停车页不在本板交换工程中'
    pin_type_text=None;pin_type_coverage={};pin_type_changed=0
    if native_pin_types:
        pin_type_text,pin_type_coverage,pin_type_changed=normalize_native_pin_types(source_text,native_pin_types)
        assert pin_type_coverage=={model:set(pins) for model,pins in native_pin_types.items()}, '审定引脚类型表未精确覆盖本次源型号'
    cache.mkdir(parents=True, exist_ok=True)
    template = context['template'] or CACHE / '空工程模板.eprj2'
    if not template.exists():
        assert context['template'] is None, '指定空模板不存在；不会替换为FOC模板'
        # 本机先前用官方createProject产生的空模板；复制到缓存后不再依赖原路径。
        template_source = Path.home() / 'Documents/LCEDA-Pro/projects/电机驱动原理图.eprj2'
        assert template_source.exists(), '缺少原生空模板，请提供由本机嘉立创创建的空eprj2工程'
        with closing(sqlite3.connect('file:' + template_source.as_posix() + '?mode=ro', uri=True)) as db:
            assert db.execute('select count(*) from schematics').fetchone()[0] == 0, '模板已被编辑，停止覆盖'
        sqlite_copy(template_source, template)
    with closing(sqlite3.connect('file:' + template.as_posix() + '?mode=ro', uri=True)) as db:
        assert db.execute('select count(*) from schematics').fetchone()[0] == 0, '空模板包含用户原理图，停止导入'
    # 客户端按路径缓存工程信息，每轮在新缓存目录构建，避免旧会话信息污染空模板。
    work = Path(tempfile.mkdtemp(prefix='原生构建-', dir=cache)) / '原生构建.eprj2'
    audit_dir=work.parent if context['custom'] else CACHE
    uid_path=work.parent/'位号恢复映射.json'
    uid_path.write_text(json.dumps(list(uid_map.items()),ensure_ascii=False),encoding='utf8')
    import_source=source
    if pin_type_text is not None:
        import_source=work.parent/'审定引脚类型.epro2'
        with zipfile.ZipFile(source) as original,zipfile.ZipFile(import_source,'w',zipfile.ZIP_DEFLATED) as prepared:
            for member in original.infolist():
                prepared.writestr(member,pin_type_text.encode('utf8') if member.filename==epru else original.read(member.filename))
        (audit_dir/'审定引脚类型.json').write_text(json.dumps({'源SHA256':source_hash,
            '覆盖型号':sorted(pin_type_coverage),'修改字段数':pin_type_changed,
            '说明':'仅调用者明确提交的审定逐针表；未覆盖型号保留原状，不作为电气类型通过'},ensure_ascii=False,indent=2),encoding='utf8')
    sqlite_copy(template, work)
    with closing(sqlite3.connect('file:' + work.as_posix() + '?mode=ro', uri=True)) as db:
        initial_history = db.execute('select count(*),coalesce(sum(length(dataStr)),0) from history_data').fetchone()
    session = cli(exe, 'open', '--path', work.as_posix(), '--headless', 'true')['value']['sessionId']
    def invoke(code):
        return cli(exe, 'invoke', '--session', session, '--ext-uuid', 'eda', '--timeout', '60000', '--code', code)['value']
    try:
        initial=wait_for_project(invoke)
        assert all(d['name'] in ('Board1', 'Panel1') for d in initial['data']), '空模板包含用户文档，停止覆盖'
        path = import_source.as_posix()
        invoke('const f=await eda.sys_FileSystem.readFileFromFileSystem(' + json.dumps(path) + ');await eda.sys_FileManager.importProjectByProjectFile(f,"JLCEDA Pro",undefined,{operation:"Existing Project",existingProjectUuid:globalThis.gVars.currentProject.projectId});return true;')
        pages = None
        for _ in range(30):
            info = invoke('return await eda.dmt_Project.getCurrentProjectInfo();')
            all_pages = invoke('return await eda.dmt_Schematic.getAllSchematicPagesInfo();')
            # 空模板仍有P1默认页；在清理默认文档前，只统计本轮导入页。
            pages=[p for p in all_pages if p['name'] in expected_titles]
            if len(pages) == expected_pages: break
            time.sleep(0.5)
        assert pages and len(pages) == expected_pages, {'客户端导入页面不完整':True,
            '期望':expected_pages,'导入':len(pages or []),'全工程':len(all_pages),
            '缺少页面':sorted(expected_titles-{p['name'] for p in pages or []})}
        # 先激活新页，再清理空模板；删除唯一已打开的默认页可能结束无界面会话。
        first=next(p['uuid'] for p in pages if p['name']==first_title)
        open_document(invoke,first)
        # 空模板的默认Panel可能在首次读取工程树后异步出现。
        late_panels = [d for d in info['data'] if d['itemType'] == 'Panel' and d['name'] == 'Panel1'
                       and not any(v.get('uuid') == d['uuid'] for v in initial['data'])]
        initial['data'].extend(late_panels)
        for d in initial['data']:
            if d['itemType'] == 'Board':
                if d.get('schematic'):
                    assert invoke('return await eda.dmt_Schematic.deleteSchematic(' + json.dumps(d['schematic']['uuid']) + ');') is True
                if d.get('pcb'):
                    assert invoke('return await eda.dmt_Pcb.deletePcb(' + json.dumps(d['pcb']['uuid']) + ');') is True
                # 删除最后的关联文档时客户端可能同步删除空板；仅在它仍存在时删除。
                exists = invoke('return (await eda.dmt_Board.getAllBoardsInfo()).some(b=>b.name===' + json.dumps(d['name']) + ');')
                if exists:
                    assert invoke('return await eda.dmt_Board.deleteBoard(' + json.dumps(d['name']) + ');') is True
            elif d['itemType'] == 'Panel':
                assert invoke('return await eda.dmt_Panel.deletePanel(' + json.dumps(d['uuid']) + ');') is True
        for _ in range(30):
            info = invoke('return await eda.dmt_Project.getCurrentProjectInfo();')
            # 新建空模板的Panel可能迟于导入/首次清理出现；只清理该已知默认项。
            extra=[d for d in info['data'] if d['itemType']=='Panel' and d['name']=='Panel1']
            if extra:
                for d in extra:
                    assert invoke('return await eda.dmt_Panel.deletePanel('+json.dumps(d['uuid'])+');') is True
                time.sleep(.5)
                continue
            actual_pages=invoke('return await eda.dmt_Schematic.getAllSchematicPagesInfo();')
            if len(actual_pages)==expected_pages and {p['name'] for p in actual_pages}==expected_titles and all(d['name'] not in ('Board1','Panel1') for d in info['data']):break
            time.sleep(0.5)
        assert len(actual_pages)==expected_pages and {p['name'] for p in actual_pages}==expected_titles and all(d['name'] not in ('Board1','Panel1') for d in info['data']), {'原生工程残留默认文档': [(d['itemType'],d['name']) for d in info['data']]}
        first=next(p['uuid'] for p in pages if p['name']==first_title)
        tab = invoke('return await eda.dmt_EditorControl.openDocument(' + json.dumps(first) + ');')
        for _ in range(10):
            if tab: break
            time.sleep(0.5); tab = invoke('return await eda.dmt_EditorControl.openDocument(' + json.dumps(first) + ');')
        assert tab
        assert invoke('return await eda.dmt_EditorControl.activateDocument(' + json.dumps(tab) + ');') is True
        time.sleep(1)
        # 官方导入会重编某些含尾数的位号；按保留的Unique ID恢复项目位号，
        # 先临时腾空避免连续编号碰撞，再逐一验证；不通过则不导出。
        restored_refs=[]
        parking=next(p['uuid'] for p in pages if p['name']==context['parking'] or p['name'].startswith(context['parking']+'-'))
        def park_document(uuid):
            if uuid==parking:return
            tab=open_document(invoke,uuid)
            open_document(invoke,parking)
            assert invoke('return await eda.dmt_EditorControl.closeDocument('+json.dumps(tab)+');') is True
        for page in sorted(pages,key=lambda p:p['name']):
            restore=invoke_on_page(invoke,page['uuid'],parking,'const cs=await eda.sch_PrimitiveComponent.getAll("part");\nconst mapping=new Map(' + 'JSON.parse(await (await eda.sys_FileSystem.readFileFromFileSystem('+json.dumps(uid_path.as_posix())+')).text())' + ');const seen=new Set();const fix=[];\nfor(const c of cs){const u=c.getState_UniqueId();if(!mapping.has(u)||seen.has(u))throw new Error("未知或重复Unique ID:"+u);seen.add(u);\nconst want=mapping.get(u);if(c.getState_Designator()!==want)fix.push({c,want});}\nfor(let i=0;i<fix.length;i++)await eda.sch_PrimitiveComponent.modify(fix[i].c,{designator:"Z_RESTORE_"+(i+1),otherProperty:fix[i].c.getState_OtherProperty()});\nfor(const x of fix)await eda.sch_PrimitiveComponent.modify(x.c,{designator:x.want,otherProperty:x.c.getState_OtherProperty()});\nif(await eda.sch_Document.save()!==true)throw new Error("页保存失败");const final=await eda.sch_PrimitiveComponent.getAll("part");return {count:final.length,changed:fix.length,\nrefs:final.map(c=>c.getState_Designator()).sort(),ok:final.every(c=>mapping.has(c.getState_UniqueId())&&c.getState_Designator()===mapping.get(c.getState_UniqueId()))};')
            assert restore['ok'],restore
            restored_refs.extend(restore['refs'])
        assert sorted(restored_refs)==expected_refs, '多页位号恢复未覆盖全设计或存在重复位号'
        if native_flags:
            # 真正的官方网络标识器件，禁止以PL/LINE图元拼出地和电源。
            # 先创建一个实际GND，使API装入默认标识库，再指定Power-VCC；
            # 否则首次默认库初始化会覆盖提前指定的VCC型号。
            from collections import Counter
            flag_checks=[]
            for page in sorted(pages,key=lambda p:p['name']):
                full_plan=native_flags[page['name']]
                plan=[p for p in full_plan if p['type']!='Port']
                open_document(invoke,page['uuid'])
                port_checks=invoke('const cs=await eda.sch_PrimitiveComponent.getAll("netport");const out=[];for(const c of cs){const pins=await eda.sch_PrimitiveComponent.getAllPinsByPrimitiveId(c.getState_PrimitiveId());out.push({id:c.getState_PrimitiveId(),net:c.getState_Net(),component:c.getState_Component(),pins});}return out;')
                expected_ports=Counter((p['net'],p['direction'],p['x'],p['y'],p['rotation']) for p in full_plan if p['type']=='Port')
                actual_ports=Counter((c['net'],c['component']['name'][8:],round(c['pins'][0]['x'],6),round(-c['pins'][0]['y'],6),(c['pins'][0]['rotation']-(0 if c['component']['name']=='Netport-IN' else 180))%360) for c in port_checks if len(c['pins'])==1)
                assert actual_ports==expected_ports, ('原生端口引脚或方向不一致',page['name'],actual_ports-expected_ports,expected_ports-actual_ports)
                power=invoke('return await eda.lib_Device.search("Power-VCC","0819f05c4eef4c71ace90d822a990e87",undefined,18,10,1);')
                vcc=next(p for p in power if p['name']=='Power-VCC')
                ordered=sorted(plan,key=lambda p:p['type']!='Ground')
                checks=[]
                for start in range(0,len(ordered),64):
                    code='const plan='+json.dumps(ordered[start:start+64])+'; const vcc='+json.dumps({'uuid':vcc['uuid'],'libraryUuid':vcc['libraryUuid']})+'; const out=[]; let configured=false;'
                    code+='''
for(const p of plan){
 if(p.type==="Power" && !configured){await eda.sch_PrimitiveComponent.setNetFlagComponentUuid_Power(vcc);configured=true;}
 const f=await eda.sch_PrimitiveComponent.createNetFlag(p.type,p.net,p.x,-p.y,0,false);
 if(!f || f.getState_ComponentType()!=="netflag" || f.getState_Net()!==p.net)throw new Error("标准符号创建失败");
 const pins=await eda.sch_PrimitiveComponent.getAllPinsByPrimitiveId(f.getState_PrimitiveId());
 if(pins.length!==1 || Math.abs(pins[0].x-p.x)>1e-6 || Math.abs(pins[0].y+p.y)>1e-6)throw new Error("符号锚点变化");
 const attrs=await eda.sch_PrimitiveAttribute.getAll(f.getState_PrimitiveId());
 for(const a of attrs)if(["Name","Global Net Name"].includes(a.getState_Key())){
  await eda.sch_PrimitiveAttribute.modify(a,{valueVisible:a.getState_Key()==="Name" && p.net!=="GND",keyVisible:false,fontSize:7/72});
 }
 out.push({net:p.net,type:p.type,direction:p.direction,id:f.getState_PrimitiveId(),component:f.getState_Component()});
}
await eda.sch_Document.save(); return out;'''
                    checks.extend(invoke(code))
                    print('官方内置符号 '+page['name']+' '+str(len(checks))+'/'+str(len(plan)),flush=True)

                assert len(checks)==len(plan)
                assert all(c['component']['name']==('Ground-GND' if c['type']=='Ground' else 'Power-VCC') for c in checks),checks
                nodes=normalize_standard_nodes(invoke)
                flag_checks.append({'page':page['name'],'flags':checks,'ports':port_checks,'nodes':nodes})
                park_document(page['uuid'])
            (audit_dir/'标准符号创建核验.json').write_text(json.dumps(flag_checks,ensure_ascii=False,indent=2),encoding='utf8')
        else:
            # 批量导入的原生特殊符号仍需实际客户端建立导线顶点关联。
            node_checks=[]
            for number,page in enumerate(sorted(pages,key=lambda p:p['name']),1):
                invoke_on_page(invoke,page['uuid'],page['uuid'],'return true;')
                def node_checkpoint():
                    nonlocal session, work
                    # SQLite history is committed asynchronously. Preserve the
                    # previous checkpoint, then reopen an independent path to
                    # avoid repeatedly mounting a cached client path.
                    time.sleep(2)
                    with closing(sqlite3.connect('file:' + work.as_posix() + '?mode=ro', uri=True)) as db:
                        assert db.execute('pragma integrity_check').fetchone()[0]=='ok'
                        persisted=db.execute('select count(*),coalesce(sum(length(dataStr)),0) from history_data').fetchone()
                        assert persisted[0]>initial_history[0] and persisted[1]>initial_history[1]+1000,('节点检查点尚未持久化',persisted)
                    cli(exe,'session','close','--session',session,'--destroy')
                    next_work=Path(tempfile.mkdtemp(prefix='节点独立重开-',dir=cache))/work.name
                    sqlite_copy(work,next_work)
                    work=next_work
                    session=cli(exe,'open','--path',work.as_posix(),'--headless','true')['value']['sessionId']
                    wait_for_project(invoke,attempts=90)
                    invoke_on_page(invoke,page['uuid'],page['uuid'],'return true;')
                    print('单页节点已保存并重开继续；仍为同一完整图页',flush=True)
                node_checks.append({'page':page['name'],'nodes':normalize_standard_nodes(invoke,node_checkpoint)})
                park_document(page['uuid'])
                if number%8==0:print('官方节点保存',number,'/',len(pages),flush=True)
            (audit_dir/'标准符号节点核验.json').write_text(json.dumps(node_checks,ensure_ascii=False,indent=2),encoding='utf8')
        open_document(invoke,first)
        # 官方导出补齐客户端文档元数据。FileSystem直接写缓存被客户端拒绝时，
        # 读取公开返回的File对象，由Python保存到本任务缓存；不修改客户端权限。
        exchange = invoke('''const f=await eda.sys_FileManager.getProjectFile("规范化工程",undefined,"epro2");
const a=new Uint8Array(await f.arrayBuffer());let s="";
for(let i=0;i<a.length;i+=32768)s+=String.fromCharCode(...a.subarray(i,i+32768));
return {name:f.name,size:f.size,data:btoa(s)};''')
        normalized = work.parent / (context['name']+'.epro2')
        payload = base64.b64decode(exchange['data'], validate=True)
        assert len(payload)==exchange['size'] and payload.startswith(b'PK')
        normalized.write_bytes(payload)
        with zipfile.ZipFile(normalized) as z:
            assert z.testzip() is None
        if folder_export:
            folder_export=Path(folder_export).resolve()
            assert not folder_export.exists(), '官方另存目标已经存在，停止覆盖'
            folder_export.parent.mkdir(parents=True,exist_ok=True)
            saved=invoke('const v=globalThis.gVars;return (await v.messageBus.rpcCall("/pro-mgr/projectAsCloud",{uuid:v.currentProject.projectId,info:{name:'+json.dumps(folder_export.name)+',path:'+json.dumps(folder_export.parent.as_posix())+',isFolder:true,owner:{uuid:v.loginedUserInfo.uuid},introduction:"",description:"",cbb_project:false},options:{needDlg:false,autoOpen:false,needTip:false},progressOptions:{needProgress:false}})).message;')
            assert saved and saved.get('success'), ('官方文件夹另存失败',saved)
            (work.parent/'官方文件夹另存.json').write_text(json.dumps(saved,ensure_ascii=False,indent=2),encoding='utf8')
            assert (folder_export/(folder_export.name+'.eprj3')).is_file(), ('官方文件夹另存落点不符',saved)
        # 文档save及交换导出先反映编辑器状态，SQLite历史快照另行异步提交。
        # 短工程不能在快照仍只有空模板时结束客户端，否则重开只剩默认P1。
        persisted = None
        for _ in range(120):
            with closing(sqlite3.connect('file:' + work.as_posix() + '?mode=ro', uri=True)) as db:
                persisted = db.execute('select count(*),coalesce(sum(length(dataStr)),0) from history_data').fetchone()
            if persisted[0] > initial_history[0] and persisted[1] > initial_history[1] + 1000:
                break
            time.sleep(.5)
        assert persisted[0] > initial_history[0] and persisted[1] > initial_history[1] + 1000, ('原生工程历史快照尚未持久化', initial_history, persisted)
    finally:
        try:
            cli(exe, 'session', 'close', '--session', session, '--destroy')
        except AssertionError as cleanup_error:
            if 'SESSION_NOT_FOUND' not in str(cleanup_error):raise
    with closing(sqlite3.connect(work)) as db, db:
        db.execute('update projects set default_sheet=?', (first,))
        assert db.execute('pragma integrity_check').fetchone()[0] == 'ok'
    assert sha(source)==source_hash, '官方导入期间源交换文件发生变化'
    return work, normalized


def power_anchor(x,y,net,segments,ground=False,up=False):
    """标准网络符号接在现有短引线端点，避免客户端合并线段内部的连接节点。"""
    choices=[]
    for x1,y1,x2,y2,n in segments:
        if n!=net:continue
        inside=(x1==x2==x and min(y1,y2)<y<max(y1,y2)) or (y1==y2==y and min(x1,x2)<x<max(x1,x2))
        if inside:
            for px,py in ((x1,y1),(x2,y2)):
                distance=abs(px-x)+abs(py-y)
                if 1e-5<distance<=10.00001:
                    score=py if ground==up else -py
                    choices.append((distance,score,px,py))
    return min(choices)[2:] if choices else (x,y)


def resolve_standard_port_plans(source,plans):
    """Record the exact <=10px same-wire endpoint adjustment used by import."""
    result=copy.deepcopy(plans);documents=[];changes=[]
    with zipfile.ZipFile(source) as z:
        text=z.read(next(n for n in z.namelist() if n.endswith('.epru'))).decode('utf8')
    for _,(a,b) in records(text):
        if a['type']=='DOCHEAD':documents.append([])
        documents[-1].append((a,b))
    for doc in documents:
        if doc[0][1]['docType']!='SCH_PAGE':continue
        title=next(b['title'] for a,b in doc if a['type']=='META');props={}
        for a,b in doc:
            if a['type']=='ATTR':props.setdefault(b['parentId'],{})[b['key']]=b['value']
        segments=[(b['startX'],b['startY'],b['endX'],b['endY'],props.get(b.get('lineGroup'),{}).get('NET')) for a,b in doc if a['type']=='LINE' and b.get('lineGroup')]
        for flag in result[title]:
            before=(flag['x'],flag['y'])
            after=power_anchor(*before,flag['net'],segments,ground=flag['type']=='Ground')
            assert abs(after[0]-before[0])+abs(after[1]-before[1])<=10.00001
            if after!=before:changes.append({'page':title,'net':flag['net'],'before':before,'after':after})
            flag.update(x=after[0],y=after[1])
    return result,changes


def insert_standard_ports(source,plans):
    """复用公开API保存的原生端口和电源地模板，避免逐个创建耗尽撤销内存。"""
    templates=json.loads((BASE.parent/'公共/库/标准网络端口.json').read_text(encoding='utf8'))
    with zipfile.ZipFile(source) as z:entries={n:z.read(n) for n in z.namelist()}
    filename=next(n for n in entries if n.endswith('.epru'))
    docs=[]
    for _,(a,b) in records(entries[filename].decode('utf8')):
        if a['type']=='DOCHEAD':docs.append([])
        docs[-1].append([a,b])
    title=lambda d:next(b['title'] for a,b in d if a['type']=='META')
    # 规范化交换文件已含真实端口时不重复写入；后续客户端核验数量和名称。
    device_names={d[0][1]['uuid']:title(d) for d in docs if d[0][1]['docType']=='DEVICE'}
    from collections import Counter
    existing_ports=any(v.startswith('Netport-') for v in device_names.values())
    existing_flags=any(v in ('Ground-GND','Power-VCC') for v in device_names.values())
    if existing_ports:
        actual={}
        for doc in docs:
            if doc[0][1]['docType']!='SCH_PAGE':continue
            props={}
            for a,b in doc:
                if a['type']=='ATTR':props.setdefault(b['parentId'],{})[b['key']]=b['value']
            actual[title(doc)]=Counter((v['Name'],device_names[v['Device']][8:]) for v in props.values() if device_names.get(v.get('Device'),'').startswith('Netport-'))
        assert actual=={p:Counter((f['net'],f['direction']) for f in plan if f['type']=='Port') for p,plan in plans.items()}, '已有端口实例不完整，禁止继续复用'
    if existing_flags:
        actual={}
        for doc in docs:
            if doc[0][1]['docType']!='SCH_PAGE':continue
            props={}
            for a,b in doc:
                if a['type']=='ATTR':props.setdefault(b['parentId'],{})[b['key']]=b['value']
            actual[title(doc)]=Counter((v.get('Name'),v.get('Global Net Name'),device_names[v['Device']]) for v in props.values() if device_names.get(v.get('Device')) in ('Ground-GND','Power-VCC'))
        assert actual=={p:Counter((f['net'],f['net'],'Ground-GND' if f['type']=='Ground' else 'Power-VCC') for f in plan if f['type']!='Port') for p,plan in plans.items()}, '已有电源地实例不完整，禁止继续复用'
    if existing_ports and existing_flags:return
    ids={d[0][1]['uuid'] for d in docs}
    for original in templates['库记录']:
        if original[0][1]['uuid'] in ids:continue
        doc=copy.deepcopy(original)
        if doc[0][1]['docType']=='SYMBOL' and title(doc) in ('Ground-GND','Power-VCC'):
            # 转换器交换工程使用向下坐标；导入会反转所有库坐标，不能混入向上模板。
            # PIN角度按官方交换序列化保留；位置及线段点转换后由客户端回读验证。
            # PART.BBOX不被该导入器反转，保留官方原生边界，避免最终选择框倒置。
            for a,b in doc:
                for key in ('y','originY','centerY','startY','endY','referenceY'):
                    if isinstance(b.get(key),(int,float)):b[key]=-b[key]
                for point in b.get('points',[]):
                    if isinstance(point,dict) and isinstance(point.get('y'),(int,float)):point['y']=-point['y']
                if 'yAxisDirection' in b:b['yAxisDirection']='down'
        docs.append(doc)
    ticket=max(a.get('ticket',0) for d in docs for a,b in d)
    for doc in docs:
        if doc[0][1]['docType']!='SCH_PAGE':continue
        page=title(doc);assert page in plans
        props={}
        for a,b in doc:
            if a['type']=='ATTR':props.setdefault(b['parentId'],{})[b['key']]=b['value']
        if len(plans)==1:
            port_names={p['net'] for p in plans[page] if p['type']=='Port'}
            # The standard port already names this signal. Retain the real
            # wire NET attribute, but do not print it again over the circuit.
            for a,b in doc:
                if a['type']=='ATTR' and b['key']=='NET' and b['value'] in port_names:
                    b.update(keyVisible=False,valueVisible=False)
        segments=[(b['startX'],b['startY'],b['endX'],b['endY'],props.get(b.get('lineGroup'),{}).get('NET')) for a,b in doc if a['type']=='LINE' and b.get('lineGroup')]
        zindex=max(b.get('zIndex',0) for a,b in doc)
        for number,plan in enumerate(plans[page]):
            isport=plan['type']=='Port'
            if (isport and existing_ports) or (not isport and existing_flags):continue
            direction=plan['direction'] if isport else plan['type']
            rows=copy.deepcopy(templates['实例模板'][direction])
            if isport and len(plans)==1:
                # A physical board is a single sheet. Same-sheet cross-reference
                # lists can repeat its name thousands of times, obscuring the
                # real circuit. Hide only this display attribute, not Name/NET.
                relevance=copy.deepcopy(next(row for row in rows if row[0]['type']=='ATTR' and row[1]['key']=='Name'))
                relevance[1].update(key='Relevance',value='',keyVisible=False,valueVisible=False)
                rows.append(relevance)
            cid=hashlib.sha256((page+'|standard|'+str(number)).encode()).hexdigest()[:16]
            x,y=plan['x'],plan['y'];rotation=plan['rotation'] if isport else 0
            x,y=power_anchor(x,y,plan['net'],segments,ground=direction=='Ground')
            assert rotation in (0,180)
            side=(-1 if direction=='IN' else 1)*(1 if rotation==0 else -1)
            for ordinal,(a,b) in enumerate(rows):
                ticket+=1;a['ticket']=ticket;b['yAxisDirection']='down';a['id']=cid if ordinal==0 else hashlib.sha256((cid+'|'+str(ordinal)).encode()).hexdigest()[:16]
                if a['type']=='COMPONENT':
                    zindex+=1;b.update(x=x,y=y,rotation=rotation,zIndex=zindex)
                else:
                    b['parentId']=cid
                    if isport and b['key']=='Name':b.update(value=plan['net'],x=x+side*(50 if direction=='OUT' else 45),y=y,rotation=0,fontSize=7/72*100,keyVisible=False,valueVisible=True,align='LEFT_MIDDLE' if side==1 else 'RIGHT_MIDDLE')
                    elif not isport and b['key'] in ('Name','Global Net Name'):
                        b.update(value=plan['net'],x=x,y=y+(25 if direction=='Ground' else -10),rotation=0,fontSize=7/72*100,keyVisible=False,valueVisible=b['key']=='Name' and direction=='Power',align='CENTER_MIDDLE' if direction=='Ground' else 'CENTER_BOTTOM')
                    elif b['x'] is not None:b.update(x=x,y=y+30)
            doc.extend(rows)
    entries[filename]=('\n'.join(record_json(a)+'||'+record_json(b)+'|' for d in docs for a,b in d)+'\n').encode('utf8')
    with zipfile.ZipFile(source,'w',zipfile.ZIP_DEFLATED) as z:
        for n,data in entries.items():z.writestr(n,data)


def normalize_folder_nodes(exe, project, exchange):
    """从独立磁盘副本重开后建立特殊符号关联，保留原索引和PCB。"""
    project=Path(project).resolve();index=json.loads(project.read_text(encoding='utf8'))
    copy_dir=Path(tempfile.mkdtemp(prefix='节点重开-',dir=CACHE))/'工程'
    shutil.copytree(project.parent,copy_dir)
    # 已保存的文件同样校正标准符号；只在同网10mil以内的短引线内平移。
    for relative in _schematic_paths(index):
        if relative.suffix!='.esch2':continue
        path=copy_dir/relative;rows=[r for _,r in records(path.read_text(encoding='utf8'))]
        rows,_=deduplicate_wire_lines(rows)
        props={};kind=None;page_rows=[]
        for a,b in rows:
            if a['type']=='DOCHEAD':kind=b['docType']
            if kind=='SCH_PAGE':page_rows.append((a,b))
            if kind=='SCH_PAGE' and a['type']=='ATTR':props.setdefault(b['parentId'],{})[b['key']]=b['value']
        segments=[(b['startX'],b['startY'],b['endX'],b['endY'],props.get(b.get('lineGroup'),{}).get('NET')) for a,b in page_rows if a['type']=='LINE' and b.get('lineGroup')]
        for a,b in page_rows:
            if a['type']!='COMPONENT':continue
            properties=props.get(a['id'],{})
            if 'Designator' in properties:continue
            net=properties.get('Global Net Name') or properties.get('Name')
            if not net:continue
            x,y=power_anchor(b['x'],b['y'],net,segments,ground=net=='GND',up=True);dx,dy=x-b['x'],y-b['y']
            if not (dx or dy):continue
            b.update(x=x,y=y)
            for aa,bb in page_rows:
                if aa['type']=='ATTR' and bb.get('parentId')==a['id']:
                    if bb.get('x') is not None:bb['x']+=dx
                    if bb.get('y') is not None:bb['y']+=dy
        path.write_text('\n'.join(record_json(a)+'||'+record_json(b)+'|' for a,b in rows)+'\n',encoding='utf8',newline='\n')
    session=cli(exe,'open','--path',(copy_dir/project.name).as_posix(),'--headless','true')['value']['sessionId']
    def invoke(code):return cli(exe,'invoke','--session',session,'--ext-uuid','eda','--timeout','60000','--code',code)['value']
    checks=[]
    try:
        wait_for_project(invoke,require_documents=False)
        pages=list(index['profile']['sheets'].values())
        parking=next(p['uuid'] for p in pages if p['title'].startswith('辅助电源板'))
        for page in sorted(pages,key=lambda p:p['title']):
            tab=open_document(invoke,page['uuid'])
            checks.append({'page':page['title'],'nodes':normalize_standard_nodes(invoke)})
            open_document(invoke,parking)
            if page['uuid']!=parking:assert invoke('return await eda.dmt_EditorControl.closeDocument('+json.dumps(tab)+');') is True
        open_document(invoke,index['default_sheet'])
        exported=invoke('const f=await eda.sys_FileManager.getProjectFile("节点规范化",undefined,"epro2");const a=new Uint8Array(await f.arrayBuffer());let s="";for(let i=0;i<a.length;i+=32768)s+=String.fromCharCode(...a.subarray(i,i+32768));return {size:f.size,data:btoa(s)};')
        payload=base64.b64decode(exported['data'],validate=True)
        assert len(payload)==exported['size'] and payload.startswith(b'PK')
    finally:cli(exe,'session','close','--session',session,'--destroy')
    # 客户端可能回写旧索引UUID，只提升经过修改的图页，原索引及其他文档原样保留。
    for relative in _schematic_paths(index):
        if relative.suffix=='.esch2':
            text=(copy_dir/relative).read_text(encoding='utf8')
            normalized='\n'.join(line for line,_ in records(text))+'\n'
            (project.parent/relative).write_text(normalized,encoding='utf8',newline='\n')
    Path(exchange).write_bytes(payload)
    (CACHE/'标准符号节点核验.json').write_text(json.dumps(checks,ensure_ascii=False,indent=2),encoding='utf8')
    project_documents(project)
    return checks


def canonical_project(exe, source, target=None, native_flags=None, native_pin_types=None):
    """缓存预处理后由客户端另存文件夹；最终页面使用官方序列化格式。"""
    source=Path(source).resolve();target=Path(target or PROJECT).resolve()
    CACHE.mkdir(parents=True,exist_ok=True)
    stage=Path(tempfile.mkdtemp(prefix='官方文件夹-',dir=CACHE))
    prepared=stage/'预处理';original_index=target/(NAME+'.eprj3')
    if original_index.exists():
        prepared.mkdir();shutil.copy2(original_index,prepared/original_index.name)
        if (target/'pcb').exists():shutil.copytree(target/'pcb',prepared/'pcb')
    staged_source=stage/source.name;shutil.copy2(source,staged_source)
    if native_flags:insert_standard_ports(staged_source,native_flags)
    build(staged_source,prepared)
    flags_to_create=native_flags
    if native_flags:
        with zipfile.ZipFile(staged_source) as z:
            text=z.read(next(n for n in z.namelist() if n.endswith('.epru'))).decode('utf8')
        existing={};port_attrs={};device_titles={};uid=None;page=None;kind=None
        for _,(a,b) in records(text):
            if a['type']=='DOCHEAD':kind=b['docType'];uid=b['uuid'];page=None
            elif a['type']=='META' and kind=='DEVICE':device_titles[uid]=b['title']
            elif a['type']=='META' and kind=='SCH_PAGE':page=b['title']
            elif page and a['type']=='ATTR':
                port_attrs.setdefault(page,{}).setdefault(b['parentId'],{})[b['key']]=b['value']
                if b['key']=='Global Net Name':existing.setdefault(page,[]).append(b['value'])
        if existing:
            # 复用已经含官方旗标的交换文件时不能再次创建；部分计划不接受。
            from collections import Counter
            assert {p:Counter(v) for p,v in existing.items()}=={
                p:Counter(f['net'] for f in plan if f['type']!='Port') for p,plan in native_flags.items() if any(f['type']!='Port' for f in plan)}, '已有电源旗标与本轮计划不一致'
            actual_ports={p:Counter((v['Name'],device_titles[v['Device']][8:]) for v in attrs.values() if device_titles.get(v.get('Device'),'').startswith('Netport-')) for p,attrs in port_attrs.items()}
            planned_ports={p:Counter((f['net'],f['direction']) for f in plan if f['type']=='Port') for p,plan in native_flags.items()}
            assert actual_ports==planned_ports, '已有网络端口与本轮计划不一致'
            flags_to_create=None
    official=stage/NAME
    work,normalized=native_import(exe,staged_source,flags_to_create,folder_export=official)
    project=adopt_official_folder(official,target,native_flags,native_pin_types)
    shutil.copyfile(normalized,source)
    normalize_folder_nodes(exe,project,source)
    return {'工程':str(project),'规范化交换文件':str(normalized),'缓存原生工程':str(work),
            '官方文件夹':str(official)}


def _schematic_paths(index):
    """只按工程索引确认允许替换/清理的原理图文件。"""
    profile=index['profile'];paths=set()
    for sch in profile['schematics'].values():
        name=sch['name'];assert name and '/' not in name and '\\' not in name and name not in ('.','..')
        paths.add(Path('sch')/name/(name+'.ecfg'))
    for page in profile['sheets'].values():
        name=profile['schematics'][page['schematic_uuid']]['name'];title=page['title']
        assert title and '/' not in title and '\\' not in title and title not in ('.','..')
        paths.add(Path('sch')/name/(title+'.esch2'))
    return paths


def _hide_power_label_text(text, names):
    """隐藏标准符号旁的导线文字，保留真实网络名称。"""
    kind=None;lines=[]
    for line,(a,b) in records(text):
        if a['type']=='DOCHEAD':kind=b['docType']
        if kind=='SCH_PAGE' and a['type']=='ATTR' and b['key']=='NET' and b['value'] in names:
            b.update(valueVisible=False,keyVisible=False);line=record_json(a)+'||'+record_json(b)+'|'
        lines.append(line)
    return '\n'.join(lines)+'\n'


NATIVE_PIN_TYPES = frozenset({
    'IN', 'OUT', 'BI', 'Passive', 'Open Collector', 'Open Emitter',
    'Power', 'Ground', 'HIZ', 'Terminator', 'Undefined',
})
LEGACY_NATIVE_PIN_TYPE_ALIASES = {
    'Input': 'IN', 'Output': 'OUT', 'Bidirectional': 'BI',
}


def normalize_native_pin_types(text, professional_pin_types):
    """只按 SYMBOL PIN 的 partId/Pin Number 规范 Pin Type，其他原生记录原样保留。"""
    assert isinstance(professional_pin_types, dict), '审定引脚类型必须是型号-针号映射'
    if not professional_pin_types:return text,{},0
    assert all(isinstance(model, str) and isinstance(pins, dict) for model, pins in professional_pin_types.items()), '型号和针号映射必须是字典'
    for model, pins in professional_pin_types.items():
        assert all(isinstance(number, str) and number and value in NATIVE_PIN_TYPES
                   for number, value in pins.items()), ('目标类型不是专业版原生枚举', model, pins)
    docs=[];current=None
    for line,(a,b) in records(text):
        if a['type']=='DOCHEAD':
            if current:docs.append(current)
            current={'kind':b['docType'],'rows':[]}
        assert current is not None, '原生文件在 DOCHEAD 前包含记录'
        current['rows'].append((line,a,b))
    if current:docs.append(current)
    output=[];coverage={};changed=0
    for doc in docs:
        if doc['kind']!='SYMBOL':
            output.extend(line for line,_,_ in doc['rows']);continue
        attrs=collections.defaultdict(lambda:collections.defaultdict(list))
        for _,a,b in doc['rows']:
            if a['type']=='ATTR':attrs[b.get('parentId')][b.get('key')].append((a,b))
        substitutions={};models=collections.defaultdict(set)
        for _,a,b in doc['rows']:
            if a['type']!='PIN':continue
            part=b.get('partId','');mpn=part.rsplit('.',1)[0]
            if mpn not in professional_pin_types:continue
            number_rows=attrs[a['id']].get('Pin Number',[])
            type_rows=attrs[a['id']].get('Pin Type',[])
            assert len(number_rows)==len(type_rows)==1,(mpn,a['id'],len(number_rows),len(type_rows))
            number=str(number_rows[0][1]['value']);assert number in professional_pin_types[mpn],(mpn,number)
            assert number not in models[mpn],('目标型号在符号中重复针号',mpn,number)
            models[mpn].add(number);coverage.setdefault(mpn,set()).add(number)
            attr_a,attr=type_rows[0];new_type=professional_pin_types[mpn][number]
            assert attr['value'] in NATIVE_PIN_TYPES or attr['value'] in LEGACY_NATIVE_PIN_TYPE_ALIASES,(mpn,number,attr['value'])
            if attr['value']!=new_type:
                substitutions[attr_a['id']]=new_type
        for mpn,numbers in models.items():
            assert numbers==set(professional_pin_types[mpn]),(mpn,numbers,set(professional_pin_types[mpn]))
        for line,a,b in doc['rows']:
            if a['type']=='ATTR' and a['id'] in substitutions:
                before=dict(b);b['value']=substitutions[a['id']]
                assert {k:v for k,v in before.items() if k!='value'}=={k:v for k,v in b.items() if k!='value'}
                line=record_json(a)+'||'+record_json(b)+'|';changed+=1
            output.append(line)
    for mpn,numbers in coverage.items():
        assert numbers==set(professional_pin_types[mpn]),(mpn,numbers,set(professional_pin_types[mpn]))
    return '\n'.join(output)+'\n',coverage,changed


def adopt_official_folder(official, target=None, native_flags=None, native_pin_types=None):
    """提升官方文件夹，保留原PCB字节；板关联按名称回映到原板UUID。"""
    official=Path(official).resolve();target=Path(target or PROJECT).resolve()
    assert official!=target and not official.is_relative_to(target), '官方候选必须位于独立缓存目录'
    index_path=official/(NAME+'.eprj3');index=json.loads(index_path.read_text(encoding='utf8'))
    previous_path=target/index_path.name
    previous=json.loads(previous_path.read_text(encoding='utf8')) if previous_path.exists() else None
    profile=index['profile'];old_profile=(previous or {}).get('profile',{})
    groups=('驱动主板','辅助电源板','中央稳压模块')
    old_boards={v.get('title',v.get('name')):uid for uid,v in old_profile.get('boards',{}).items()}
    official_boards={v.get('title',v.get('name')):uid for uid,v in profile['boards'].items()}
    assert set(official_boards)==set(groups) and len(profile['boards'])==3, '官方输出板列表不完整或重复'
    assert set(v['name'] for v in profile['schematics'].values())==set(groups)|{'系统接线'} and len(profile['schematics'])==4
    mapping={uid:old_boards.get(name,uid) for name,uid in official_boards.items()}
    profile['boards']={mapping[uid]:dict(v,uuid=mapping[uid]) for uid,v in profile['boards'].items()}
    for sch in profile['schematics'].values():
        sch['board']=mapping.get(sch.get('board',''),sch.get('board',''))
        assert sch['board']==('' if sch['name']=='系统接线' else mapping[official_boards[sch['name']]])
    main_sch=next(uid for uid,v in profile['schematics'].items() if v['name']=='驱动主板')
    main_pages=[p for p in profile['sheets'].values() if p['schematic_uuid']==main_sch]
    assert main_pages, '官方输出缺少驱动主板页'
    first=min(main_pages,key=lambda p:p.get('zIndex',0))['uuid']
    index['default_sheet']=first
    # 官方config是BOARD/CONFIG记录串，保留UNIVERSAL等真实项目设置。
    assert isinstance(index['config'],str), '官方文件夹CONFIG格式变化，停止手工猜测'
    rows=[];kind=None;defaults=[]
    for _,(a,b) in records(index['config']):
        if a['type']=='DOCHEAD':
            kind=b['docType']
            if kind=='BOARD':b['uuid']=mapping[b['uuid']]
        elif a['type']=='META' and kind=='CONFIG':b['defaultSheet']=first;defaults.append(first)
        rows.append(record_json(a)+'||'+record_json(b)+'|')
    assert defaults==[first], '官方CONFIG缺少唯一默认页'
    index['config']='\n'.join(rows)+'\n'
    outputs={};paths=_schematic_paths(index);pin_type_coverage={}
    page_ids=set();sch_ids=set()
    for name in sorted(paths):
        p=official/name;assert p.is_file(), ('官方文件夹缺少索引文档',name)
        text=p.read_text(encoding='utf8');kind=None;rows=[]
        for line,(a,b) in records(text):
            if a['type']=='DOCHEAD':
                kind=b['docType']
                if kind=='SCH_PAGE':
                    assert b['uuid'] in profile['sheets'];page_ids.add(b['uuid'])
                elif kind=='SCH':
                    assert b['uuid'] in profile['schematics'];sch_ids.add(b['uuid'])
            elif a['type']=='META' and kind=='SCH':
                b['board']=mapping.get(b.get('board',''),b.get('board',''))
                line=record_json(a)+'||'+record_json(b)+'|'
            elif a['type']=='META' and kind=='SCH_PAGE':
                assert b['schematic'] in profile['schematics'], ('官方页所属原理图缺失',p)
            rows.append(line)
        text='\n'.join(rows)+'\n'
        if native_flags and p.suffix=='.esch2':
            assert p.stem in native_flags, ('缺少页面电源标签计划',p.stem)
            text=_hide_power_label_text(text,{f['net'] for f in native_flags[p.stem]})
        if native_pin_types and p.suffix=='.esch2':
            text,coverage,_=normalize_native_pin_types(text,native_pin_types)
            for mpn,numbers in coverage.items():
                pin_type_coverage.setdefault(mpn,set()).update(numbers)
        outputs[name]=text.encode('utf8')
    if native_pin_types:
        assert pin_type_coverage=={mpn:set(pins) for mpn,pins in native_pin_types.items()},('官方导出未覆盖目标针脚',pin_type_coverage,native_pin_types)
    assert page_ids==profile['sheets'].keys() and sch_ids==profile['schematics'].keys(), '官方文档与索引UUID不一致'
    # 原板PCB不能接受官方另存时的META重编；关联由原板UUID保持一致。
    pcb_source=target if previous else official
    preserved={p.relative_to(pcb_source):sha(p) for p in (pcb_source/'pcb').rglob('*') if p.is_file()}
    profile['pcbs']=copy.deepcopy(old_profile.get('pcbs',{}) if previous else profile.get('pcbs',{}))
    for uid,pcb in profile['pcbs'].items():
        board=profile['boards'].get(pcb['board']);assert board and board.get('title',board.get('name')) in groups
        p=pcb_source/'pcb'/(pcb['title']+'.epcb2');assert p.is_file()
        heads=[b for _,(a,b) in records(p.read_text(encoding='utf8')) if a['type']=='DOCHEAD' and b['docType']=='PCB']
        assert len(heads)==1 and heads[0]['uuid']==uid, ('PCB索引与真实文档不一致',p)
    assert len(profile['pcbs'])==len(list((pcb_source/'pcb').rglob('*.epcb2'))), '存在未索引PCB，停止提升'
    index['pcb_count']=len(profile['pcbs'])
    outputs[Path(index_path.name)]=(json.dumps(index,ensure_ascii=False,indent=2)+'\n').encode('utf8')
    old_files={p.relative_to(target) for p in target.rglob('*') if p.is_file()} if target.exists() else set()
    known=(_schematic_paths(previous) if previous else set())|{Path('eprj3-intro.md')}
    kept={p for p in old_files if p in preserved or p.suffix=='.evar'}
    obsolete=old_files-kept-outputs.keys()
    assert obsolete<=known, ('工程含未知文件，停止覆盖',sorted(map(str,obsolete-known)))
    CACHE.mkdir(parents=True,exist_ok=True)
    if old_files:
        backup=CACHE/('官方文件夹提升前-'+str(time.time_ns())+'.zip')
        with zipfile.ZipFile(backup,'w',zipfile.ZIP_DEFLATED) as z:
            for name in sorted(old_files):z.write(target/name,name)
        with zipfile.ZipFile(backup) as z:assert z.testzip() is None and len(z.namelist())==len(old_files)
    for name,data in outputs.items():
        p=target/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
    if not previous:
        for name in preserved:
            p=target/name;p.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(official/name,p)
    for name in obsolete:
        p=(target/name).resolve()
        assert p.is_relative_to(target) and (p.suffix in ('.esch2','.ecfg') or name==Path('eprj3-intro.md'))
        p.unlink()
    for p in sorted((target/'sch').rglob('*'),key=lambda p:len(p.parts),reverse=True):
        if p.is_dir() and not any(p.iterdir()):p.rmdir()
    assert all(sha(target/name)==digest for name,digest in preserved.items()), '提升官方文件夹改变了原PCB文件'
    return target/index_path.name


def verify_native_pin_type_fields(paths, professional_pin_types):
    """读取实际原生属性；规范化若还需改值，表示保存结果未保留审定类型。"""
    coverage={}
    for path in paths:
        _,found,changed=normalize_native_pin_types(path.read_text(encoding='utf8'),professional_pin_types)
        assert changed==0, ('客户端未保留审定引脚类型',str(path),changed)
        for model,pins in found.items():coverage.setdefault(model,set()).update(pins)
    assert coverage=={model:set(pins) for model,pins in professional_pin_types.items()}, ('原生审定引脚覆盖不完整',coverage)
    return {'实际原生字段一致':True,'已审定型号数':len(coverage),
            '已审定型号针脚数':sum(map(len,coverage.values())),
            '范围':'已审定型号逐针类型；未审定型号及全图电气正确性不由此证明'}


def hide_conversion_power_labels(project,native_flags):
    """内置符号已创建后隐藏临时转换标签；保留其NET和实体导线。"""
    for p in project.parent.rglob('*.esch2'):
        names={f['net'] for f in native_flags[p.stem]}
        p.write_text(_hide_power_label_text(p.read_text(encoding='utf8'),names),encoding='utf8',newline='\n')


def native_project(exe):
    """官方生成内部eprj2缓存，独立重开核验；不进入交付。"""
    work, _ = native_import(exe, EXCHANGE)
    # 缓存候选必须独立重开通过后才允许覆盖现有交付；加载错误保留原件。
    verify_native(exe, work, record=False)
    target = CACHE / (NAME + '.eprj2')
    sqlite_copy(work, target)
    return verify_native(exe)


def verify_native(exe, target=None, record=False):
    """独立核验现有交付工程；占用中的原文件只读，客户端操作仅作用于缓存副本。"""
    target = target or CACHE / (NAME + '.eprj2')
    original_hash = sha(target)
    expected_pages = len(json.loads((PROJECT / (NAME + '.eprj3')).read_text(encoding='utf-8'))['profile']['sheets'])
    with closing(sqlite3.connect('file:' + target.as_posix() + '?mode=ro', uri=True)) as db:
        assert db.execute('pragma integrity_check').fetchone()[0] == 'ok'
        first = db.execute('select default_sheet from projects').fetchone()[0]
    def invoke(code):
        return cli(exe, 'invoke', '--session', session, '--ext-uuid', 'eda', '--timeout', '60000', '--code', code)['value']
    # 客户端按原路径缓存旧页UUID；从交付文件只读备份后在新路径重开，
    # 验证文件自身内容，避免将缓存中的旧页误当本轮交付内容。
    verification = Path(tempfile.mkdtemp(prefix='原生重开-',dir=CACHE))/(NAME+'.eprj2')
    sqlite_copy(target,verification)
    session = cli(exe, 'open', '--path', verification.as_posix(), '--headless', 'true')['value']['sessionId']
    try:
        wait_for_project(invoke, require_documents=False)
        tab = invoke('return await eda.dmt_EditorControl.openDocument(' + json.dumps(first) + ');')
        for _ in range(10):
            if tab: break
            time.sleep(0.5)
            tab = invoke('return await eda.dmt_EditorControl.openDocument(' + json.dumps(first) + ');')
        assert tab, '原生工程重开第一页未就绪'
        assert invoke('return await eda.dmt_EditorControl.activateDocument(' + json.dumps(tab) + ');') is True
        native=read_all_schematics(invoke)
        assert len(native['pages'])==expected_pages, '原生工程页面不完整'
        (CACHE / '原生客户端网表.json').write_text(json.dumps(native,ensure_ascii=False),encoding='utf-8')
    finally:
        cli(exe, 'session', 'close', '--session', session, '--destroy')
    reference = json.loads((CACHE / '客户端网表.json').read_text(encoding='utf-8'))['value']['data']
    def normalized(data):
        result = {}
        for component in json.loads(data)['components'].values():
            p = component['props']; ref = p['Designator']
            result[ref] = {k: p.get(k, '') for k in ('Manufacturer Part', 'Convert to PCB', 'FootprintName')}
            result[ref]['pins'] = {k: v.get('net', '') for k, v in component['pinInfoMap'].items()}
        return result
    assert normalized(native['data']) == normalized(reference), '原生工程与已核验文件夹工程不一致'
    assert sha(target) == original_hash, '核验期间原生交付文件发生变化，停止记录结论'
    if not record: return target
    report_path = REPORT / '原理图核验.json'
    assert report_path.is_file(), '缺少当前源核验记录；先按当前设计源重新生成并核验，不继承旧客户端结果'
    report = json.loads(report_path.read_text(encoding='utf-8'))
    report['嘉立创原生工程'] = {'文件': str(target.resolve()), 'SHA256': sha(target), '页数': expected_pages,
                              '客户端重开保存与逐脚网表一致': True, '默认打开第一页': first,
                              '原生ERC': native['erc'], '数据库完整性': True,
                              '说明': '由嘉立创官方导入接口写入eprj2；交付文件只读备份至新路径，排除旧页UUID缓存后独立重开、保存及逐脚比较'}
    report_path.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(report['嘉立创原生工程'], ensure_ascii=False, indent=2))
    return target


def project_documents(project):
    """核对eprj3索引引用的真实磁盘文件和文档UUID，覆盖配置、图页及PCB。"""
    project=Path(project).resolve()
    assert project.is_file(), ('工程索引不是可读取的磁盘文件；请先完整解压工程',str(project))
    index=json.loads(project.read_text(encoding='utf8'));profile=index['profile'];wanted=[]
    for uid,row in profile['schematics'].items():
        assert uid==row['uuid']
        name=row['name'];assert name and '/' not in name and '\\' not in name and name not in ('.','..')
        wanted.append((Path('sch')/name/(name+'.ecfg'),'SCH',uid))
    for uid,row in profile['sheets'].items():
        assert uid==row['uuid']
        name=profile['schematics'][row['schematic_uuid']]['name'];title=row['title']
        assert title and '/' not in title and '\\' not in title and title not in ('.','..')
        wanted.append((Path('sch')/name/(title+'.esch2'),'SCH_PAGE',uid))
    for group,folder,extension,kind in (('pcbs','pcb','.epcb2','PCB'),('panels','panel','.epan2','PANEL')):
        for uid,row in profile.get(group,{}).items():
            assert uid==row['uuid']
            title=row['title'];assert title and '/' not in title and '\\' not in title and title not in ('.','..')
            wanted.append((Path(folder)/(title+extension),kind,uid))
    missing=[{'UUID':uid,'文件':str(relative)} for relative,kind,uid in wanted if not (project.parent/relative).is_file()]
    assert not missing, ('工程索引引用的文档缺失；必须解压并保留整个工程目录，不能只打开ZIP内索引',missing)
    verified=[]
    for relative,kind,uid in wanted:
        path=project.parent/relative
        headers=[b for _,(a,b) in records(path.read_text(encoding='utf8')) if a['type']=='DOCHEAD' and b.get('docType')==kind]
        assert len(headers)==1 and headers[0]['uuid']==uid, ('索引与文档UUID不一致',str(relative),uid,headers)
        verified.append({'文件':relative.as_posix(),'文档类型':kind,'UUID':uid})
    default=index.get('default_sheet')
    assert default in profile['sheets'], ('默认页引用无效',default)
    return {'完整磁盘工程':True,'索引引用文档数':len(verified),'缺失文档':[],
            '默认页已设置':default in profile['sheets'],
            '默认页边界':'官方另存未指定默认页；调用方须按本版标题显式打开并核对' if default not in profile['sheets'] else '有效页UUID',
            '索引及文档UUID一致':True,'文档':verified,
            '打开要求':'从普通磁盘目录打开.eprj3，保留同级sch/pcb；收到ZIP须先完整解压'}


def check(exe, project=None):
    project = project or PROJECT / (NAME + '.eprj3')
    disk_documents=project_documents(project)
    index = json.loads(project.read_text(encoding='utf-8'))
    files = sorted(project.parent.rglob('*.esch2'))
    count = 0
    for p in files:
        text = p.read_text(encoding='utf-8')
        assert text.endswith('|\n'), p
        for line, (a, b) in records(text):
            count += 1
        assert all(l.endswith('|') for l in text.split('\n') if l), p
    assert len(files) == len(index['profile']['sheets']) and files
    CACHE.mkdir(parents=True, exist_ok=True)
    verification = Path(tempfile.mkdtemp(prefix='文件夹重开-', dir=CACHE)) / '工程'
    shutil.copytree(project.parent, verification)
    opened = cli(exe, 'open', '--path', (verification/project.name).as_posix(), '--headless', 'true')
    session = opened['value']['sessionId']
    try:
        def invoke(code):
            return cli(exe,'invoke','--session',session,'--ext-uuid','eda','--timeout','60000','--code',code)['value']
        wait_for_project(invoke, require_documents=False)
        first=min(index['profile']['sheets'].values(),key=lambda p:p['zIndex'])['uuid']
        open_document(invoke,first)
        value=read_all_schematics(invoke)
        raw={'value':value}
        (CACHE / '客户端网表.json').write_text(json.dumps(raw,ensure_ascii=False),encoding='utf-8')
        version = cli(exe, 'doctor')['value']['bridgeVersion']
    finally:
        cli(exe, 'session', 'close', '--session', session, '--destroy')
    # 客户端也可能给配置的末条记录省略结束符；保存后统一规范，再记录最终哈希。
    for p in project.parent.rglob('*.ecfg'):
        lines = [line for line, _ in records(p.read_text(encoding='utf-8'))]
        p.write_text('\n'.join(lines) + '\n', encoding='utf-8', newline='\n')
    count = 0
    for p in files:
        text = p.read_text(encoding='utf-8')
        assert text.endswith('|\n') and all(l.endswith('|') for l in text.split('\n') if l), p
        count += sum(1 for _ in records(text))
    value = raw['value']
    actual = json.loads(value['data'])['components']
    parts = runpy.run_path(str(BASE / '设计数据.py'))['PARTS']
    pin_types=runpy.run_path(str(BASE.parent/'公共/工具/生成可编辑原理图.py'))['PROFESSIONAL_PIN_TYPES']
    models={p['mpn'] for p in parts}
    pin_types={model:pins for model,pins in pin_types.items() if model in models}
    native_pin_type_result=verify_native_pin_type_fields(sorted(verification.rglob('*.esch2')),pin_types)
    native_pin_type_result['未审定IC型号']=sorted({p['mpn'] for p in parts if p['ref'].startswith('U')}-set(pin_types))
    binding = json.loads((BASE.parent / '公共/库' / '封装绑定.json').read_text(encoding='utf-8'))
    assert binding['设计源SHA256'] == sha(BASE / '设计数据.py')
    bindings = {b['位号']: b for b in binding['位号绑定']}
    expected, nc, outside, pending = {}, set(), [], []
    for p in parts:
        b = bindings[p['ref']]
        if b['安装'] == '板外': outside.append(p['ref'])
        if b['安装'] == '待设计': pending.append(p['ref'])
        for pin, net in p['pins'].items():
            key = (p['ref'], str(b['引脚映射'][pin]))
            if net.startswith('NC_'): nc.add(key)
            else:
                assert key not in expected or expected[key] == net
                expected[key] = net
    got, blank, refs = {}, set(), set()
    for c in actual.values():
        props = c['props']; ref = props['Designator']; b = bindings[ref]
        assert ref not in refs; refs.add(ref)
        assert props['Manufacturer Part'] == b['型号'], ref
        assert props['Convert to PCB'] == ('yes' if b['安装'] == '板上' else 'no'), ref
        assert props.get('FootprintName', '') == (b['封装'] or ''), ref
        for number, pin in c['pinInfoMap'].items():
            key = (ref, str(number)); net = pin.get('net', '')
            if net: got[key] = net
            else: blank.add(key)
    assert refs == {p['ref'] for p in parts}
    assert got == expected, {'missing_or_wrong': list(set(expected.items()) - set(got.items()))[:10], 'unexpected': list(set(got.items()) - set(expected.items()))[:10]}
    assert blank == nc, {'missing_nc': sorted(nc - blank), 'unexpected_blank': sorted(blank - nc)}
    assert len(value['pages']) == len(files)
    saved_files=[verification/p.relative_to(project.parent) for p in files]
    geometry=wire_geometry(saved_files,expected,nc)
    rendered_labels=[]
    for path in saved_files:
        page_uuid=None;net_ids=set();kind=None
        for _,(a,b) in records(path.read_text(encoding='utf8')):
            if a['type']=='DOCHEAD':
                kind=b['docType']
                if kind=='SCH_PAGE':page_uuid=b['uuid']
            elif kind=='SCH_PAGE' and a['type']=='ATTR' and b.get('key')=='NET':net_ids.add(a['id'])
        rendered=next(p for p in value['rendered'] if p['页UUID']==page_uuid)
        bare=sorted(net_ids.intersection(rendered['可见文字图元ID']))
        assert not bare, ('客户端重开后自动显示裸网络文字',path.name,bare)
        rendered_labels.append({'图页':path.stem,'客户端SVG可见裸网络文字':len(bare)})
    report_path = REPORT / '原理图核验.json'
    report = json.loads(report_path.read_text(encoding='utf-8')) if report_path.exists() else {}
    warning_count = sum(r['count'] for r in value['erc'] if r['type'] == 'warn')
    erc_pass = not any(r['count'] for r in value['erc'])
    details = erc_details(value['ercMessages'], index)
    for level in ('fatalError', 'error', 'warn'):
        assert sum(d['等级'] == level for d in details) == sum(r['count'] for r in value['erc'] if r['type'] == level), 'ERC明细和摘要不一致'
    waived, boundaries, defects = [], [], []
    for d in details:
        if d['规则'] == '缺少封装' and d['对象'] and all(o['对象'] in outside for o in d['对象']):
            d['处理'] = '板外接线/机械器件，不转PCB；PCB封装规则不适用，保留空封装'
            waived.append(d)
        elif (d['规则'] == '单引脚网络' and len(d['对象']) == 1 and d['对象文本'].startswith('SHIELD ')
              and [(ref, pin) for (ref, pin), net in expected.items() if net == 'SHIELD'] == [('J_CAN', '4')]):
            d['处理'] = 'J_CAN.4为板外线束屏蔽边界；按设计要求仅在电缆入口连接机壳，不在PCB上短接GND。已在图页标注，单板ERC无法看到机壳。'
            waived.append(d)
        else:
            boundary=cross_schematic_boundary(d,index,saved_files,expected)
            if boundary:
                d['处理']='跨原理图边界单端网络，已回读对象真实网络并核对其他原理图端子'
                d['边界证据']=boundary;boundaries.append(d)
            else: defects.append(d)
    report.pop('单页实体导线',None)
    report.update({'工程磁盘文档核验':disk_documents,'原生引脚属性核验':native_pin_type_result,'分板几何核验':geometry,'客户端图面网名核验':rendered_labels,'分板原理图':value['schematics'],
                   '器件': len(refs), '板上封装绑定': sum(b['安装']=='板上' and bool(b['封装']) for b in bindings.values()), '候选封装绑定': sum(b['安装']=='待设计' and bool(b['封装']) for b in bindings.values()), '板外器件': len(outside), '待设计位号': sorted(pending),
                   '网络': len(set(got.values())), '连接节点': len(got), '明确不连接': len(blank), '页数': len(files),
                   '专业版回读连接一致': True, '设计源SHA256': sha(BASE / '设计数据.py'),
                   '工程SHA256': sha(project), '现代交换工程SHA256': sha(EXCHANGE),
                   '工程文件SHA256': {p.relative_to(project.parent).as_posix(): sha(p) for p in sorted(project.parent.rglob('*')) if p.is_file()},
                   '客户端版本': version, '客户端加载及保存验收': True, '界面导入验收': False,
                   '验证方法': '交付工程复制至新路径，逐页打开保存、逐板原理图网表聚合，与设计全器件逐引脚和NC比较',
                   '客户端网表SHA256': hashlib.sha256(value['data'].encode('utf-8')).hexdigest(),
                   '现代记录数量': count, '记录结束符核验': True,
                   '电气规则检查ERC': erc_pass, 'ERC已执行': True, 'ERC原始结果': value['erc'],
                   'ERC明细已取得': True, 'ERC实际待修问题': defects, 'ERC板外规则例外': waived,
                   'ERC跨板边界例外':boundaries,
                   'ERC工程范围判定通过': not defects,
                   'ERC待处理': {'缺封装板外器件': sorted(outside), '说明': f'原生ERC：{len(waived)}条明确板外规则例外、{len(boundaries)}条有端子证据的跨板边界例外、{len(defects)}条实际待修问题；全部明细与摘要逐等级一致。'},
                   'PCB布局布线': False})
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({k: report[k] for k in ('器件', '连接节点', '明确不连接', '页数', '客户端加载及保存验收', 'ERC原始结果')}, ensure_ascii=False, indent=2))
    return report


def isolated_api_check(exe, template, target, report_path):
    """仅在工作根缓存内创建两电阻小图；保留逐阶段事实，失败返回非零。"""
    global CACHE
    root = Path(__file__).resolve().parents[3]
    target = target.resolve(); template = template.resolve(); report_path = report_path.resolve()
    assert all(p.is_relative_to(root) for p in (target, template, report_path))
    assert report_path.is_file() and not target.exists()
    CACHE = target.parent
    CACHE.mkdir(parents=True, exist_ok=True)
    result = {'客户端': str(exe), '创建': False, '修改保存': False, '独立重开': False,
              'ERC已调用': False, '有效网表': False, '工作工程': str(target.relative_to(root))}
    sessions = []; session = None; phase = 'open'
    def invoke(code):
        return cli(exe, 'invoke', '--session', session, '--ext-uuid', 'eda',
                   '--timeout', '60000', '--code', code)['value']
    def record():
        report = json.loads(report_path.read_text(encoding='utf8'))
        report.setdefault('native_validation', {})['工具隔离验证'] = result
        report_path.write_text(json.dumps(report, ensure_ascii=False, indent=2)+'\n', encoding='utf8')
    try:
        sqlite_copy(template, target)
        session = cli(exe, 'open', '--path', target.as_posix(), '--headless', 'true')['value']['sessionId']
        sessions.append(session)
        wait_for_project(invoke, require_documents=False)
        phase = 'create_page'
        page = invoke('const s=await eda.dmt_Schematic.createSchematic();if(!s)throw new Error("原理图创建失败");const p=await eda.dmt_Schematic.createSchematicPage(s);if(!p)throw new Error("页面创建失败");return p;')
        open_document(invoke, page)
        phase = 'create_parts_and_wires'
        created = invoke('''const items=await eda.lib_Device.search('0603WAF1001T5E');
const lib=items.find(x=>x.name==='0603WAF1001T5E');if(!lib)throw new Error('精确器件未找到');
const pins=[];const ids=[];
for(const [ref,x] of [['R1',400],['R2',700]]){
const c=await eda.sch_PrimitiveComponent.create(lib,x,600,undefined,90,false,true,true);
if(!c)throw new Error('元件创建失败');const id=c.getState_PrimitiveId();
const pre=(await eda.sch_PrimitiveComponent.get(id)).getState_OtherProperty();
await eda.sch_PrimitiveComponent.modify(id,{designator:ref,otherProperty:pre});
const pp=await eda.sch_PrimitiveComponent.getAllPinsByPrimitiveId(id);
if(pp.length!==2)throw new Error('电阻引脚不符');pp.sort((a,b)=>a.y-b.y);pins.push(pp);ids.push(id);
}
const low=Math.min(...pins.map(p=>p[0].y))-50,high=Math.max(...pins.map(p=>p[1].y))+50;
for(const [i,y,net] of [[0,low,'GND'],[1,high,'TEST_PWR']]){
const a=pins[0][i],b=pins[1][i];
await eda.sch_PrimitiveWire.create([a.x,a.y,a.x,y,b.x,y,b.x,b.y],net);
}
await eda.sch_PrimitiveComponent.createNetFlag('Ground','GND',pins[0][0].x,low,0,false);
await eda.sch_PrimitiveComponent.createNetFlag('Power','TEST_PWR',pins[0][1].x,high,0,false);
const text=await eda.sch_PrimitiveText.create(400,780,'API isolated check before');
if(!text||await eda.sch_Document.save()!==true)throw new Error('创建保存失败');
return {ids,textId:text.getState_PrimitiveId(),parts:2,pins:pins.flat().map(p=>({n:p.pinNumber,x:p.x,y:p.y})),libraryUuid:lib.libraryUuid,deviceUuid:lib.uuid};''')
        result.update(创建=True, 创建回读=created, 图页UUID=page)
        phase = 'modify_save'
        result['修改保存回读'] = edit_native_text(invoke, page, created['textId'],
                                                'API isolated check before', 'API isolated check saved')
        result['修改保存'] = True
        time.sleep(8)
        result['创建图ERC结果'] = invoke(ERC_CODE)
        result['ERC已调用'] = True
        first_net = invoke('const f=await eda.sch_ManufactureData.getNetlistFile("隔离网表","JLCEDA");return f?{data:await f.text(),size:f.size}:null;')
        result['创建图网表返回'] = {'有数据': bool(first_net and first_net.get('data')),
                                   '字节': first_net['size'] if first_net else 0}
        # 保留原窗口到独立副本已打开，避免最后窗口销毁时owner关闭与新open竞争。
        phase = 'independent_reopen'
        reopen = target.with_name(target.stem+'-独立重开.eprj2')
        assert not reopen.exists()
        sqlite_copy(target, reopen)
        session = cli(exe, 'open', '--path', reopen.as_posix(), '--headless', 'true')['value']['sessionId']
        sessions.append(session)
        wait_for_project(invoke); open_document(invoke, page)
        got = invoke('return {refs:(await eda.sch_PrimitiveComponent.getAll("part")).map(c=>c.getState_Designator()),texts:(await eda.sch_PrimitiveText.getAll()).map(t=>t.getState_Content()),wires:(await eda.sch_PrimitiveWire.getAll()).map(w=>({net:w.getState_Net(),line:w.getState_Line()}))};')
        result['独立重开回读'] = got
        assert sorted(got['refs']) == ['R1','R2'] and 'API isolated check saved' in got['texts'], got
        assert {w['net'] for w in got['wires']} == {'GND','TEST_PWR'}
        result.update(独立重开=True, 独立重开回读=got)
        time.sleep(8)
        phase = 'ERC_netlist'
        result['ERC结果'] = invoke(ERC_CODE); result['ERC已调用'] = True
        raw = invoke('const f=await eda.sch_ManufactureData.getNetlistFile("隔离网表","JLCEDA");return f?{data:await f.text(),size:f.size}:null;')
        if raw and raw.get('data'):
            netlist = json.loads(raw['data']); components=netlist['components']
            actual = {c['props']['Designator']:{str(n):p.get('net','') for n,p in c['pinInfoMap'].items()} for c in components.values()}
            assert set(actual)=={'R1','R2'}
            assert all(set(p.values())=={'GND','TEST_PWR'} and len(p)==2 for p in actual.values())
            result.update(有效网表=True, 网表逐脚回读=actual, 网表SHA256=hashlib.sha256(raw['data'].encode()).hexdigest(), 网表字节=raw['size'])
        result['完成'] = all(result[k] for k in ('创建','修改保存','独立重开','ERC已调用','有效网表'))
    except Exception as e:
        result.update(完成=False, 失败阶段=phase, 错误=type(e).__name__+': '+str(e)[:4000])
    finally:
        for owned in reversed(sessions):
            try: cli(exe, 'session', 'close', '--session', owned, '--destroy')
            except Exception as e: result.setdefault('关闭异常',[]).append(str(e)[:500])
        if result['独立重开']:
            result['原生SHA256'] = sha(reopen)
            result['原生哈希时点'] = 'ERC与网表导出完成、自建会话关闭后；独立重开副本'
        result['工具SHA256'] = sha(Path(__file__))
        record()
    return result


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--构建', type=Path)
    ap.add_argument('--规范化', type=Path, help='先由官方客户端导入导出，再构建可打开页面的文件夹工程')
    ap.add_argument('--目标', type=Path, help='构建或规范化的目标文件夹；省略时使用交付工程目录')
    ap.add_argument('--检查', action='store_true')
    ap.add_argument('--原生工程', action='store_true')
    ap.add_argument('--检查原生工程', action='store_true')
    ap.add_argument('--客户端', type=Path, default=Path('D:/lceda-pro/lceda-pro.exe'))
    ap.add_argument('--隔离验证', type=Path, help='工作根内的空SQLite模板；仅测试公共API')
    ap.add_argument('--核验记录', type=Path, help='已有板级核验JSON，结果仅写native_validation.工具隔离验证')
    args = ap.parse_args()
    if args.隔离验证:
        assert args.目标 and args.核验记录, '隔离验证须提供新缓存目标及已有核验JSON'
        result=isolated_api_check(args.客户端,args.隔离验证,args.目标,args.核验记录)
        print(json.dumps(result,ensure_ascii=False,indent=2))
        raise SystemExit(0 if result['完成'] else 1)
    if args.构建: print(build(args.构建.resolve(), args.目标))
    if args.规范化: print(json.dumps(canonical_project(args.客户端,args.规范化,args.目标),ensure_ascii=False,indent=2))
    if args.检查: check(args.客户端)
    if args.原生工程: native_project(args.客户端)
    if args.检查原生工程: verify_native(args.客户端)
