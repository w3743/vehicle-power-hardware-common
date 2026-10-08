"""离线生成标准版封装JSON与逐位号绑定；不调用EDA、不布局、不布线。"""
from pathlib import Path
import copy, csv, hashlib, json, math, runpy, sys, uuid, zipfile
sys.dont_write_bytecode = True
BASE = Path(__file__).resolve().parents[2]/'FOC驱动与储能'
LIB = BASE.parent/'公共/库'
DOCS = BASE/'文档'
TOOLS = BASE/'工具'
# Bases removed from the active BOM after the RevF buck deletion. The RevF
# catalog recorded exact MPN, LCSC code, pin/pad-number agreement, and this raw
# response hash; reuse is allowed only when the retained ZIP object still matches.
HISTORICAL_ALIAS_BASES={
    'C0805C104K1RACTU':('C3151888','d1087a2846d4480e512170fc7ea4511febe7c5c93be4ae34a0df11328d92608d'),
    'RT0805BRD07100KL':('C122537','2eda19d3efd6178701d6227cc42349e51eb7dae42a3b2b938174f5610c30376d'),
    'GRM32ER72A225KA35L':('C86054','a0c6eda93564d4bd5bf25ad649c238009b97e7f0f04e893a9a488a51949ddd9c'),
    'CRCW25122R20FKEGHP':('C4168885','34e3a970d8dfac82605993690bbdb5eee81917cb10beb25bd466b776b26a1e24')}
def dump(obj): return json.dumps(obj,ensure_ascii=False,indent=2)

def confirmed_pin_functions(metadata, symbol_pins):
    """Normalize an explicitly confirmed manufacturer pin map without inventing names."""
    if not isinstance(metadata, dict):
        return None
    data=(metadata.get('pin_functions') or metadata.get('functions') or metadata.get('pins')
          or metadata.get('pin_map') or metadata.get('pinmap') or metadata.get('引脚映射'))
    if data is None:
        # Also accept a direct pin-number -> function map, excluding metadata fields.
        data={k:v for k,v in metadata.items() if str(k) in symbol_pins}
    if isinstance(data, list):
        rows=data
        data={str(next((row[k] for k in ('number','pin','pin_number','pad_number','引脚号') if row.get(k) is not None),'')):row
              for row in rows if isinstance(row,dict)}
    if not isinstance(data, dict):
        return None
    result={}
    for number,value in data.items():
        number=str(number)
        if number not in symbol_pins:
            continue
        if isinstance(value, dict):
            value=next((value[k] for k in ('function','name','pin_name','symbol_name','名称','功能') if value.get(k)),None)
        if isinstance(value,str) and value.strip():
            result[number]=value.strip()
    return result if result and set(result)==set(symbol_pins) else None

def pinmap_source(metadata):
    if not isinstance(metadata,dict):
        return ''
    return next((metadata[k] for k in ('source','source_url','datasheet','datasheet_url','manufacturer_source','url','来源','依据')
                 if isinstance(metadata.get(k),str) and metadata[k].strip()),'')

def approved_mechanical_adapters(adapters, library_zip, geometry_zip):
    """Load explicit, unreleased per-MPN mechanical contracts supplied by the caller."""
    if adapters is None:
        return {}
    if not isinstance(adapters,dict):
        raise ValueError('机械适配必须由调用方以明确的MPN映射提供')
    if not adapters:
        return {}
    approved={}
    with zipfile.ZipFile(library_zip) as raw_zip, zipfile.ZipFile(geometry_zip) as geometry_archive:
        geometry_names=set(geometry_archive.namelist())
        for mpn,record in adapters.items():
            if record.get('候选绑定') is not True:
                continue
            if record.get('本批制造放行') is not False or record.get('同版客户端ERC') is not False:
                raise ValueError(f'{mpn}: 候选机械适配必须保留制造/ERC未放行状态')
            manufacturer_source=record.get('来源')
            package_name=record.get('封装')
            evidence=record.get('依据')
            geometry=evidence.get('geometry_source') if isinstance(evidence,dict) else None
            if not all(isinstance(x,str) and x.strip() for x in (manufacturer_source,package_name)):
                raise ValueError(f'{mpn}: 缺少厂家来源或既有封装名')
            if not isinstance(geometry,dict) or geometry.get('method')!='立创完整型号库':
                raise ValueError(f'{mpn}: 缺少明确的真实几何来源')
            code=geometry.get('library_code'); package_uuid=geometry.get('package_uuid')
            geometry_source=geometry.get('source')
            if not all(isinstance(x,str) and x.strip() for x in (code,package_uuid,geometry_source)):
                raise ValueError(f'{mpn}: 几何来源缺少编号、UUID或来源URL')
            if geometry.get('name')!=package_name or geometry_source!=f'https://easyeda.com/api/products/{code}/components':
                raise ValueError(f'{mpn}: 封装名与立创几何来源不一致')
            target_functions=evidence.get('pin_functions')
            geometry_functions=geometry.get('pin_functions')
            mapping=record.get('引脚映射')
            if not all(isinstance(x,dict) and x for x in (target_functions,geometry_functions,mapping)):
                raise ValueError(f'{mpn}: 缺少目标逐针合同或焊盘映射')
            target_functions={str(k):v for k,v in target_functions.items()}
            geometry_functions={str(k):v for k,v in geometry_functions.items()}
            mapping={str(k):str(v) for k,v in mapping.items()}
            if (set(target_functions)!=set(geometry_functions) or set(target_functions)!=set(mapping)
                    or len(set(mapping.values()))!=len(mapping)
                    or any(not isinstance(v,str) or not v.strip() for v in target_functions.values())
                    or any(not isinstance(v,str) or not v.strip() for v in geometry_functions.values())):
                raise ValueError(f'{mpn}: 目标型号、几何来源及映射的针号不完整或重复')
            raw_name=f'元件_{code}.json'
            if raw_name not in raw_zip.namelist():
                raise ValueError(f'{mpn}: 缺少几何来源的原始立创库对象 {raw_name}')
            raw_payload=json.loads(raw_zip.read(raw_name)); raw_result=raw_payload.get('result') or {}
            package_detail=raw_result.get('packageDetail') or {}
            actual_uuid=package_detail.get('uuid')
            if actual_uuid!=package_uuid:
                raise ValueError(f'{mpn}: 原始立创包UUID与审定几何来源不一致')
            raw_package=package_detail.get('dataStr')
            raw_symbol=raw_result.get('dataStr')
            raw_package=json.loads(raw_package) if isinstance(raw_package,str) else raw_package
            raw_symbol=json.loads(raw_symbol) if isinstance(raw_symbol,str) else raw_symbol
            if not isinstance(raw_package,dict) or not isinstance(raw_symbol,dict):
                raise ValueError(f'{mpn}: 原始库缺少可读封装或符号几何')
            geometry_member=f'封装/{package_name}.json'
            if geometry_member not in geometry_names:
                raise ValueError(f'{mpn}: 可导入库缺少已审定几何 {geometry_member}')
            geometry_bytes=geometry_archive.read(geometry_member)
            doc=json.loads(geometry_bytes)
            if (doc.get('head',{}).get('c_para',{}).get('package')!=package_name
                    or doc.get('head',{}).get('uuid') is None):
                raise ValueError(f'{mpn}: 已缓存几何封装名或UUID无效')
            pad_numbers=[shape.split('~')[8] for shape in doc.get('shape',[]) if shape.startswith('PAD~')]
            pads=set(pad_numbers)
            if (not pads or len(pads)!=len(pad_numbers) or pads!=set(mapping.values())
                    or pads!=set(target_functions) or pads!=set(geometry_functions)):
                raise ValueError(f'{mpn}: 真实封装PAD集合与厂家针号映射不完全一致')
            if raw_package.get('shape')!=doc.get('shape'):
                raise ValueError(f'{mpn}: 缓存导入几何与精确立创来源geometry shape不一致')
            source_pin_map={}
            for shape in raw_symbol.get('shape',[]):
                if not shape.startswith('P~'):
                    continue
                fields=shape.split('^^')
                number=fields[4].split('~')[4]
                function=fields[3].split('~')[4]
                if number in source_pin_map:
                    raise ValueError(f'{mpn}: 原始符号引脚号重复 {number}')
                source_pin_map[number]=function
            normalize_function=lambda value:value.strip().upper().replace('N.C','NC')
            if (set(source_pin_map)!=set(geometry_functions)
                    or any(normalize_function(source_pin_map[n])!=normalize_function(geometry_functions[n])
                           for n in geometry_functions)):
                raise ValueError(f'{mpn}: 原始库P引脚功能与几何来源逐针合同不一致')
            approved[mpn]={'name':package_name,'method':'本板已审定机械适配候选；保留未放行状态',
                           'source':manufacturer_source,'pin_functions':target_functions,
                           'pad_mapping':mapping,
                           'geometry_source':geometry,'geometry_sha256':hashlib.sha256(geometry_bytes).hexdigest(),
                           'library_code':code,'package_uuid':package_uuid,
                           'candidate_binding':True,'electrical_release':False,'manufacturing_released':False,
                           '_geometry_doc':doc}
    return approved

def is_approved_mechanical_candidate(part, adapters):
    contract=adapters.get(part.get('mpn'),{})
    return (part.get('installation')=='待设计' and part.get('catalog_lookup') is False
            and part.get('candidate_storage_not_released') is True
            and part.get('manufacturing_released') is False
            and contract.get('candidate_binding') is True
            and contract.get('electrical_release') is False
            and contract.get('manufacturing_released') is False)

def build_footprint(name, spec, template):
    assert 'holes' not in spec,'机械非金属孔须使用nonplated_holes，禁止忽略未支持的holes字段'
    doc=copy.deepcopy(template)
    doc['head']={'docType':'4','editorVersion':'6.5.3','x':4000,'y':3000,
                 'c_para':{'package':name,'pre':'U?','Contributor':'项目封装','来源':spec['source']},
                 'uuid':uuid.uuid5(uuid.NAMESPACE_URL,'foc-footprint/'+name).hex}
    doc['shape']=[]
    def f(v): return format(v,'.7f').rstrip('0').rstrip('.')
    for i,p in enumerate(spec['pads'],1):
        x=4000+p['x_mm']/.254; y=3000+p['y_mm']/.254
        w=p['width_mm']/.254; h=p['height_mm']/.254; hole=p.get('drill_mm',0)/.508
        kind=p.get('shape','ELLIPSE' if hole else 'RECT')
        corners=' '.join(f(v) for v in [x-w/2,y-h/2,x+w/2,y-h/2,x+w/2,y+h/2,x-w/2,y+h/2]) if kind=='RECT' else ''
        if 'polygon_mm' in p:
            assert kind=='POLYGON' and len(p['polygon_mm'])>=3
            assert all(abs(px-p['x_mm'])<=p['width_mm']/2+1e-9 and abs(py-p['y_mm'])<=p['height_mm']/2+1e-9 for px,py in p['polygon_mm'])
            corners=' '.join(f(v) for px,py in p['polygon_mm'] for v in (4000+px/.254,3000+py/.254))
        fields=['PAD',kind,f(x),f(y),f(w),f(h),'11' if hole else '1','',str(p['number']),f(hole),corners,'0',f'gge{i}','0','','Y','0']
        if 'slot_length_mm' in p:
            # Official Std PAD fields 14/15: total slot length and arc-centre
            # endpoints, not a second circular drill or an unplated cutout.
            length=p['slot_length_mm']/.254
            assert hole>0 and length>=2*hole
            delta=(length-2*hole)/2
            fields[13]=f(length)
            fields[14]=' '.join(f(v) for v in (x-delta,y,x+delta,y))
        if 'paste_expansion_mm' in p or 'solder_expansion_mm' in p:
            # Std 6.5 extended PAD: paste expansion, then solder expansion,
            # in 10mil units. Never change existing pads' default rules.
            fields += [f(p['paste_expansion_mm']/.254) if 'paste_expansion_mm' in p else '',
                       f(p['solder_expansion_mm']/.254) if 'solder_expansion_mm' in p else '',
                       f(x)+','+f(y)]
        doc['shape'].append('~'.join(fields))
    for kind,layer in (('solder_mask_regions',7),('paste_mask_regions',5)):
        for i,region in enumerate(spec.get(kind,[]),1):
            if region.get('shape')=='circle':
                x=4000+region['x_mm']/.254;y=3000+region['y_mm']/.254;r=region['diameter_mm']/.508
                assert r>0
                path=f'M {f(x-r)} {f(y)} A {f(r)} {f(r)} 0 1 0 {f(x+r)} {f(y)} A {f(r)} {f(r)} 0 1 0 {f(x-r)} {f(y)} Z'
            else:
                points=region['points_mm'];assert len(points)>=3
                coords=[(4000+x/.254,3000+y/.254) for x,y in points]
                path='M '+' L '.join(f(x)+' '+f(y) for x,y in coords)+' Z'
            doc['shape'].append('~'.join(['SOLIDREGION',str(layer),'',path,'solid',f'gge_{kind}_{i}','','','','0']))
    for j,line in enumerate(spec.get('outline_lines',[]),len(spec['pads'])+1):
        coords=[4000+line['start'][0]/.254,3000+line['start'][1]/.254,
                4000+line['end'][0]/.254,3000+line['end'][1]/.254]
        doc['shape'].append('~'.join(['TRACK',f(line.get('width_mm',.1)/.254),str(line['layer']),'',
                                    ' '.join(f(v) for v in coords),f'gge{j}','0']))
    for i,hole in enumerate(spec.get('nonplated_holes',[]),1):
        assert hole['diameter_mm']>0
        doc['shape'].append('~'.join(['HOLE',f(4000+hole['x_mm']/.254),f(3000+hole['y_mm']/.254),
                                    f(hole['diameter_mm']/.508),f'ggeNPTH{i}','0']))
    # 文档层装配边界来自明确尺寸/原始库；不把它声称为EDA已配置的自动DRC庭院。
    doc.pop('BBox',None)
    return doc

def main():
    parts=runpy.run_path(str(BASE/'设计数据.py'))['PARTS']
    catalog=json.loads((LIB/'嘉立创元件匹配.json').read_text(encoding='utf8'))
    assert catalog['设计源SHA256']==hashlib.sha256((BASE/'设计数据.py').read_bytes()).hexdigest()
    rows={r['原型号']:r for r in catalog['型号结果']}
    libraries={}; sources={}; bindings=[]; pad_rows=[]; package_names={}; shared_library_names=set()
    with zipfile.ZipFile(LIB/'嘉立创库数据.zip') as z:
        raw_bytes={name:z.read(name) for name in z.namelist()}
        raw={name:json.loads(blob)['result'] for name,blob in raw_bytes.items()}
        for row in rows.values():
            lib=row.get('库数据',{}); selected=row.get('选定匹配')
            if not selected or not lib.get('型号编号一致'): continue
            code=selected['立创编号']; a=raw.get(f'元件_{code}.json')
            if not a or not lib.get('封装焊盘'): continue
            assert hashlib.sha256(z.read(f'元件_{code}.json')).hexdigest()==lib['原始数据SHA256']
            doc=a['packageDetail']['dataStr']
            if isinstance(doc,str):doc=json.loads(doc)
            package_id=a['packageDetail']['uuid']
            signature=hashlib.sha256(dump(doc['shape']).encode()).hexdigest()
            if package_id in package_names:
                name,prior_signature=package_names[package_id]
                assert signature==prior_signature,(package_id,'同UUID返回不同几何，不得静默合并')
            else:
                name='立创封装_'+code
                doc=copy.deepcopy(doc); doc['head']['c_para']['package']=name
                doc['head']['uuid']=uuid.uuid5(uuid.NAMESPACE_URL,'foc-library/'+package_id).hex
                libraries[name]=doc;package_names[package_id]=(name,signature)
            sources[row['原型号']]={'name':name,'method':'立创完整型号库','source':lib['URL'],
                                   'pin_functions':lib.get('符号引脚',{}),'library_code':code,'package_uuid':package_id}
    # A removed alias base may still be present in the retained raw archive.
    # Verify it against the old, exact-model RevF catalog proof before reusing it.
    for mpn,(code,expected_sha) in HISTORICAL_ALIAS_BASES.items():
        if mpn in sources:continue
        filename=f'元件_{code}.json'; blob=raw_bytes.get(filename)
        if not blob:continue
        actual_sha=hashlib.sha256(blob).hexdigest()
        assert actual_sha==expected_sha,(mpn,code,'缓存原始响应与RevF目录SHA256证明不一致')
        payload=json.loads(blob); assert payload.get('success') is True
        a=payload['result']; sd=a.get('dataStr') or {}; pd=(a.get('packageDetail') or {}).get('dataStr') or {}
        if isinstance(sd,str):sd=json.loads(sd)
        if isinstance(pd,str):pd=json.loads(pd)
        para=(sd.get('head') or {}).get('c_para') or {}
        assert para.get('Manufacturer Part','').casefold()==mpn.casefold(),(mpn,para.get('Manufacturer Part'))
        assert str(para.get('Supplier Part',''))==code,(mpn,code,para.get('Supplier Part'))
        pins={}
        for shape in sd.get('shape',[]):
            if shape.startswith('P~'):
                fields=shape.split('^^')
                number=fields[4].split('~')[4]; name=fields[3].split('~')[4]
                pins[number]=name
        pads={shape.split('~')[8] for shape in pd.get('shape',[]) if shape.startswith('PAD~')}
        assert pins and set(pins)==pads,(mpn,sorted(pins),sorted(pads))
        package_id=(a.get('packageDetail') or {}).get('uuid'); assert package_id
        signature=hashlib.sha256(dump(pd['shape']).encode()).hexdigest()
        if package_id in package_names:
            name,prior_signature=package_names[package_id]
            assert signature==prior_signature,(package_id,'历史别名库与现有UUID几何不一致')
        else:
            name='立创封装_'+code
            pd=copy.deepcopy(pd); pd['head']['c_para']['package']=name
            pd['head']['uuid']=uuid.uuid5(uuid.NAMESPACE_URL,'foc-library/'+package_id).hex
            libraries[name]=pd; package_names[package_id]=(name,signature)
        sources[mpn]={'name':name,'method':'RevF已核验完整型号库缓存；原始响应哈希复核',
                      'source':f'https://easyeda.com/api/products/{code}/components',
                      'pin_functions':pins,'library_code':code,'package_uuid':package_id,
                      '原始数据SHA256':actual_sha,
                      '历史依据':'改动前-RevF.zip内精确型号、立创编号、型号及引脚/焊盘编号一致记录'}
    template=next(iter(libraries.values()),None)
    # 同系列、同机械尺寸的无极性阻容可共用焊盘；不替换采购型号。
    aliases={
        **{r['原型号']:'C0805C104K1RACTU' for r in rows.values() if r['原型号'].startswith('C0805')},
        **{r['原型号']:'RT0805BRD07100KL' for r in rows.values() if r['原型号'].startswith('RT0805BRD07')},
        **{r['原型号']:'RC0805FR-0710KL' for r in rows.values() if r['原型号'].startswith('RC0805FR-07')},
        'GRM32ER71A226ME20L':'GRM32ER72A225KA35L',
        'RT0805BRD0732K4L':'RT0805BRD07100KL',
        'CRCW251210R0FKEGHP':'CRCW25122R20FKEGHP'}
    for mpn,base in aliases.items():
        if mpn in sources:continue
        if base not in sources:
            raise RuntimeError(f'{mpn}: 缺少有身份和哈希依据的封装基础型号 {base}')
        source=copy.deepcopy(sources[base]); source.update(method='同系列同尺寸共用焊盘',shared_from=base)
        sources[mpn]=source
    # C2158951的二维焊盘可用，但原始库误挂4.1mm高的E壳3D；实际器件为D壳。
    # 原始下载证据不改；可导入库禁用该错误模型，不能让装配检查继承错误高度。
    if 'T598D476M025ATE060' in sources:
        selected=sources['T598D476M025ATE060']
        doc=libraries[selected['name']]
        for key in list(doc['head'].get('c_para',{})):
            if '3d' in key.lower():del doc['head']['c_para'][key]
        doc['shape']=[shape for shape in doc['shape'] if not shape.startswith('SVGNODE~')]
        selected['notes']='KEMET T59X第8/24页：D壳7.3×4.3×2.8±0.3mm，条纹端为正；库1正2负已核。原库误挂E壳4.1mm的3D，已从可导入库排除；保留原始下载证据，不作3D装配验收。'
    # C478075仅提供封装，符号为空；按TI数据手册第3页确认引脚，不能把空符号当完整元件。
    if 'TLV3202AIDGKR' in sources:
        sources['TLV3202AIDGKR'].update(method='立创封装加厂家引脚表',
          pin_functions={'1':'1OUT','2':'1IN-','3':'1IN+','4':'GND','5':'2IN+','6':'2IN-','7':'2OUT','8':'VCC'},
          pin_source='https://www.ti.com/lit/ds/symlink/tlv3202.pdf#page=3')
    supplemental=LIB/'封装补充依据.json'
    if supplemental.exists():
        supplemental_data=json.loads(supplemental.read_text(encoding='utf8'))
        for mpn,spec in supplemental_data['footprints'].items():
            if template is None:
                raise RuntimeError('无法用补充封装生成标准JSON：缺少可复用的标准库模板')
            name=spec['name']; libraries[name]=build_footprint(name,spec,template)
            if spec.get('shared_library') is True:
                shared_library_names.add(name)
            sources[mpn]={'name':name,'method':spec['method'],'source':spec['source'],
                          'pin_functions':{str(p['number']):p.get('function','无极性') for p in spec['pads']},
                          'notes':spec.get('notes','')}
        rdy_adapters=approved_mechanical_adapters(
            supplemental_data.get('本板RDY型号适配',{}),
            LIB/'嘉立创库数据.zip',LIB/'可导入封装库.zip')
        for mpn,adapter in rdy_adapters.items():
            doc=adapter.pop('_geometry_doc')
            name=adapter['name']
            if name in libraries:
                assert dump(libraries[name]['shape'])==dump(doc['shape']),(
                    mpn,name,'已存在几何与明确适配包的PAD/外形数据冲突')
            else:
                libraries[name]=doc
            existing_source=sources.get(mpn)
            if existing_source and existing_source.get('name')!=name:
                raise ValueError(f'{mpn}: 目录完整型号包与审定机械候选封装冲突')
            sources[mpn]=adapter
    for p in parts:
        ref=p['ref']; mapping={pin:pin for pin in p['pins']}
        installation=p.get('installation','板上')
        if installation not in {'板上','板外','待设计'}:
            raise ValueError(f'{ref}: 未知安装状态 {installation!r}')
        b={'位号':ref,'型号':p['mpn'],'安装':installation,'封装':'','引脚映射':mapping,
           '封装状态':'待核验' if installation=='板上' else ('candidate_storage_not_released' if installation=='待设计' else '外置器件')}
        if installation=='待设计':
            b['焊盘映射']={}
            b['封装未确认']=True
        elif installation=='板外' and p.get('catalog_lookup') is False:
            b['封装状态']='external/hardware_not_released'
        for source_key,target_key in [('manufacturer','制造商'),('quantity','数量'),('assembly','装配'),
                                      ('source','来源'),('pinmap_metadata','厂家引脚依据'),
                                      ('catalog_lookup','查询嘉立创目录')]:
            if p.get(source_key) is not None:
                b[target_key]=p[source_key]
        metadata=p.get('pinmap_metadata')
        functions=confirmed_pin_functions(metadata,set(mapping.values())) if installation in {'板外','待设计'} else None
        if functions:
            b['依据']={'method':'厂家引脚资料（端子符号；不含PCB封装）',
                       'source':pinmap_source(metadata) or p.get('source',''),
                       'pin_functions':functions,'pinmap_metadata':metadata,
                       'footprint_pending_review':True}
        elif installation in {'板外','待设计'} and metadata:
            b['引脚功能状态']='厂家pinmap_metadata不完整或格式未识别；符号仅显示引脚编号'
        candidate = installation=='待设计' and functions and metadata.get('assignment_verified') is True
        mechanical_adapter=sources.get(p['mpn'],{})
        mechanical_candidate=is_approved_mechanical_candidate(p,sources)
        if mechanical_candidate:
            mapping=copy.deepcopy(mechanical_adapter['pad_mapping'])
            if set(mapping)!=set(p['pins']):
                raise ValueError(f'{ref}: 符号引脚集与审定机械映射不完全一致')
        if (((installation=='板上' and p.get('catalog_lookup') is not False) or candidate or mechanical_candidate)
                and p['mpn'] in sources):
            s=copy.deepcopy(sources[p['mpn']]); name=s['name']; doc=libraries[name]
            pads={t.split('~')[8] for t in doc['shape'] if t.startswith('PAD~')}
            if p['mpn']=='IPT015N10N5ATMA1':
                assert s['pin_functions']=={'1':'G','3':'D','2':'S'}
                assert len({p['pins'][str(i)] for i in range(2,9)})==1
                mapping={'1':'1',**{str(i):'2' for i in range(2,9)},'9':'3'}
            assert set(mapping.values())==pads,(ref,set(mapping.values()),pads)
            b.update(封装=name,引脚映射=mapping,依据=s,封装状态='已有依据待PCB审核',
                库文件='封装/'+name+'.json',封装SHA256=hashlib.sha256(dump(doc).encode()).hexdigest())
            if mechanical_candidate:
                b.update(封装状态='真实候选封装；电气及制造未放行',封装未确认=False,
                         电气放行=False,制造放行=False,焊盘映射=mapping,
                         目录型号命中=False,候选合同='本板RDY型号适配；仅机械/针号候选')
            elif candidate:
                s['库符号引脚']=s['pin_functions']
                if p['mpn']!='IPT015N10N5ATMA1':s['pin_functions']=functions
                s['厂家引脚依据']=metadata
                b.update(封装状态='真实候选封装；电路及制造未放行',封装未确认=False,制造放行=False)
                b['焊盘映射']=mapping
        bindings.append(b)
    bound_used={b['封装'] for b in bindings if b['封装']}
    export_used=bound_used | shared_library_names
    with zipfile.ZipFile(LIB/'可导入封装库.zip','w',zipfile.ZIP_DEFLATED) as z:
        for name in sorted(export_used):
            doc=libraries[name]; z.writestr('封装/'+name+'.json',dump(doc))
            ox=float(doc['head']['x']); oy=float(doc['head']['y'])
            for shape in doc['shape']:
                if not shape.startswith('PAD~'):continue
                f=shape.split('~')
                x,y,w,h,hole,rot=map(float,[f[2],f[3],f[4],f[5],f[9],f[11]])
                assert all(math.isfinite(v) for v in (x,y,w,h,hole,rot)) and min(w,h)>0
                assert f[6] in ('1','2','11')
                pad_rows.append([name,f[8],f[1],round((x-ox)*.254,5),round((y-oy)*.254,5),
                    round(w*.254,5),round(h*.254,5),round(hole*.508,5),rot,f[6]])
        z.writestr('使用说明.md','标准版封装JSON，可供人工按嘉立创专业版“导入标准版”路径导入。\n网表封装名与各JSON的head.c_para.package一致。未执行编辑器导入、ERC、DRC或制造验收。\n原始立创数据保留在嘉立创库数据.zip；自建封装依据见封装补充依据.json。\n按完整型号采购，共用封装不等于替代器件。\nhttps://prodocs.lceda.cn/cn/import-export/import-lceda/\n')
    result={'设计源SHA256':catalog['设计源SHA256'],
            '板上器件数':sum(b['安装']=='板上' for b in bindings),
            '板外器件数':sum(b['安装']=='板外' for b in bindings),
            '待设计器件数':sum(b['安装']=='待设计' for b in bindings),
            '已绑定板上位号数':sum(b['安装']=='板上' and bool(b['封装']) for b in bindings),
            '待补板上位号':[b['位号'] for b in bindings if b['安装']=='板上' and not b['封装']],
            '待设计位号':[b['位号'] for b in bindings if b['安装']=='待设计'],
            '已绑定候选位号数':sum(b['安装']=='待设计' and bool(b['封装']) for b in bindings),
            '候选待补封装位号':[b['位号'] for b in bindings if b['安装']=='待设计' and not b['封装']],
            '唯一封装文件数':len(bound_used),'共享未绑定封装数':len(shared_library_names-bound_used),
            'ZIP导出封装文件数':len(export_used),
            '核验边界':'验证结构、编号集合及网表连接；封装工艺、安装和软件导入仍需人类终审。',
            '位号绑定':bindings}
    (LIB/'封装绑定.json').write_text(dump(result),encoding='utf8')
    with (LIB/'封装焊盘尺寸.csv').open('w',encoding='utf-8-sig',newline='') as f:
        w=csv.writer(f); w.writerow(['封装','焊盘','形状','中心X毫米','中心Y毫米','宽毫米','高毫米','孔径毫米','角度','标准版层编号']);w.writerows(pad_rows)
    print(dump({k:v for k,v in result.items() if k!='位号绑定'}))

if __name__=='__main__':
    sys.stdout.reconfigure(encoding='utf8');main()
