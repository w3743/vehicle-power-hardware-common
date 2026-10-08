"""离线回读官方交换记录；由调用板显式传入同版源与候选库合同。"""
import collections, hashlib, json, zipfile

def current_document_records(text):
    """Resolve saved records and deletion tombstones in each document's scope."""
    documents=[];uuids=set();current=None;tombstones=0;replacements=0
    for number,line in enumerate(text.split('\n'),1):
        if not line.strip():continue
        head,body=line.strip().split('||',1);a=json.loads(head);body=body.removesuffix('|')
        if a['type']=='DOCHEAD':
            assert body,('删除文档记录需要单独解析',number)
            b=json.loads(body);assert b['uuid'] not in uuids,('重复文档头',b['uuid'])
            uuids.add(b['uuid']);current={'head':(a,b),'rows':{}};documents.append(current);continue
        assert current is not None and a.get('id') is not None,('无文档或无图元ID',number,a)
        if not body:
            tombstones+=1;current['rows'].pop(a['id'],None);continue
        b=json.loads(body)
        if a['id'] in current['rows']:
            old=current['rows'][a['id']][0]
            assert a.get('ticket',0)>=old.get('ticket',0),('更新记录顺序不明',number,a)
            replacements+=1
        current['rows'][a['id']]=(a,b)
    return [[d['head'],*d['rows'].values()] for d in documents],{'deletion_tombstones':tombstones,'replaced_records':replacements,'scope':'逐文档图元ID的官方保存后有效记录'}

def verify_exchange(path, expected, expected_nc, scope_refs=None, strict_full_BOM=False, *, parts, hardware, cap_specs=None, mechanical_refs=(), mechanical_models=None, mechanical_library_sha256=None):
    PARTS = parts
    HW = hardware
    CAP_SPECS = cap_specs or {}
    MECHANICAL_REFS = mechanical_refs
    MECHANICAL_MODELS = mechanical_models or {}
    MECHANICAL_LIBRARY_SHA256 = mechanical_library_sha256
    """按官方转换记录读真实SYMBOL PIN坐标及导线，不按源数据回显PASS。"""
    with zipfile.ZipFile(path) as z:
        assert z.testzip() is None
        records=z.read(next(n for n in z.namelist() if n.endswith('.epru'))).decode('utf8')
    docs,serialization=current_document_records(records)
    normalized_coordinates=0
    def coordinate(value):
        nonlocal normalized_coordinates
        rounded=round(value,6)
        assert abs(rounded-value)<=0.000001,('超出坐标数值容差',value)
        normalized_coordinates+=rounded!=value
        return rounded
    symbols={doc[0][1]['uuid']:doc for doc in docs if doc[0][1]['docType']=='SYMBOL'}
    actual={};actual_nc=set();actual_refs=set();geometric_points=0;bom_refs=[]
    parts_byref={p['ref']:p for p in PARTS}
    devices={doc[0][1]['uuid']:doc for doc in docs if doc[0][1]['docType']=='DEVICE'}
    footprints={doc[0][1]['uuid']:doc for doc in docs if doc[0][1]['docType']=='FOOTPRINT'}
    mechanical=[];footprint_readback={};full_bindings=[];full_BOM=[]
    for doc in [d for d in docs if d[0][1]['docType']=='SCH_PAGE']:
        attrs=collections.defaultdict(dict)
        for a,b in doc:
            if a['type']=='ATTR':attrs[b['parentId']][b['key']]=b['value']
        segments=[];ncs=[]
        for a,b in doc:
            if a['type']=='LINE':
                segments.append((*[coordinate(b[k]) for k in ('startX','startY','endX','endY')],attrs[b['lineGroup']]['NET']))
            if a['type']=='ATTR' and b['key']=='NO_CONNECT' and b['value']=='yes':
                ncs.append((coordinate(b['x']),coordinate(b['y'])))
        points={}
        for a,b in doc:
            if a['type']!='COMPONENT':continue
            b=dict(b,x=coordinate(b['x']),y=coordinate(b['y']))
            at=attrs[a['id']]
            if 'Designator' not in at:
                # 官方原生导出包含真实网络端口/电源标识，不把它们计入BOM元件。
                device=devices.get(at.get('Device'),[])
                meta=next((db for da,db in device if da['type']=='META'),{})
                assert meta.get('title','').startswith(('Netport-','Ground-','Power-')),('未知非设计器件',at)
                net=at.get('Global Net Name') or at.get('Name')
                assert net and any(n==net and ((y1==y2==b['y'] and min(x1,x2)<=b['x']<=max(x1,x2)) or
                    (x1==x2==b['x'] and min(y1,y2)<=b['y']<=max(y1,y2))) for x1,y1,x2,y2,n in segments),('原生标识未接实际同网导线',net,b)
                continue
            ref=at['Designator'];assert ref not in actual_refs
            if scope_refs is not None and ref not in scope_refs:continue
            actual_refs.add(ref)
            part=parts_byref[ref]
            if 'cap_contract' in part:
                spec=CAP_SPECS[part['model']]
                want={'Manufacturer Part':part['model'],'Manufacturer':spec['manufacturer'],
                      'Value':str(spec['nominal_uF'])+'uF',
                      'Tolerance':str(spec['initial_tolerance']*100)+'%',
                      'Voltage':str(spec['rated_V'])+'V','Dielectric':spec['dielectric'],
                      'Case':spec['case_candidate'],
                      'Cap_Contract':json.dumps(part['cap_contract'],ensure_ascii=True,separators=(',',':'))}
                # Official save may decode JSON Unicode escapes without changing
                # the contract. Compare that one JSON attribute canonically;
                # retain exact values/types, array order and every contract key.
                def equal_attribute(key,actual,expected):
                    if key!='Cap_Contract':return actual==expected
                    if not isinstance(actual,str):return False
                    try:
                        canonical=lambda s:json.dumps(json.loads(s),ensure_ascii=True,sort_keys=True,separators=(',',':'))
                        return canonical(actual)==canonical(expected)
                    except (TypeError,ValueError):return False
                assert all(equal_attribute(k,at.get(k),v) for k,v in want.items()),(ref,'BOM/电容合同交换属性丢失',want,at)
                bom_refs.append(ref)
            if strict_full_BOM:
                # 同版全部元件的实际属性回读，不将源字典当BOM证据。
                value=part.get('value',part['model'])
                manufacturer=part.get('manufacturer','待确认')
                if 'cap_contract' in part:
                    value=str(CAP_SPECS[part['model']]['nominal_uF'])+'uF'
                    manufacturer=CAP_SPECS[part['model']]['manufacturer']
                if 'mechanical_candidate' in part:value=part['mechanical_candidate']['value']
                # 原生客户端把明确未选MPN的空串序列化为null；只规范空值，不以显示名称代替型号。
                actual_mpn=at.get('Manufacturer Part') or ''
                assert actual_mpn==part['model'] and at['Value']==value and at['Manufacturer']==manufacturer,(ref,at)
                assert at['Assembly']==part.get('assembly','候选装配禁止生产')
                if 'onboard' in part:
                    assert isinstance(part['onboard'],bool)
                    placement='yes' if part['onboard'] else 'no'
                    assert at.get('Convert to PCB')==placement,(ref,'正式PCB纳入与作者物理边界不符',placement,at.get('Convert to PCB'))
                    assert at.get('PCB_Placement')==placement,(ref,'BOM与正式PCB纳入不符',placement,at.get('PCB_Placement'))
                for source_key,attr_key in [('fitted','Fitted'),('procurement_quantity','Procurement_Quantity'),('assembly_domain','Assembly_Domain')]:
                    if source_key in part:
                        want=str(part[source_key]).lower() if isinstance(part[source_key],bool) else str(part[source_key])
                        assert at.get(attr_key)==want,(ref,attr_key,'装配合同属性未保存',want,at.get(attr_key))
                if 'runtime_assembly_option' in part:
                    assert at.get('Runtime_Assembly_Option')==part['runtime_assembly_option'],ref
                    assert json.loads(at['Assembly_Profiles'])==part['assembly_profiles'],ref
                    assert at.get('Default_Quantity')==str(0 if part.get('fitted') is False else part['quantity']),ref
                full_BOM.append(dict(ref=ref,model=actual_mpn,value=at['Value'],manufacturer=at['Manufacturer'],assembly=at['Assembly'],status=at['Status']))
                candidate=part.get('approved_binding')
                if candidate:
                    meta=next(db for da,db in devices[at['Device']] if da['type']=='META')
                    fp=meta['attributes']['Footprint'];assert fp in footprints,(ref,'Device.Footprint missing')
                    fpdoc=footprints[fp];fpmeta=next(fb for fa,fb in fpdoc if fa['type']=='META')
                    assert fpmeta['title']==candidate['footprint']
                    with zipfile.ZipFile(HW/'公共/库/可导入封装库.zip') as library:raw=library.read(candidate['member'])
                    assert hashlib.sha256(raw).hexdigest()==candidate['sha256']
                    std=json.loads(raw);ox=float(std['head']['x']);oy=float(std['head']['y'])
                    stdpads=[q.split('~') for q in std['shape'] if q.startswith('PAD~')]
                    pads=[fb for fa,fb in fpdoc if fa['type']=='PAD']
                    mapping=candidate['physical_pin_to_pad']
                    assert set(mapping)==set(part['pins']),(ref,'源逻辑端子缺映射')
                    groups=collections.defaultdict(list)
                    for logical,physical in mapping.items():groups[physical].append(logical)
                    assert all(len({part['pins'][n] for n in logical})==1 for logical in groups.values()),(ref,'一块铜的逻辑端子异网')
                    assert len(pads)==len(stdpads) and {q['num'] for q in pads}=={q[8] for q in stdpads}==set(mapping.values())
                    # 原厂/共享批准多铜片可同号；按号和中心匹配每个铜片，不因set去重漏检。
                    remaining=list(pads)
                    for sp in stdpads:
                        want=(sp[8],(float(sp[2])-ox)*10,-(float(sp[3])-oy)*10)
                        matching=[q for q in remaining if q['num']==want[0] and abs(q['centerX']-want[1])<1e-5 and abs(q['centerY']-want[2])<1e-5]
                        assert len(matching)==1,(ref,'pad center/count mismatch',want)
                        pad=matching[0]
                        final_batch=(part['model'] in {'BSC050N10NS5ATMA1','NX3008PBK,215','PBSS4240T,215','MCP4921-E/SN','MCP3201T-BI/SN','LM2662MX/NOPB','BZT52H-C12','MMBT5551LT1G','LTC6995IS6-1#TRPBF','AQZ205','1714971','GRM32ER61C476KE15L','SiS892ADN-T1-GE3','TPSM65620SVCGR','43045-0800','43045-1200','ABM8G-12.000MHZ-8-D2X-T','SN74LXC1T45DBVR','CGA6N3X7R2A225K230AB','CGA3E1X7R1C105K080AC','WSL2512R0100FEA','WSL25128L000FEA'} or part['model'].startswith('KLKD') and part['model'].endswith('.HXR'))
                        if final_batch or part['model'] in {'PSMN1R1-100CSE','MPLAD30KP43AE3','BCX53-16,115','BAS116,215','WSR58L000FEA','WSR5R0200FEA','WSR5R0500FEA','C0805C822J1GACTU','C2220C334J1GACTU','RC0805FR-0747RL','RC0805FR-073R3L','NVMFS6B25NLT1G','NVMFS6B14NLT1G','NVMFS6H800NLT1G','39-30-1020','1777545'}:
                            if sp[1]=='POLYGON':
                                assert pad['defaultPad']['padType']=='POLYGON'
                                path=pad['defaultPad']['path'];assert all(not isinstance(v,str) or v=='L' for v in path)
                                nums=[v for v in path if not isinstance(v,str)];assert len(nums)%2==0
                                got={(round(x,3),round(y,3)) for x,y in zip(nums[::2],nums[1::2])}
                                stdpoints=list(map(float,sp[10].split()))
                                needed={(round((x-ox)*10,3),round(-(y-oy)*10,3)) for x,y in zip(stdpoints[::2],stdpoints[1::2])}
                                assert got==needed,(ref,'连续polygon实际顶点变形',got,needed)
                            else:
                                assert all(abs(pad['defaultPad'][k]-float(sp[i])*10)<1e-4 for k,i in (('width',4),('height',5))),(ref,'新批铜面宽高改变')
                            diameter=float(sp[9])*20
                            slot=float(sp[13] or 0)*10
                            if slot:
                                assert pad['hole']['holeType']=='SLOT' and pad['relativeAngle']==0
                                assert abs(pad['hole']['width']-slot)<1e-4 and abs(pad['hole']['height']-diameter)<1e-4,(ref,'HXR长圆槽未保持')
                            else:
                                assert all(abs(pad['hole'][k]-diameter)<1e-4 for k in ('width','height')),(ref,'孔径/无孔未保持')
                        remaining.remove(pad)
                    assert not remaining and not any('MODEL' in fa['type'] for fa,fb in fpdoc)
                    if part['model']=='BSC050N10NS5ATMA1':
                        assert len([fb for fa,fb in fpdoc if fa['type']=='FILL' and fb.get('layerId')==7])==12,(ref,'12独立顶锡膏窗口未保持')
                        assert all(pad['topPasteExpansion']==-1000 and abs(pad['topSolderExpansion']-.05/.0254)<1e-5 for pad in pads),(ref,'默认锡膏关闭及工程阻焊边界未保持')
                    stdholes=[q.split('~') for q in std['shape'] if q.startswith('HOLE~')]
                    # Official TPCB_LayersOfFill remarks: MULTI FILL is a slot
                    # region, not copper. The official converter maps HOLE to
                    # an unnetted circular MULTI FILL with the exact radius.
                    native_holes=[fb for fa,fb in fpdoc if fa['type']=='FILL' and fb.get('layerId')==12]
                    if stdholes:
                        assert len(native_holes)==len(stdholes),(ref,'原生NPTH孔数量不符')
                        remaining_holes=list(native_holes)
                        for hole in stdholes:
                            want=((float(hole[1])-ox)*10,-(float(hole[2])-oy)*10,float(hole[3])*10)
                            matching=[h for h in remaining_holes if len(h['path'])==1 and h['path'][0][0]=='CIRCLE'
                                and all(abs(actual-required)<1e-4 for actual,required in zip(h['path'][0][1:],want))
                                and h.get('netName','')=='']
                            assert len(matching)==1,(ref,'原生非金属孔中心/半径/无网络不符',want)
                            remaining_holes.remove(matching[0])
                    full_bindings.append(dict(ref=ref,model=part['model'],footprint=fpmeta['title'],
                        member=candidate['member'],member_sha256=candidate['sha256'],copper_records=len(pads),
                        physical_pin_to_pad=candidate['physical_pin_to_pad'],
                        nonplated_holes_verified=len(stdholes),
                        nonplated_hole_format='unnetted circular MULTI FILL (official slot region)' if stdholes else None,
                        status='PASS_EXACT_SHARED_CANDIDATE_DEVICE_LINK_PAD_NUMBER_CENTER_COUNT_NO_3D',
                        full_manufacturer_landpattern_or_process_verified=False))
            assert b['rotation']==0 and not b['isMirror']
            sym=symbols[at['Symbol']];pin_attrs=collections.defaultdict(dict)
            for sa,sb in sym:
                if sa['type']=='ATTR':pin_attrs[sb['parentId']][sb['key']]=sb['value']
            if ref in MECHANICAL_REFS:
                candidate=MECHANICAL_MODELS[part['model']]
                assert at['Manufacturer Part']==part['model'] and at['Value']==candidate['value']
                types={pa['Pin Number']:pa['Pin Type'] for pa in pin_attrs.values() if 'Pin Number' in pa}
                assert types=={'1':'Undefined','2':'Undefined'},(ref,types)
                meta=next(db for da,db in devices[at['Device']] if da['type']=='META')
                fp=meta['attributes']['Footprint'];assert fp in footprints,(ref,'未形成实际Device.Footprint绑定')
                fpdoc=footprints[fp];fpmeta=next(fb for fa,fb in fpdoc if fa['type']=='META')
                assert fpmeta['title']==candidate['footprint'],(ref,fpmeta)
                if fp not in footprint_readback:
                    with zipfile.ZipFile(HW/'公共/库/可导入封装库.zip') as library:
                        raw=library.read(candidate['member'])
                    assert hashlib.sha256(raw).hexdigest()==candidate['sha256']
                    std=json.loads(raw);ox=float(std['head']['x']);oy=float(std['head']['y'])
                    stdpads={s.split('~')[8]:s.split('~') for s in std['shape'] if s.startswith('PAD~')}
                    pads={fb['num']:fb for fa,fb in fpdoc if fa['type']=='PAD'}
                    assert set(pads)==set(stdpads)=={'1','2'}
                    for num,pad in pads.items():
                        sp=stdpads[num]
                        want={'centerX':(float(sp[2])-ox)*10,'centerY':-(float(sp[3])-oy)*10,
                              'width':float(sp[4])*10,'height':float(sp[5])*10}
                        got={k:pad[k] if k.startswith('center') else pad['defaultPad'][k] for k in want}
                        assert all(abs(got[k]-v)<0.00001 for k,v in want.items()),(fp,num,want,got)
                        assert pad['layerId']==1 and pad['defaultPad']['padType']=='RECT'
                        assert pad['hole']['width']==pad['hole']['height']==0
                    assert not any('MODEL' in fa['type'] for fa,fb in fpdoc),'本轮交换不得带入3D'
                    footprint_readback[fp]=dict(title=fpmeta['title'],source_member=candidate['member'],
                        source_member_sha256=candidate['sha256'],pin_to_pad={'1':'1','2':'2'},
                        geometry_status='PASS_TWO_COPPER_PADS_MATCH_APPROVED_CANDIDATE',
                        coordinate_basis='实际Pro记录坐标/尺寸为mil；由标准记录×10独立比对，mm=mil×0.0254',
                        pads=[dict(number=n,center_mm=[p['centerX']*0.0254,p['centerY']*0.0254],
                            size_mm=[p['defaultPad']['width']*0.0254,p['defaultPad']['height']*0.0254],
                            layer=p['layerId'],hole_mm=[0,0],
                            pad_offset_mm=[p['padOffsetX']*0.0254,p['padOffsetY']*0.0254],
                            solder_expansion_mil=[p['topSolderExpansion'],p['bottomSolderExpansion']],
                            paste_expansion_mil=[p['topPasteExpansion'],p['bottomPasteExpansion']])
                            for n,p in sorted(pads.items())],
                        models_3D=0,qualification=candidate['qualification'],
                        process_status=('RT负扩展关闭默认锡膏窗口，两个独立顶锡膏区域保留；未证专用哨兵约定，不改0；钢网/焊接工艺仍候选'
                            if part['model']=='RT0805BRD0768KL' else '厂家密度B推荐铜焊盘候选；钢网/焊接工艺仍未核'))
                mechanical.append(dict(ref=ref,model=part['model'],value=at['Value'],symbol=at['Symbol'],device=at['Device'],
                    footprint=fp,footprint_title=fpmeta['title'],pin_types=types,nets=part['pins']))
            for sa,sb in sym:
                if sa['type']!='PIN':continue
                num=pin_attrs[sa['id']]['Pin Number'];key=(ref,num)
                x=coordinate(b['x']+sb['x']);y=coordinate(b['y']+sb['y'])
                assert (x,y) not in points,(ref,num,'pin overlap')
                points[(x,y)]=key;geometric_points+=1
                nets={net for x1,y1,x2,y2,net in segments
                      if ((y==y1==y2 and min(x1,x2)<=x<=max(x1,x2)) or
                          (x==x1==x2 and min(y1,y2)<=y<=max(y1,y2)))}
                if (x,y) in ncs:
                    assert not nets,(key,'NC有导线');actual_nc.add(key)
                else:
                    assert len(nets)==1,(key,x,y,nets)
                    actual[key]=next(iter(nets))
        if scope_refs is None:assert set(points).issuperset(ncs),'NC未落真实引脚'
    if scope_refs is not None:
        expected={k:v for k,v in expected.items() if k[0] in scope_refs}
        expected_nc={k for k in expected_nc if k[0] in scope_refs}
    assert actual==expected,dict(missing=set(expected)-set(actual),extra=set(actual)-set(expected),
                                 wrong={str(k):[v,actual.get(k)] for k,v in expected.items() if actual.get(k)!=v})
    assert actual_nc==expected_nc,dict(missing=expected_nc-actual_nc,extra=actual_nc-expected_nc)
    assert actual_refs==(scope_refs if scope_refs is not None else {p['ref'] for p in PARTS})
    if scope_refs is not None:
        for item in mechanical:
            item['nets']={num:net for (ref,num),net in actual.items() if ref==item['ref']}
        return dict(mechanical_binding_readback=dict(status='PASS_EXCHANGE_FOUR_REFS_ONLY',refs=mechanical,
            connected_pins=len(actual),pin_type='Undefined（保留原类型）；非IN',
            footprints=footprint_readback,
            type_basis=dict(format='EasyEDA Std P~show~electrical；共享生成函数标准码0',
                explicit_local_enum='硬件/公共/工具/生成可编辑原理图.py:59-62：Undefined=0，IN=1；Passive/HIZ也压成0，故不声称Passive',
                serialization='同文件pin():119-122将标准码写入P记录；本次实际Pro SYMBOL ATTR Pin Type逐脚回读Undefined',
                normalization='硬件/FOC驱动与储能/工具/原理图交付.py:1093-1122允许明确Undefined/Passive；本轮不改公共工具或符号类型',
                converter_record_warning='安装转换器另一ELECTRICAL旧输入码表不适用于本板标准P记录'),
            library_sha256=MECHANICAL_LIBRARY_SHA256,shared_old_58_members_independently_proved=False,
            native_API_or_ERC=False,manufacturing_release=False))
    serialization.update(coordinate_tolerance_mil=0.000001,normalized_float_coordinates=normalized_coordinates,raw_exchange_bytes_unchanged=True)
    return dict(connection_readback='PASS_CONVERTED_PIN_AND_WIRE_GEOMETRY',
                saved_record_resolution=serialization,
                connected_pins=len(actual),NC_pins=len(actual_nc),actual_component_refs=len(actual_refs),
                full_BOM_readback=dict(status='PASS_ACTUAL_EXCHANGE_ALL_COMPONENT_ATTRIBUTES',count=len(full_BOM),
                     actual_attributes_sha256=hashlib.sha256(json.dumps(full_BOM,sort_keys=True,ensure_ascii=True).encode()).hexdigest()),
                 full_footprint_readback=dict(status='PARTIAL_EXACT_SHARED_CANDIDATE_BINDING',bound_count=len(full_bindings)+len(mechanical),
                     approved_shared_refs=full_bindings,mechanical_scope_refs=mechanical,
                     missing_refs=[p['ref'] for p in PARTS if 'approved_binding' not in p and 'mechanical_candidate' not in p],
                     complete=False,native_or_process_qualified=False),
                 capacitor_BOM_readback=dict(status='PASS_EXCHANGE_ATTRIBUTES_ONLY',refs=sorted(bom_refs),
                    count=len(bom_refs),native_BOM_export=False,actual_footprints=False),
                geometric_pins=geometric_points,scope='实际官方转换记录，未做客户端重开或ERC')
