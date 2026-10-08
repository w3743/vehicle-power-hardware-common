"""显式读取冻结板源；共享库增量绑定、官方转换与原生同版验证。"""
from pathlib import Path
import argparse, base64, collections, concurrent.futures, copy, csv, hashlib, os
import importlib.util, json, math, re, runpy, shutil, sqlite3, subprocess, sys, tempfile, time, traceback, uuid, zipfile
import requests
import xml.etree.ElementTree as ET
sys.dont_write_bytecode = True
HW = Path(__file__).resolve().parents[2]
ROOT = HW.parent
LIB = HW/'公共/库'
CACHE = HW/'公共/.cache/板级集成'
EXE = Path('D:/lceda-pro/lceda-pro.exe')
CONFIG = {
 'FOC': ('FOC驱动与储能','设计数据.py','原生工程','电机驱动原理图','原理图核验.json',
         {'设计数据.py':'2a7da3f2f4af67d4bc868017bf239d96a8e36d7ad57178c68e6ab532dacb9fdf',
           '中央稳压模块.py':'55c06ee3ab913c9cd7cf3e3d7cd55a3d4360216579a27949eaf309d4c762b936'}),
 'BMS': ('充电与BMS','设计数据.py','原生候选','BMS原理图候选','原理图核验.json',
         {'设计数据.py':'5a23d7909762c4680257468d3ad091186f054d5a74a0c8830d3a37294d56c46e',
          '充电模块.py':'d8f39ba623cb34b4ebbaf21138cc02d67c74bd8202c0a6ab359fdc267269ea35'}),
 '配电': ('配电与水泵','设计源.py','原生工程','系统辅助板候选','核验.json',
         {'设计源.py':'76ea145bdd5b9472e844264bd4d670c93e639984d1dd51842d51c9024884c9c3'})}
SPLIT_BOARDS={'BMS板','外充板'}
SPLIT_INPUT_HASHES={'BMS板':'809cb7a14c0b5adacd2d3e4623623e099d6488823da8b55e4a5019fa67361766',
 '外充板':'2a15eba568282300a905003b3c49201d0ac7e0a0bb9933d2e471ecf218872c49'}
for _board in SPLIT_BOARDS:CONFIG[_board]=CONFIG['BMS']
def dump(x): return json.dumps(x,ensure_ascii=False,indent=2)
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def scope_digest(values): return hashlib.sha256(dump(sorted(values)).encode('utf8')).hexdigest()
TOOL_SHA=sha(__file__)
def write_exclusive(path,payload):
 """Create evidence bytes once; never replace an existing historical export."""
 path=Path(path)
 with path.open('xb') as f:f.write(payload)
 return sha(path)

def artifact_relative_path(path,base):
 """Legacy intermediates may live in the shared cache, never outside this root."""
 path=Path(path).resolve();base=Path(base).resolve()
 assert path.is_relative_to(ROOT.resolve()) and base.is_relative_to(ROOT.resolve())
 return os.path.relpath(path,base)
def new_export_dir(root,record_key):
 return Path(tempfile.mkdtemp(prefix=f'{record_key}-回读-',dir=root))
def save_export_text(export_dir,name,text):
 path=Path(export_dir)/name
 return path,write_exclusive(path,text.encode('utf8'))
def validate_protel2_reuse(record,source_hashes,source_sha,origin_sha,root=ROOT):
 """Validate identity and every declared file reference before evidence reuse."""
 if record.get('板源文件SHA256')!=source_hashes or record.get('源SHA256')!=source_sha:
  raise ValueError('网表证据板源SHA与当前源不一致')
 if record.get('原件SHA256_前')!=origin_sha or record.get('原件SHA256_后')!=origin_sha:
  raise ValueError('网表证据原件SHA与当前原件不一致')
 pairs=(('同版原件','原件SHA256_后'),('隔离副本','隔离副本SHA256_后'),
        ('实际官方交换文件','实际官方交换SHA256'),('保全副本','保全副本SHA256'),
        ('必要文件','必要文件SHA256'),('原生图面预览','原生图面预览SHA256'),('官方原生SVG','官方原生SVGSHA256'))
 refs=[];historical_missing=[]
 def walk(value):
  if isinstance(value,dict):
   historical='原字节证据未恢复' in value.get('历史原字节状态','')
   for path_key,hash_key in pairs:
    if path_key not in value and hash_key not in value:continue
    if path_key not in value or hash_key not in value:raise ValueError(f'证据文件路径/SHA字段不完整: {path_key}')
    rel=Path(value[path_key]);path=rel if rel.is_absolute() else Path(root)/rel
    if not path.resolve().is_relative_to(Path(root).resolve()):raise ValueError(f'证据文件路径越界: {path_key}')
    expected=value[hash_key]
    if historical and path_key=='实际官方交换文件':
     if not path.is_file() or sha(path)!=expected:historical_missing.append(str(value[path_key]))
     else:refs.append(str(value[path_key]))
     continue
    if not path.is_file() or sha(path)!=expected:raise ValueError(f'声明的证据文件不存在或SHA不符: {path_key}')
    refs.append(str(value[path_key]))
   for child in value.values():walk(child)
  elif isinstance(value,list):
   for child in value:walk(child)
 walk(record)
 if not refs:raise ValueError('网表证据没有可校验的文件引用')
 if historical_missing or any('原字节证据未恢复' in str(v) for v in _walk_values(record)):
  return {'status':'INCOMPLETE_HISTORICAL_BYTES','checked_file_refs':len(refs),'missing_historical_refs':historical_missing}
 return {'status':'REUSABLE_COMPLETE','checked_file_refs':len(refs)}
def _walk_values(value):
 if isinstance(value,dict):
  for child in value.values():yield child;yield from _walk_values(child)
 elif isinstance(value,list):
  for child in value:yield child;yield from _walk_values(child)
def read(p): return json.loads(Path(p).read_text(encoding='utf8'))
def write(p,x): Path(p).write_text(dump(x),encoding='utf8')

def normalize_pin_function(name):
 """允许字体/拼写别名，但必须保留模拟输入及电源的正负极性。"""
 name=name.upper().replace('−','-').replace('–','-')
 normalized=''.join(v for v in name if v.isalnum() or v in '+-')
 return {'GROUND':'GND','VOUT':'OUT','-IN':'IN-','+IN':'IN+',
         'INMINUS':'IN-','INPLUS':'IN+'}.get(normalized,normalized)

def compare_pin_functions(source_functions,expected_functions,numbers):
 return {n:[source_functions.get(n,''),expected_functions.get(n,'')] for n in numbers
         if normalize_pin_function(source_functions.get(n,''))!=normalize_pin_function(expected_functions.get(n,''))}
def module(name):
 p=Path(__file__).with_name(name+'.py');s=importlib.util.spec_from_file_location('board_'+name,p)
 m=importlib.util.module_from_spec(s);s.loader.exec_module(m);m.CACHE=CACHE;return m
def stable_pd_source(manifest_path):
 """消费作者完整稳定板包；候选输入不更改历史白名单或正式交付入口。"""
 manifest_path=Path(manifest_path).resolve()
 assert manifest_path.is_relative_to(CACHE.resolve()),'稳定清单须在既有集成缓存'
 inp=read(manifest_path);assert inp['board']=='配电'
 base=manifest_path.parent;live_base=HW/'配电与水泵'
 hashes=inp['源文件SHA256'];assert set(hashes)=={'设计源.py'}
 for name,expected in hashes.items():
  assert sha(base/name)==expected and sha(live_base/name)==expected,'稳定源改变，停止消费'
 bom=base/inp['作者BOM'];assert bom.resolve().is_relative_to(base)
 assert sha(bom)==inp['作者BOM_SHA256'],'作者BOM字节变化'
 d={'__file__':str(live_base/'设计源.py'),'__name__':'stable_pd_source'}
 exec(compile((base/'设计源.py').read_bytes(),str(base/'设计源.py'),'exec'),d)
 parts=copy.deepcopy(d['PARTS']);refs=[p['ref'] for p in parts]
 assert len(refs)==len(set(refs))==inp['位号数']
 assert sum(len(p['pins']) for p in parts)==inp['端子数']
 nets={(p['ref'],n):net for p in parts for n,net in p['pins'].items() if not net.startswith('NC_')}
 nc={(p['ref'],n) for p in parts for n,net in p['pins'].items() if net.startswith('NC_')}
 assert set(refs)==set(inp['expected_refs'])
 assert nets=={(r,n):v for r,n,v in inp['expected_connections']}
 assert nc=={tuple(x) for x in inp['expected_NC']}
 assert set(nets.values())==set(inp['expected_nets'])
 with bom.open(encoding='utf-8-sig',newline='') as f:rows=list(csv.DictReader(f))
 assert len(rows)==len(refs) and {r['位号'] for r in rows}==set(refs)
 by={p['ref']:p for p in parts}
 for row in rows:
  p=by[row['位号']]
  assert row['完整型号']==p['model'] and row['数值']==str(p['value']) and row['制造商']==p['manufacturer'],row['位号']
  assert float(row['数量'])==float(p.get('quantity',1)) and row['装配']==p.get('assembly','候选装配禁止生产'),row['位号']
  assert row['源SHA256'].lower()==hashes['设计源.py'] and row['制造放行']=='否',row['位号']
 for p in parts:
  p['mpn']=p['model'];p['page']=p.get('page',p.get('section',''))
  p['onboard']=bool(p.get('pcb_footprint_required',p.get('installation')!='板外')) if ('pcb_footprint_required' in p or p.get('installation')=='板外') else not any(s in p['model'] for s in ('接口','TBD','未知负载'))
  p.setdefault('quantity',1)
 return dict(board='配电',base=base,live_base=live_base,name='配电板R1候选',
  target=base/'原生候选',report=base/'核验.json',parts=parts,data=d,
  digest=hashes['设计源.py'],hashes=hashes,frozen=True,revision=inp['输入版本'],
  tool_sha=TOOL_SHA,structured_regions=True,build_root=base,
  packet_path=base/'单页工具集成输入.json',exchange_target=base/'配电板R1候选.epro2',
  stable_manifest_sha=sha(manifest_path),author_bom_sha=inp['作者BOM_SHA256'],candidate_only=True,pd_stable=True)
def stable_foc_source(manifest_path,require_live=True):
 """完整作者E4电气稳定包；历史白名单和正式入口保持独立。"""
 manifest_path=Path(manifest_path).resolve()
 assert manifest_path.is_relative_to(CACHE.resolve()),'稳定清单须在既有集成缓存'
 inp=read(manifest_path);assert inp['board']=='FOC'
 base=manifest_path.parent;live_base=HW/'FOC驱动与储能';hashes=inp['源文件SHA256']
 assert set(hashes)=={'设计数据.py','中央稳压模块.py'}
 live_paths=inp.get('稳定文件路径')
 if live_paths:
  assert require_live and set(live_paths)==set(inp['稳定文件SHA256']),'活源稳定清单不适用历史保全消费'
  assert all((ROOT/live_paths[n]).resolve()==(live_base/n).resolve() for n in live_paths),'稳定路径须为本域唯一活源'
 for name,expected in inp['稳定文件SHA256'].items():
  path=ROOT/live_paths[name] if live_paths else base/name
  assert path.resolve().is_relative_to(live_base.resolve() if live_paths else base) and sha(path)==expected
  if require_live:assert sha(live_base/name)==expected,(name,'稳定作者输入改变，停止消费')
 d=runpy.run_path(str((live_base if live_paths else base)/'设计数据.py'));parts=copy.deepcopy(d['PARTS'])
 assert len(parts)==len({p['ref'] for p in parts})==inp['位号数']
 assert sum(len(p['pins']) for p in parts)==inp['端子数']
 assert {p['ref'] for p in parts}==set(inp['expected_refs'])
 assert {(p['ref'],n):net for p in parts for n,net in p['pins'].items() if not net.startswith('NC_')}=={(r,n):v for r,n,v in inp['expected_connections']}
 assert {(p['ref'],n) for p in parts for n,net in p['pins'].items() if net.startswith('NC_')}=={tuple(x) for x in inp['expected_NC']}
 for board,(refs,pins) in inp['实体板清点'].items():
  own=[p for p in parts if p['board']==board]
  assert len(own)==refs and sum(len(p['pins']) for p in own)==pins
 with ((live_base if live_paths else base)/inp['作者BOM']).open(encoding='utf-8-sig',newline='') as f:rows=list(csv.DictReader(f))
 assert len(rows)==len(parts) and {r['位号'] for r in rows}=={p['ref'] for p in parts}
 by={p['ref']:p for p in parts}
 for r in rows:
  p=by[r['位号']]
  assert r['完整型号']==p['mpn'] and r['标称参数']==str(p['value']) and r['所属板或取电边界']==p['board'],p['ref']
  assert r['装配']==p['assembly']
  quantity=float(r['数量']);assert quantity==int(quantity) and quantity in (0,1)
  assert quantity==p.get('quantity',1),p['ref']
  if p.get('fitted') is False and p.get('runtime_assembly_option'):
   assert p['assembly_profiles']=={'bringup':'DNP','runtime':'DNP'}
   assert r['bringup数量']==r['runtime数量']=='0'
  p['quantity']=int(quantity)
 for p in parts:
  assert p['design_revision']==inp['输入版本'] and p['common_sha256']==inp['共同SHA256'] and p['common_revision']==inp['共同revision']
  p['model']=p['mpn'];p['onboard']=bool(p.get('pcb_footprint_required',p['installation']!='板外'))
  p['page']=p['board']+'-'+d['SECTIONS'][p['section']].split('：')[0]
  p['names']=p.get('factory_pin_functions',p.get('pinmap_metadata',{}).get('pin_functions',{}))
  p.setdefault('quantity',1);p.setdefault('manufacturer','原厂见source')
 source_paths={name:str((ROOT/path).resolve()) for name,path in live_paths.items()} if live_paths else {}
 return dict(board='FOC',base=base,live_base=live_base,name='驱动域E4候选',target=base/'原生候选',
  report=base/'原理图核验.json',parts=parts,data=d,digest=hashes['设计数据.py'],hashes=hashes,frozen=True,
  revision=inp['输入版本'],e4_stable=True,tool_sha=TOOL_SHA,structured_regions=True,build_root=base,
  packet_path=base/'单页工具集成输入.json',stable_manifest_sha=sha(manifest_path),
  stable_manifest_path=str(manifest_path),source_paths=source_paths,candidate_only=True)

def source(board, frozen=False, revision=None):
 assert board!='BMS','当前已物理分板；请显式选择BMS板或外充板，不生成旧合板工程'
 folder,file,target,name,report,hashes=CONFIG[board];base=HW/folder
 live_base=base
 if revision:
  assert board=='FOC' or (board in SPLIT_BOARDS and revision in ('RevN-8bd580ddbc3e','RevO-93c052142116','RevP-bdf928914670','RevQ-fe3d17b2b9ce','RevR-4f35e1c53af4','RevS-b9d5714fd58d','RevU-8be06130e9ee','RevV-1c41e297d19a','RevV-583066fa99a7','RevV-533840b11849','RevW-9a044a641d5c','RevX-6b0d0383f697','RevY-e79a970cac6f')) or (board=='配电' and revision in ('RevN-c47d0646d155','RevN-8ff2fabbd4a7','RevN-b3e9f11ccab6','RevO-bcea12a69c16','RevP-4255b6ec31c8','RevP-f48f56be6bff','RevQ-64ae9411c827','RevR-d85512098789','RevAA-90371cf13928','RevAB-5273659b7895','RevAC-3e3b44b2029f'))
  revisions={'RevL-8c24403679dc':{'设计数据.py':'8c24403679dc3f093b7daf2b3d8d096e346ab9596542d8a7dee91614d58efd87',
    '储能模块.py':'5581e7fc290370fa9b5e63ddc504e452a1c8f684ffab0876df1f3489577db03d'},
   'RevM-ea0190d573e5':{'设计数据.py':'ea0190d573e59087af6b4464c16258fa71d9c4a8c0a76dacc939ac759222d321',
    '储能模块.py':'771bf87536b03f73353cbc0e041c3ac83c4cf61a6660c70ebba63c5c5d370a90'},
   'RevN-ea9850dfdb77':{'设计数据.py':'ea9850dfdb77c5980cb523fae0bd79692d553f581b0b8bb2146dffc17018648a',
    '储能模块.py':'680480e345cdae2ed71a64acca52a51be40c1545c9a5127ff21177aad97c1ac0'},
   'RevN-8bd580ddbc3e':{'设计数据.py':'8bd580ddbc3e38bbf207df7e70345dab06b5ab01f78c47e5d1fce048a4d6ceff',
    '充电模块.py':'fb8e5100d189e25461a383acc655868fd7eb62bb687f62e2136e20a9fb69e28b'},
   'RevN-c47d0646d155':{'设计源.py':'c47d0646d155426c5a76baba1ab0dc9a876b98f12604d1b2818df15a9576d11f'},
   'RevN-8ff2fabbd4a7':{'设计源.py':'8ff2fabbd4a79933e985c97b44fb7a3b5cceef2749290e3a4946517dd88b573f'},
   'RevN-b3e9f11ccab6':{'设计源.py':'b3e9f11ccab64654c82429d35d1bf7e6566ca008340abe5b9abf31e0eb9062aa'},
   'RevO-93c052142116':{'设计数据.py':'93c052142116811d33629c2b8b84e475be3f8fefd551a6988d69b942e26b88ce',
    '充电模块.py':'f4ebeffe7e65b39e7a14f14b1099268ca247a2af203e07be0452528f47d991b2'},
   'RevP-bdf928914670':{'设计数据.py':'bdf928914670c8c18c085c3e35196193d74c7005ea5930f0f17eedc2bb15de35',
    '充电模块.py':'e7978392f94dca5542bbee2f8182f37277c3f930024da217bb3f997594c80892'},
   'RevQ-fe3d17b2b9ce':{'设计数据.py':'fe3d17b2b9cedaaa1824d2af6d0197f66f0f61483bdc15fd3e3635ce9442769f',
    '充电模块.py':'661a729644c4573c15891828c458c1738e5ca54f657fb3bd35e2c2337d78e2b3'},
   'RevR-4f35e1c53af4':{'设计数据.py':'4f35e1c53af4685f21e3fb118a1adc49c40d1fcd4cc7d1ef13f9583c1c230b22',
    '充电模块.py':'25007a11d429f0488ca27bac83b67b305eccf1b0182109c836a120f06d1acccc'},
   'RevS-b9d5714fd58d':{'设计数据.py':'b9d5714fd58df372c3a0f7bff5d5747a8bfefc0d889dbb29acb22487d2fd299e',
    '充电模块.py':'1483bde950c3c30dba8ab54a60697bc8dc654e0f4b5df689e76c7e5fd4e788e3'},
   'RevU-8be06130e9ee':{'设计数据.py':'8be06130e9ee99a44a8fb114604d5dd7a52c9b54742da15874daeefb97dbbfba',
    '充电模块.py':'ec1dd488ae1e1a41edfa16b1230b4bb42f185f0e901eaaf688016f9b99057a6f'},
   'RevV-1c41e297d19a':{'设计数据.py':'1c41e297d19a2879f38fa195fc70a8136d4f5977e874fa2add565a93fc5dbc5f',
    '充电模块.py':'f4214543abd7442a8ddd08bf3c6d1ba0fab486532263975e0a9a168f297f7d91'},
   'RevV-583066fa99a7':{'设计数据.py':'583066fa99a746b5e1961f67593e84dd8e5075ae899a22a31a977526bf8e063b',
    '充电模块.py':'f4214543abd7442a8ddd08bf3c6d1ba0fab486532263975e0a9a168f297f7d91'},
   'RevV-533840b11849':{'设计数据.py':'533840b11849e8bb880383276c1ac318a18e26ed5bf7e831de019fedae307bf3',
    '充电模块.py':'f4214543abd7442a8ddd08bf3c6d1ba0fab486532263975e0a9a168f297f7d91'},
   'RevW-9a044a641d5c':{'设计数据.py':'9a044a641d5c3905582dadbcccc4c03f90440cbfa6ffa9c5c0cc32937f36dccc',
    '充电模块.py':'7dcc6a683c55079e160efdd6a96e5d9be3ae289c05e9a12540b6a15f18761c7c'},
   'RevX-6b0d0383f697':{'设计数据.py':'6b0d0383f69795fcf3d3b62e2b3db5ea1d019a5b33979712b6cbd0737abbc1f9',
    '充电模块.py':'7dcc6a683c55079e160efdd6a96e5d9be3ae289c05e9a12540b6a15f18761c7c'},
   'RevY-e79a970cac6f':{'设计数据.py':'e79a970cac6ffe7788ad34a3420d40d88fe23a9bf0518b13ea8c5404c7b13456',
    '充电模块.py':'3d6049236b1acf1a6769bdaa804f8968f9ad0240d01fff842753fed64cb84e8c'},
   'RevQ-64ae9411c827':{'设计源.py':'64ae9411c82719e99dd9fd5bdffac82c02cb775004f3fcb824159c415629191e'},
   'RevR-d85512098789':{'设计源.py':'d85512098789d68089072da1aa363a75cba0beecd31d1ef1de675c883a9ce242'},
   'RevU-f519d949e18c':{'设计数据.py':'f519d949e18c51e291b858201ec66ec1416f538a6dc3b3ea09fb5852ec80901e',
    '储能模块.py':'9f9d23ece753d5e06b82518f613a22dd6953b90a9d41fe140a37da1a2cef280a'},
   'RevV-d68cc398dbf1':{'设计数据.py':'d68cc398dbf17dd7d5c182cef2b9b7f0ddb7871faa332c8101200aa4eb3fbc35',
    '储能模块.py':'d763eb0f8bf51d1cab2ad96e1313a543f5c9acf1a0437ec6d166dd46e9b60e95'},
   'RevV-8a893cee9b2b':{'设计数据.py':'8a893cee9b2b1b6db01e5b036280241d5a004d7e87a3851a39029ea24699855e',
    '储能模块.py':'31854cadd2aa5d51e5e92951bd980e6e0d9b058d8c6b90464548a93ed47f6d79'},
   'RevV-4a8a056128cf':{'设计数据.py':'4a8a056128cfc6c1d6a64284eeaf89c38afc1be4f536b3405af86c91669d8e2d',
    '储能模块.py':'31854cadd2aa5d51e5e92951bd980e6e0d9b058d8c6b90464548a93ed47f6d79'},
   'RevW-c64d726f5775':{'设计数据.py':'c64d726f57756769c6d4b6c8fe80386886ce8b7c8b4d748fc9d6f3be48df47ba',
    '储能模块.py':'e20cb28f160af09a7942d4bfae9c633867594e3b3e46935efb0f07f256425c3a'},
   'RevX-d417b7aa3df8':{'设计数据.py':'d417b7aa3df802a43eb078ad0f8b9f7b45eecb2be4ac83daa3276a6dd8b9e82b',
    '储能模块.py':'4a7b0ad0a61fa205cc7e2dc1b4b3bc9b8c4a65f6ab4c69c64d805a30ff245863'},
   'RevY-bb5d2188be94':{'设计数据.py':'bb5d2188be94672c935e8d61514e522e794267ea2ad5f244fe0872921375195f',
    '储能模块.py':'ca4b87e76c008e7e02b39a1437549b34483475f5aa56b017377754df2dcb0c76'},
   'RevZ-197103dc101a':{'设计数据.py':'197103dc101ae2da8f80afdd9b404238dad9bd6c68754b74b110000b7229e1b3',
    '储能模块.py':'87cd6ef9083f5dcdaf382a76ba446712ad7984863dfe3dc4246de89876117d44'},
   'RevP-0f5f27059bb0':{'设计数据.py':'0f5f27059bb0de03a2d048b17b766457e5e118b6b1add8187425b61b3cdcbc5f',
    '储能模块.py':'6322a3be25952c46dfea6fefaa89d26354bb1d1c34fec251aeb458698d88c288'},
   'RevO-bcea12a69c16':{'设计源.py':'bcea12a69c16cfe4eaf3c6936f480c8993fbe044f31762b568e936604566b64e'},
   'RevP-4255b6ec31c8':{'设计源.py':'4255b6ec31c83a30aa8660aeebc9039d57299ab1e4db6e8b5b1d855e22a5e556'},
   'RevP-f48f56be6bff':{'设计源.py':'f48f56be6bff85721a309066a3bc9326920d05679d51969d0352651a34372475'},
   'RevAA-90371cf13928':{'设计源.py':'90371cf13928a7b70fa914cb4783afa92c4ee8b177380f7da19f2171d12dce6d'},
   'RevAB-5273659b7895':{'设计源.py':'5273659b78950f54d72bcf018fc64eeca8d8ac309c64ce7315d39827465b4fb3'},
   'RevAC-3e3b44b2029f':{'设计源.py':'3e3b44b2029f8ebe3ab3a68e5365672b742f064fb4475fcac479b9ad94ec6abf'}}
  hashes=revisions[revision]
  base=CACHE/('BMS' if board in SPLIT_BOARDS else board)/revision;frozen=True
 elif frozen:
  base=CACHE/board
  for f,h in hashes.items():
   saved=base/('当前源-'+f)
   assert sha(saved)==h, (f,'保全源字节不符')
   restored=base/f
   if restored.exists():assert sha(restored)==h, (f,'缓存源名冲突')
   else:shutil.copy2(saved,restored)
 for f,h in hashes.items(): assert sha(base/f)==h, (f,'冻结源发生变化')
 if frozen and board=='配电':
  d={'__file__':str(live_base/file),'__name__':'frozen_power_source'}
  exec(compile((base/file).read_bytes(),str(base/file),'exec'),d)
 else:d=runpy.run_path(str(base/file))
 parts=copy.deepcopy(d['PARTS']);split=None
 if board in SPLIT_BOARDS:
  splitpath=(base/'当前源-分板输入.json') if frozen and not revision else (base/board/'分板输入.json');split=read(splitpath)
  expected_split=({'BMS板':'8c28ccb22cd63ab952fd09826be239f4909b3000b5d6c192e74fba3176658d5d',
   '外充板':'8de5f00ddaeaed22e6ae54e6a77538296ed5cc2d4c0d6782edc4d6cd2973fae8'} if revision else SPLIT_INPUT_HASHES)
  if revision=='RevO-93c052142116':expected_split={'BMS板':'ce34f3441aac1b33022f40b44f350364e9ac01828ce31e070b922dd587d7542d','外充板':'e3ce178bca5496bdfd450770530f4c4ad69d34b98b02fb339f349414917f3037'}
  if revision=='RevP-bdf928914670':expected_split={'BMS板':'76166b8179ba644b116f169c1b2c16dfec24b1ee7375a2eef4cdf553440b1766','外充板':'3d70075ad5fdc2eb40816ced89a33ec4b03f6eda4221464d9ee225c7987e6195'}
  if revision=='RevQ-fe3d17b2b9ce':expected_split={'BMS板':'3632e420ef8ecbf7dba72cc03e5e097e5855225edca052fa04df57e9baae4fae','外充板':'87fb874a47eefd34a93601da4c5da431a717c98854a4f709f1621cdcc557984f'}
  if revision=='RevR-4f35e1c53af4':expected_split={'BMS板':'1970558391ce8ff6d78b1e2595b604a1d697418fcd9cbb8800ea6a86e21a9d1b','外充板':'3bd60861a8ea5452a83bc683a2206e201dd23ae698a43d7002e9bf002d32b8af'}
  if revision=='RevS-b9d5714fd58d':expected_split={'BMS板':'15dae43310c81d11281e25f4b30bfcdfcedb5ce7159d1c9cf30be51b7d3c01c5','外充板':'652bcf01fe0efc87b0ea452669b53c85d48d715bf64318102db0575bbccb3dd0'}
  if revision=='RevU-8be06130e9ee':expected_split={'BMS板':'34bcbb098afdf78cda14a3b1bdc1a5a7c38def39c4e11429016a6aee726992cf','外充板':'bad0f549912bf13fcc88bd374dfa99b2a12b58672f946ff27bc516ac7ccb4ae5'}
  if revision=='RevV-1c41e297d19a':expected_split={'BMS板':'1a3b13d11aeca59691054bd64577a905fc967ff7f549b2fa97fe7f07e1c90b88','外充板':'407bc65072c7d0057fffd205172b3e5e277b2c3108d2ecb28c935768833a1a3d'}
  if revision=='RevV-583066fa99a7':expected_split={'BMS板':'8b71b2e204321ee44e6002cfa8af9fdf3414b39bd003e2e9c4bb2bf59597e31c','外充板':'407f8abf9297f7bb29c4b33369eb9d457512ec64992a54fdfbfd42b6ff0c2d6b'}
  if revision=='RevV-533840b11849':expected_split={'BMS板':'5a3c736358a5ed8eeb00572f63afbd6e85607f60d7a93e8c059ff28338186833','外充板':'1a6a2ec866cec03fdd0b28b330413169b190892b9c9beda4132ef4a8d4df3fca'}
  if revision=='RevW-9a044a641d5c':expected_split={'BMS板':'c0163ae23ea9d0c871805c11ccd3e21a42d6e67ae70ef301cbf06e60e6423cb5','外充板':'dce8affd386b7e657be28df12d54a2179511fd9614a17dc8c7d9d52d00baa6ab'}
  if revision=='RevX-6b0d0383f697':expected_split={'BMS板':'7d5d676f0ee54bbdc01dd81833411b027b5d0f64fc85b4f16f5abd8cd4ef668d','外充板':'3fb26408b0f4362baf22109179190354fbc82182a69fe24dcba2fab74520dd68'}
  if revision=='RevY-e79a970cac6f':expected_split={'BMS板':'05c70dcdf184f103946f8cdcce4df5cafefcc812561fc4e2d25fbca579e2da89','外充板':'f8e8396a254e59df90f4d49389cb9fdbf4acef7db5766659745d9e89736ee52f'}
  assert sha(splitpath)==expected_split.get(board),'分板输入未正式冻结或SHA变化'
  assert split['board']==board and split['源文件SHA256']==hashes
  assert split['关联源SHA256']==d['source_bundle_hash']()
  parts=copy.deepcopy(split['parts']);name=split['project_name']
  targetpath=(base/split['原生目标']).resolve()
  assert (frozen or targetpath.is_relative_to((base/board).resolve())) and targetpath.stem==name
  target=str(targetpath.parent.relative_to(base))
  assert {p['ref'] for p in parts}==set(split['expected_refs']) and len(parts)==len(split['expected_refs'])
  assert all(p['board']==board for p in parts)
  connections={(p['ref'],n):net for p in parts for n,net in p['pins'].items() if not net.startswith('NC_')}
  ncs={(p['ref'],n) for p in parts for n,net in p['pins'].items() if net.startswith('NC_')}
  assert connections=={(r,n):v for r,n,v in split['expected_connections']}
  assert ncs=={tuple(x) for x in split['expected_NC']}
  assert set(connections.values())==set(split['expected_nets'])
  prefix='BMS__' if board=='BMS板' else 'CHG__'
  assert all(net.startswith(prefix) for net in connections.values()),'物理板网络域混入系统网'
  assert parts[0].get('schematic_sheet',parts[0]['section'])==split['default_page_title']
 for p in parts:
  p['mpn']=p.get('mpn',p.get('model',''));p['model']=p.get('model',p['mpn'])
  p['page']=p.get('schematic_sheet',p.get('page',p.get('section','')))
  p['onboard']=p.get('installation','').startswith('PCB板上') if board in SPLIT_BOARDS else not any(
   s in p['model'] for s in ('接口','TBD','未知负载'))
  if board=='配电' and ('pcb_footprint_required' in p or p.get('installation')=='板外'):
   p['onboard']=bool(p.get('pcb_footprint_required',p.get('installation')!='板外'))
  if board=='FOC':
   p['onboard']=p['installation']!='板外'
   p['page']=p['board']+'-'+d['SECTIONS'][p['section']].split('：')[0]
   p['names']=p.get('factory_pin_functions',p.get('pinmap_metadata',{}).get('pin_functions',{}))
  p.setdefault('value',p['model']);p.setdefault('manufacturer','待确认');p.setdefault('quantity',1)
 assert len({p['ref'] for p in parts})==len(parts)
 digest=d['source_bundle_hash']() if board in SPLIT_BOARDS else sha(base/file)
 c=dict(board=board,base=base,name=name,target=base/target,report=base/report,
             parts=parts,data=d,digest=digest,hashes=hashes,frozen=frozen,live_base=live_base,tool_sha=TOOL_SHA,revision=revision)
 if split:
  intermediate=base/board if base.resolve().is_relative_to(CACHE.resolve()) else CACHE/board
  c.update(split=split,split_input_sha256=sha(splitpath),bom_path=intermediate/'候选BOM.csv',exchange_target=intermediate/(name+'.epro2'))
  if not base.resolve().is_relative_to(CACHE.resolve()):c['target']=intermediate/'原生候选'
 return c
def archive(path):
 if not path.exists():return {}
 with zipfile.ZipFile(path) as z:assert z.testzip() is None;return {n:z.read(n) for n in z.namelist()}
def save_archive(path,entries):
 # ZIP timestamps are not library geometry. Do not invalidate native
 # evidence or trigger an official rebuild when every member is identical.
 if path.exists() and archive(path)==entries:return
 tmp=path.with_suffix('.tmp.zip')
 with zipfile.ZipFile(tmp,'w',zipfile.ZIP_DEFLATED) as z:
  for n,b in sorted(entries.items()):z.writestr(n,b)
 with zipfile.ZipFile(tmp) as z:assert z.testzip() is None
 tmp.replace(path)
def raw_objects():
 result={}
 for n,b in archive(LIB/'嘉立创库数据.zip').items():
  p=json.loads(b);r=p.get('result') or {};s=r.get('dataStr') or {};f=(r.get('packageDetail') or {}).get('dataStr') or {}
  s=json.loads(s) if isinstance(s,str) else s;f=json.loads(f) if isinstance(f,str) else f
  if not isinstance(s,dict) or not isinstance(f,dict):continue
  para=s.get('head',{}).get('c_para',{});mpn=para.get('Manufacturer Part','')
  pins={q.split('^^')[4].split('~')[4]:q.split('^^')[3].split('~')[4] for q in s.get('shape',[]) if q.startswith('P~')}
  primary_pins=set(pins)
  for unit in r.get('subparts') or []:
   data=unit.get('dataStr',{})
   if isinstance(data,str):data=json.loads(data)
   for q in data.get('shape',[]):
    if q.startswith('P~'):
     fields=q.split('^^');number=fields[4].split('~')[4];function=fields[3].split('~')[4]
     pins.setdefault(number,function)
  pads=[q.split('~')[8] for q in f.get('shape',[]) if q.startswith('PAD~')]
  if mpn and pins and pads:result[mpn.casefold()]=dict(member=n,blob=b,symbol=s,footprint=f,
   pins=pins,pads=pads,multipart=set(pins)!=primary_pins,code=para.get('Supplier Part',''),uuid=r['packageDetail'].get('uuid'))
 return result
def fetch(c):
 old=archive(LIB/'嘉立创库数据.zip');raw=raw_objects();catalog=read(LIB/'嘉立创元件匹配.json')
 batches=catalog.setdefault('板级集成查库',{});prior=batches.get(c['board'],{}).get('型号结果',[])
 known={r['原型号']:r for r in prior}
 if c['board'] in SPLIT_BOARDS or c.get('e4_stable'):
  # 分板不改变完整型号查库的事实；沿用既有失败，避免同型号再次撞库/WAF。
  for batch in batches.values():
   for r in batch.get('型号结果',[]):known.setdefault(r['原型号'],r)
 preflight=catalog.get('充电BMS候选库预检',{}).get('器件',[])
 # 已明确失败的候选不无变化重复请求。
 for r in preflight:
  if r.get('model') and r.get('status') not in ('已取原始符号与封装',) and r.get('code'):
   known.setdefault(r['model'],{'原型号':r['model'],'状态':r.get('status'),'预检记录':r})
 groups={}
 for p in c['parts']:
  if p['mpn'] and p['onboard'] and not any(t in p['mpn'] for t in ('TBD','待选','未知')):
   groups.setdefault(p['mpn'],[]).append(p)
 api=module('获取嘉立创元件');pending=[m for m in groups if m.casefold() not in raw and m not in known]
 aliases={'Vishay Dale':'Vishay Intertech','Vishay':'Vishay Intertech','onsemi':'ON Semiconductor',
          'onsemi':'onsemi','STMicroelectronics':'STMicroelectronics','Panasonic':'Panasonic',
          'Würth Elektronik':'Wurth Elektronik','Microne':'MICRONE'}
 def job(m):
  ps=groups[m];r=api.search(m,[p['ref'] for p in ps]);maker=ps[0]['manufacturer']
  norm=lambda s: ''.join(x for x in s.casefold() if x.isalnum()).replace('technologies','').replace('intertech','').replace('electronics','').replace('semiconductor','')
  matches=[x for x in r.get('匹配',[]) if norm(x['厂家'])==norm(aliases.get(maker,maker))]
  r['指定厂家']=maker;r['选定匹配']=matches[0] if len(matches)==1 else None
  if len(matches)!=1:return r,None
  code=matches[0]['立创编号'];url=api.CAD.format(code=code);r['库数据']={'URL':url}
  cached_name=f'元件_{code}.json'
  if cached_name in old:
   r['库数据'].update(结果='复用已有原始库；不重复下载',原始数据SHA256=hashlib.sha256(old[cached_name]).hexdigest())
   return r,(cached_name,old[cached_name])
  try:
   response=requests.get(url,headers=api.HEADERS,timeout=25);r['库数据']['HTTP状态']=response.status_code
   response.raise_for_status();body=response.json();r['库数据']['success']=body.get('success',False)
   if not body.get('success'):return r,None
   blob=json.dumps(body,ensure_ascii=False).encode('utf8');r['库数据']['原始数据SHA256']=hashlib.sha256(blob).hexdigest()
   return r,(f'元件_{code}.json',blob)
  except Exception as e:r['库数据']['错误']=type(e).__name__+': '+str(e)[:180];return r,None
 print('查库',c['board'],'新型号',len(pending),flush=True)
 with concurrent.futures.ThreadPoolExecutor(max_workers=6) as pool:
  for i,(r,b) in enumerate(pool.map(job,pending),1):
   known[r['原型号']]=r
   if b:
    if b[0] in old:assert old[b[0]]==b[1], '同编号原始库变化；不得覆盖'
    old[b[0]]=b[1]
   if i%12==0:print('查库完成',i,'/',len(pending),flush=True)
 save_archive(LIB/'嘉立创库数据.zip',old)
 batches[c['board']]={'源SHA256':c['digest'],'型号结果':[known[m] for m in groups if m in known],
                      '自动替换型号':False,'制造放行':False}
 write(LIB/'嘉立创元件匹配.json',catalog)
 print('查库完成；原始库成员',len(old),flush=True)

def add_final_batch_specs(specs,models):
 """最后收口批次：独立厂家针表与明确工程尺寸，不以源针表回显为厂家证据。"""
 def pads(rows,w,h):
  return [dict(number=str(n),x_mm=x,y_mm=y,width_mm=w,height_mm=h) for n,x,y in rows]
 def add(m,name,url,method,pp,functions=None,factory=True,**extra):
  if m not in models:return
  specs[m]=dict(name=name,source=url,method=method,pads=pp,
   manufacturer_landpattern_verified=factory,prefer_manufacturer_geometry=True,
   electrical_substitution=False,native_new_binding_readback='NOT_RUN_PENDING_FINAL_BATCH',
   notes='仅封装与逐针合同；工程阻焊/钢网、热与制造条件由人类layout落实，不据此放行整板。',**extra)
  if functions:specs[m]['pin_functions']=functions
 if 'RT1206BRD0710KL' in models:
  s=copy.deepcopy(read(LIB/'封装补充依据.json')['板级集成厂家封装']['RT1206BRD07220RL'])
  s.update(method='RT V17 p2/p4精确1206/B0.1%/R纸带/D25ppm/07/10K/L；Mounting V10 p4 Fig4/Table1原厂回流铜A4.2/B2.2/C1/D1.5目视核对；复用同系列1206的已核铜面，不继承220R电气或功耗',native_new_binding_readback='NOT_RUN_PENDING_PD_REMAINING_BATCH')
  specs['RT1206BRD0710KL']=s
 so8=pads([(i+1,-2.7,-1.905+i*1.27) for i in range(4)]+[(8-i,2.7,-1.905+i*1.27) for i in range(4)],1.55,.6)
 for m,url,method,fn in (
  ('MCP4921-E/SN','https://ww1.microchip.com/downloads/en/DeviceDoc/21897B.pdf','DS21897B p1针/p32 SN8实体/p39订购；铜面复用同厂家SN8 DS21290F p31 C04-2057A，不伪称DAC原文提供land', ['VDD','CS','SCK','SDI','LDAC','VREF','VSS','VOUT']),
  ('MCP3201T-BI/SN','https://ww1.microchip.com/downloads/en/DeviceDoc/21290F.pdf','DS21290F p1针/p30 SN8实体/p31 C04-2057A厂家land/p37订购', ['VREF','IN+','IN-','VSS','CS/SHDN','DOUT','CLK','VDD']),
  ('LM2662MX/NOPB','https://www.ti.com/lit/ds/symlink/lm2662.pdf','SNVS002E p3针/p20订购/p26 D0008A/p27厂家land', ['FC','CAP+','GND','CAP-','OUT','LV','OSC','V+'])):
  add(m,'项目封装_TI_D0008A_原厂推荐',url,method,so8,dict(zip(map(str,range(1,9)),fn)))
 add('BZT52H-C12','项目封装_BZT52H_SOD123F_厂家推荐','https://assets.nexperia.com/documents/data-sheet/BZT52H_SER.pdf',
  'BZT52H全族Rev7 p2针/p11 Fig12厂家铜面；C12精确族型号，1K2A',pads([(1,-1.4,0),(2,1.4,0)],1.2,1.2),{'1':'K','2':'A'})
 add('MMBT5551LT1G','项目封装_onsemi_CASE318_原厂推荐','https://www.onsemi.com/pdf/datasheet/mmbt5550lt1-d.pdf',
  'Rev15 p1针/p6LT1G/p8CASE318铜面；中心排距1.95由总外2.90减pad.95推导',pads([(1,-.95,.975),(2,.95,.975),(3,0,-.975)],.56,.95),{'1':'B','2':'E','3':'C'})
 if 'PBSS4240T,215' in models:
  s=copy.deepcopy(specs['NX3008PBK,215']);s.update(source='https://assets.nexperia.com/documents/data-sheet/PBSS4240T.pdf',
   method='Nexperia 13May2022 p1针/p4Fig2实际推荐铜面；同厂SOT23几何复用，不复用MOS管功能',pin_functions={'1':'B','2':'E','3':'C'})
  for k in ('manufacturer_pdf','manufacturer_pdf_sha256','manufacturer_exact_ordering_source','manufacturer_exact_ordering_identity'):s.pop(k,None)
  specs['PBSS4240T,215']=s
 add('LTC6995IS6-1#TRPBF','项目封装_ADI_S6_厂家推荐','https://www.analog.com/media/en/technical-documentation/data-sheets/LTC6995-6695-1-6695-2.pdf',
  'RevB p2精确S6-1针/p26推荐land；1.22ref×.62max/排距2.62ref/.95pitch',
  pads([(1,-1.31,-.95),(2,-1.31,0),(3,-1.31,.95),(4,1.31,.95),(5,1.31,0),(6,1.31,-.95)],1.22,.62),dict(zip(map(str,range(1,7)),['RST','GND','SET','DIV','V+','OUT'])))
 aqz=[dict(number=str(i+1),x_mm=x,y_mm=0,width_mm=1.8 if i<2 else 2.1,height_mm=1.8 if i<2 else 2.1,drill_mm=.8 if i<2 else 1.1,shape='ELLIPSE') for i,x in enumerate((0,2.54,12.70,17.78))]
 add('AQZ205','项目封装_AQZ205_原厂孔位_工程铜环','https://industry.panasonic.com/ac/cdn/e/control/relay/photomos/catalog/semi_eng_pwr1a_aqz10_20.pdf',
  'ASCTB150E202204物理p12针1LED-K/2LED-A/3,4双向负载；底视孔图转器件侧顶视，正面标记侧1起不等距2.54/10.16/5.08',aqz,
  {'1':'LED K','2':'LED A','3':'load terminal','4':'load terminal'},False,
  manufacturer_hole_pattern_verified=True,project_drill_conditions='厂家孔.8/1.1、孔位±.1；铜盘1.8/2.1为工程选择，名义环.5，须落实制板孔差。')
 add('1714971','项目封装_MKDS5_2_P9p52_工程铜环','https://www.phoenixcontact.com/en-us/products/printed-circuit-board-terminal-mkds-5-2-95-1714971',
  '准确产品文本2位/P9.52/孔1.3/方脚.9×.9；厂家左右编号图未核，1左2右是项目编号及装配极性',
  [dict(number=str(i+1),x_mm=x,y_mm=0,width_mm=3,height_mm=3,drill_mm=1.3,shape='ELLIPSE') for i,x in enumerate((-4.76,4.76))],None,False,
  numbering_basis='项目CAD1=VBUS/2=GND，丝印明确；不宣称厂家正负功能或左右编号',project_drill_conditions='工程铜盘3mm/孔1.3mm；方脚对角1.273mm，孔余量较小，制板及装配孔差须核清，未宣称制造已通过。')
 add('GRM32ER61C476KE15L','项目封装_GRM32_47uF_工程候选','https://search.murata.co.jp/Ceramy/image/img/A01X/G101/ENG/GRM32ER61C476KE15-01A.pdf',
  '准确原厂PDF本次403未取得，不能声称读过；依据明确GRM32实体最大3.5×2.7×2.7mm采用工程铜面，非厂家land',pads([(1,-1.65,0),(2,1.65,0)],1.6,2.8),None,False,
  manufacturer_exact_pdf_obtained=False,body_height_max_mm=2.7,engineering_landpattern_conditions='端头覆盖、锡膏和工艺须人类layout落实；不复用2.2uF高度或有效容量。')
 if 'SN74LXC1T45DBVR' in models:
  s=copy.deepcopy(specs.get('TS5A63157DBVR') or read(LIB/'封装补充依据.json')['板级集成厂家封装']['TS5A63157DBVR']);s.update(source='https://www.ti.com/lit/ds/symlink/sn74lxc1t45.pdf',
   method='精确DBVR p3针/p39DBV0006A4214840/G08/2024；复用同6脚DBV铜面不复用开关功能',
   pin_functions=dict(zip(map(str,range(1,7)),['VCCA','GND','A','B','DIR','VCCB'])),pin_function_aliases={'5':['DIR A->B','DIR A→B']},
   notes='PCB顶视DBV6：1VCCA、2GND、3A、4B、5DIR、6VCCB；DIR高为A到B，低为B到A。仅复用同封装铜面，不继承TS5A模拟开关常开/常闭功能。阻焊钢网及工艺由PCB落实，无额外NC、热焊盘或整板放行。')
  for k in ('manufacturer_pdf','manufacturer_pdf_sha256'):s.pop(k,None)
  specs['SN74LXC1T45DBVR']=s
 add('ABM8G-12.000MHZ-8-D2X-T','项目封装_ABM8G_原厂推荐','https://abracon.com/Resonators/ABM8G.pdf','精确ABM8G p2器件侧顶视；3.2×2.5，两排±.85两列±1.1',
  pads([(1,-1.1,.85),(2,1.1,.85),(3,1.1,-.85),(4,-1.1,-.85)],1.4,1.2),{'1':'XTAL','2':'GND','3':'XTAL','4':'GND'},pin_function_aliases={'1':['XTAL1','晶体端1'],'3':['XTAL2','晶体端2']})
 for m,a,b,cv,body in (('CGA6N3X7R2A225K230AB',2.2,1.1,2.2,[3.6,2.8,2.5]),('CGA3E1X7R1C105K080AC',.7,.7,.7,[1.7,.9,.9])):
  add(m,'项目封装_TDK_'+m+'_原厂范围中值','https://product.tdk.com/en/search/capacitor/ceramic/mlcc/info?part_no='+m,
   '准确型号产品页回流PA/PB/PC；AC11010023 June2026物理p17/印16图：A内隙B铜长C铜宽，取推荐范围工程中值，非唯一厂家值',
   pads([(1,-(a+b)/2,0),(2,(a+b)/2,0)],b,cv),None,False,manufacturer_landpattern_range_verified=True,body_max_mm=body)
 for m in ('WSL2512R0100FEA','WSL25128L000FEA'):
  if m in models:
   s=copy.deepcopy(specs['WSL2512R0200FEA']);s.update(method='Vishay Doc30100 Rev23-Nov2023 p1精确型号解码/p2 WSL2512 .007至.5ohm行同推荐铜面；复用既核物理模板，非额定/热放行')
   specs[m]=s
 for m in ('KLKD025.HXR','KLKD006.HXR','KLKD002.HXR','KLKD004.HXR'):
  add(m,'项目封装_KLKD_HXR_原厂槽孔_工程铜环','https://www.littelfuse.com/assetdocs/klkd-datasheet?assetguid=7b52eebb-c7cc-43df-a8da-9682a338e0f6',
   'KLKD全族Rev061217 p2精确HXR PCB1tab/p1槽孔3.56×1.02、pitch38.86；非.T套帽夹持版',
   [dict(number=str(i+1),x_mm=x,y_mm=0,width_mm=4.6,height_mm=2,drill_mm=1.02,slot_length_mm=3.56,shape='OVAL') for i,x in enumerate((-19.43,19.43))],None,False,
   manufacturer_hole_pattern_verified=True,project_drill_conditions='铜oval4.60×2.00为工程选择；原厂槽3.56×1.02；名义最小环.49，制板槽公差须落实。')
 def copper_union(number,rectangles):
  from shapely.geometry import box
  from shapely.ops import unary_union
  copper=unary_union([box(x-w/2,y-h/2,x+w/2,y+h/2) for x,y,w,h in rectangles])
  assert copper.geom_type=='Polygon' and not copper.interiors,'连续铜面不得成为孤岛或虚造孔'
  left,top,right,bottom=copper.bounds
  return dict(number=str(number),x_mm=(left+right)/2,y_mm=(top+bottom)/2,width_mm=right-left,height_mm=bottom-top,
   shape='POLYGON',polygon_mm=[list(p) for p in list(copper.exterior.coords)[:-1]])
 if 'SiS892ADN-T1-GE3' in models:
  pp=pads([(i+1,-1.435,y) for i,y in enumerate((-.990,-.330,.330,.990))],.990,.405)
  ys=(.990,.330,-.330,-.990)
  pp.append(copper_union(5,[(.5575,0,1.725,2.235)]+[(1.550,y,.760,.405) for y in ys]))
  pp+=pads([(i+5,1.550,y) for i,y in enumerate(ys) if i],.760,.405)
  add('SiS892ADN-T1-GE3','项目封装_PowerPAK1212_8_Single_连续D_工程边界','https://www.vishay.com/docs/72597/72597.pdf',
   '精确产品62716 p1针，AN826 Doc72597 p7实际推荐1212 Single；3.86铜跨/.660pitch/.405盘高；不是SO8或1212-8S',pp,
   {**{str(i):'S' for i in (1,2,3)},'4':'G',**{str(i):'D' for i in (5,6,7,8)}},False,
   internally_common_pins=[['1','2','3'],['5','6','7','8']],manufacturer_landpattern_dimensions_verified=True,
   project_mask_paste_conditions='连续Drain由5大polygon与真实6..8重叠铜保留针号；推荐图英寸与mm有舍入，钢网阻焊另验。')
 for count in (8,12):
  m=f'43045-{count:02d}00';columns=count//2;b=(columns-1)*3;cc=4.70 if count==8 else 10.70
  add(m,f'项目封装_Molex43045_{count:02d}00_厂家孔位_NPTH','https://www.molex.com/content/dam/molex/molex-dot-com/products/automated/en-us/salesdrawingpdf/430/43045/430451200_sd.pdf',
   'SD43045-001总图与4/6CKT子图放大：近塑料柱排右到左1..m、远排右到左m+1..2m；P3双排、B9/15、C4.7/10.7',
   [dict(number=str(i+1+offset),x_mm=b/2-i*3,y_mm=y,width_mm=2,height_mm=2,drill_mm=1.02,shape='RECT' if i+1+offset==1 else 'ELLIPSE')
    for offset,y in ((0,1.5),(columns,-1.5)) for i in range(columns)],None,False,
   manufacturer_hole_pattern_verified=True,nonplated_holes=[dict(x_mm=x,y_mm=5.82,diameter_mm=3) for x in (-cc/2,cc/2)],
   project_drill_conditions='厂家电气孔1.02±.05/双NPTH3±.05、排距4.32±.08；铜环2mm为项目选择；保留所有真实NC触点。')
 if 'TPSM65620SVCGR' in models:
  pp=pads([(4+i,x,2.75) for i,x in enumerate((-1.3,-.8,-.3,.2,.7))]+[(16-i,x,-2.75) for i,x in enumerate((-1.3,-.8,-.3,.2,.7))],.25,.7)
  corner=[(-2.1,2.75,.25,.7),(-2.225,2.588,.5,.368),(-2.6375,2.588,.325,.25)]
  for num,mx,my in ((1,1,-1),(3,1,1),(9,-1,1),(11,-1,-1)):
   pp.append(copper_union(num,[(x*mx,y*my,w,h) for x,y,w,h in corner]))
  pp.append(copper_union(2,[(-2.15,0,.65,2.8)]+[(-2.6375,y,.325,.25) for y in (-.65,0,.65)]))
  pp+=pads([(10,2.45,0)],.7,.25)+pads([(17,-.1,-.95),(18,-.1,.95)],1.4,1.5)+pads([(19,1.23,1.811)],.2,.35)
  add('TPSM65620SVCGR','项目封装_TPSM65620_VCG0019A_连续铜面工程边界','https://www.ti.com/lit/ds/symlink/tpsm65620.pdf',
   '本地原厂SNVSCU1A p4精确OPN/p5-6十九针/p45 VCG0019A4230382H09/2025实际目视；非普通QFN19，17/18真实电气GND、19BOOT',pp,
   dict(zip(map(str,range(1,20)),['FB','VOUT','MODE/SYNC','RT','EN/UVLO','NC','NC','PGND1','VIN1','SW','VIN2','PGND2','BIAS','VCC','NC','PG','GND','GND','BOOT'])),False,
   pin_function_aliases={'1':['FB固定5V'],'3':['MODE/SYNC AUTO'],'10':['SW不外接'],'14':['VCC仅内部控制'],
    '16':['PGOOD','PG开漏'],'17':['GND1','GND1/散热'],'18':['GND2','GND2/散热'],'19':['BOOT内部电容']},manufacturer_landpattern_dimensions_verified=True,
   manufacturer_pdf='公共/数据手册/TPSM65620.pdf',manufacturer_pdf_sha256=sha(HW/'公共/数据手册/TPSM65620.pdf'),
   project_mask_paste_conditions='图中R.05用矩形并集包络表达，铜面连续；不得将.2热via编作逻辑pin或已布局；阻焊/钢网制造边界尚待人类落实。')
 add('BSS131H6327XTSA1','项目封装_Infineon_BSS131_原厂推荐','https://www.infineon.com/part/BSS131',
  'Rev2.6 2012-03-29 p1 H6327订购及1G2S3D，p8实际目视Footprint铜.9×.8、两向中心距2由边隙1.1/1.2加铜宽高推导',
  pads([(1,1,1),(2,1,-1),(3,-1,0)],.9,.8),{'1':'G','2':'S','3':'D'},
  manufacturer_pdf='公共/数据手册/BSS131.pdf',manufacturer_pdf_sha256=sha(HW/'公共/数据手册/BSS131.pdf'))
 for m,count,year in (('1913714',2,2015),('1913730',4,2016)):
  a=(count-1)*10.16
  add(m,f'项目封装_Phoenix_{m}_每极三针_工程铜环',f'https://www.phoenixcontact.com/us/products/{m}',
   f'原厂{year} PDF p1精确2/4极与a尺寸、p5通用孔图实际目视；2026官网每电位3针。孔1.7/列距10.16/列内5.08；图画3列为参数示意不是实际3极',
   [dict(number=str(i+1),x_mm=i*10.16,y_mm=y,width_mm=3,height_mm=3,drill_mm=1.7,shape='ELLIPSE') for i in range(count) for y in (-5.08,0,5.08)],None,False,
   nonplated_holes=[dict(x_mm=x,y_mm=8.68,diameter_mm=3.2) for x in (-10.16,a+10.16)],manufacturer_hole_pattern_verified=True,
   manufacturer_pdf=f'公共/数据手册/Phoenix_{m}_厂家图{year}.pdf',manufacturer_pdf_sha256=sha(HW/f'公共/数据手册/Phoenix_{m}_厂家图{year}.pdf'),
   numbering_basis='厂家通用钻图未标绝对1脚；项目首列1依次2/3/4，同极三真实焊盘共号，丝印与线束须标清。OUT1P+/2P−；BAT1B10/2B−/3BAT_FUSED/4AUX_BAT_FUSED',
   project_drill_conditions='铜环3mm为工程选择，厂家指定孔1.7；法兰3.2作为项目NPTH。右法兰a+10.16直接标注，左法兰−10.16为对称几何展开非单独标注；工艺/壳体庭院须落实。')

def add_pd_remaining_specs(specs,models):
 """配电余项同批：实际原厂图铜面/孔位，工程孔环与制造条件单列。"""
 def pad(n,x,y,w,h,**kw):return dict(number=str(n),x_mm=x,y_mm=y,width_mm=w,height_mm=h,**kw)
 def dual(count,x,pitch,w,h):
  ys=[(i-(count-1)/2)*pitch for i in range(count)]
  return [pad(i+1,-x,y,w,h) for i,y in enumerate(ys)]+[pad(count*2-i,x,y,w,h) for i,y in enumerate(ys)]
 def add(m,name,url,method,pp,fn,factory=True,**kw):
  if m not in models:return
  specs[m]=dict(name=name,source=url,method=method,pads=pp,pin_functions=fn,
   manufacturer_landpattern_verified=factory,prefer_manufacturer_geometry=True,
   electrical_substitution=False,native_new_binding_readback='NOT_RUN_PENDING_PD_REMAINING_BATCH',
   geometry_view='PCB元件面TOP，x右/y下，mm；不采用底视针位',
   manufacturing_released=False,notes='铜面/孔位候选；阻焊钢网/工艺/热/安装由人类layout落实，不放行电气整板。',**kw)
 fn=lambda values:dict(zip(map(str,range(1,len(values)+1)),values))
 add('TPS7A4001DGNR','项目封装_TI_DGN0008B_配电原厂铜',
  'https://www.ti.com/lit/ds/symlink/tps7a4001.pdf',
  '本地63478C04 p3针/p16DGN8/p21,22 drawing4218837B03/2025实际目视；EP铜2x3，不将阻焊开口1.88x1.98当铜',
  dual(4,2.2,.65,1.4,.45)+[pad(9,0,0,2,3)],fn(['OUT','FB','NC','GND','EN','NC','NC','IN','EP']),
  manufacturer_package_body_mm=[3.1,3.1,1.1],mask_process_conditions='EP厂商SMD opening1.88x1.98；当前仅铜面绑定，不冒充钢网/阻焊制程完成；可选thermal-via不能画作NPTH。')
 add('TPS37043DJOFDDFR','项目封装_TI_DDF0008A_原厂铜',
  'https://www.ti.com/lit/ds/symlink/tps3704.pdf','本地2C191E12 p5/6针,p31DDF8,p35/36 drawing4222047E07/2024目视，无EP',
  dual(4,1.3,.65,1.05,.45),fn(['VDD','SENSE1','SENSE2','GND','SENSE3','RESET3_OD','RESET2_OD','RESET1_OD']),
  manufacturer_package_body_mm=[1.65,2.95,1.1])
 add('LM4040A50IDBZR','项目封装_TI_DBZ0003A_原厂推荐',
  'https://www.ti.com/lit/ds/symlink/lm4040.pdf','本地F43B6B6D family p33精确A50订单,p4针,p53/54 drawing4214838F08/2024铜目视；1K2A3允许浮空或接A，源3接GND合法',
  [pad(1,-1.05,-.95,1.3,.6),pad(2,-1.05,.95,1.3,.6),pad(3,1.05,0,1.3,.6)],fn(['K','A','A_GND']),
  manufacturer_package_body_mm=[1.4,3.04,1.12])
 add('TMUX1511PWR','项目封装_TI_PW0014A_原厂推荐',
  'https://www.ti.com/lit/ds/symlink/tmux1511.pdf','本地C32B8372 p3针/p31PW14订单/p38/39 drawing4220202B12/2023实际目视；SEL低OFF高ON',
  dual(7,2.9,.65,1.5,.45),fn(['SEL1','S1','D1','SEL2','S2','D2','GND','D3','S3','SEL3','D4','S4','SEL4','VDD']),
  manufacturer_package_body_mm=[4.5,5.1,1.2])
 add('TPD2S300YFFR','项目封装_TI_YFF0009_原厂推荐',
  'https://www.ti.com/lit/ds/symlink/tpd2s300.pdf','D1F89A59 p3TOP/BOTTOM/p31精确YFF9/p34/35 drawing4219552A05/2016实际目视，TOP ball行列非镜像bottom',
  [pad(row+str(i+1),(i-1)*.4,(j-1)*.4,.23,.23,shape='ELLIPSE') for j,row in enumerate('ABC') for i in range(3)],
  dict(zip(['A1','A2','A3','B1','B2','B3','C1','C2','C3'],['C_CC1','VBIAS','C_CC2','CC1','GND','CC2','FLT_N','VPWR','VM'])),
  manufacturer_package_body_mm=[1.39,1.39,.625])
 lm=[pad(1,-.75,-2.15,.25,.6),pad(20,.75,-2.15,.25,.6)]
 lm += [pad(i+2,-1.65,-1.75+i*.5,.6,.25) for i in range(8)]
 lm += [pad(10,-.75,2.15,.25,.6),pad(11,.75,2.15,.25,.6)]
 lm += [pad(i+12,1.65,1.75-i*.5,.6,.25) for i in range(8)]
 # 外围15和内部相连的中央物理21都保留，库同号15明确映射同一GND而非省略外围。
 lm += [pad(15,0,0,1.7,2.7)]
 add('LM5146RGYR','项目封装_TI_RGY0020B_20加实体EP_原厂铜',
  'https://www.ti.com/lit/ds/symlink/lm5146.pdf',
  '非Q1电气830CBF80 p4/5；机械复用精确RGY0020B/4222860B06/2017之官方LM5146-Q1 12F8BE37 p58/59实际目视，仅同drawing铜面，不继承Q1订单/电气',
  lm,fn(['EN_UVLO','RT','SS_TRK','COMP','FB','AGND','SYNCOUT','SYNCIN_DEM','NC','PGOOD_OD','ILIM','PGND','LO','VCC','EP_GND','NC','BST','HO','SW','VIN']),
  physical_terminal_alias={'21':'15'},physical_copper_count=21,
  physical_terminal_alias_basis='中心物理EP21与外围15 internally GND；两个铜面各保留，源逻辑15共号；21不是新增IO。',
  manufacturer_package_body_mm=[3.6,4.6,1.0],mask_process_conditions='NSMD优先；thermal-via四候选坐标(0,±1.1)/(±.6,0)，厂图未给孔径，不编固定钻孔。')
 add('LTC4368IMS-2#PBF','项目封装_ADI_MS10_原厂范围工程铜',
  'https://www.analog.com/media/en/technical-documentation/data-sheets/ltc4368.pdf',
  '8DAAF750 RevC p2 exactIMS-2/p19 MS10 05-08-1661RevF实际目视，铜长.95在.889±.127内，内距3.25在3.20..3.45内，外距5.15>=5.10；工程中值不是厂家唯一中心',
  [pad(i+1,-1+i*.5,2.1,.305,.95) for i in range(5)]+[pad(10-i,-1+i*.5,-2.1,.305,.95) for i in range(5)],
  fn(['VIN','UV','OV','RETRY','GND','SHDN','FAULT_N','VOUT','SENSE','GATE']),
  manufacturer_package_body_mm=[3.102,3.102,1.10])
 thnrows=[(1,-2.54,-10.16),(2,2.54,-10.16),(6,10.16,-10.16),(3,-10.16,10.16),(4,0,10.16),(5,10.16,10.16)]
 for m in ('THN 15-4811WI','THN 15-4812WI'):
  add(m,'项目封装_TRACO_THN15WI_真实孔位工程铜环',
   'https://www.tracopower.com/sites/default/files/products/datasheets/thn15wi_datasheet.pdf',
   '12CC102E RevJuly3 2026 p1两exact单输出订单/p4实际BOTTOM镜像X转TOP；pinpitch±.25，6/2/1顶排7.62/5.08，5/4/3底排10.16/10.16，纵20.32',
   [pad(n,x,y,2.4,2.4,drill_mm=1.3,shape='ELLIPSE') for n,x,y in thnrows],
   fn(['VIN_PLUS','VIN_MINUS','VOUT_PLUS','TRIM','VOUT_MINUS','REMOTE_ON_OFF']),False,
   manufacturer_hole_pattern_verified=True,manufacturer_package_body_mm=[25.9,25.9,10.4],
   project_drill_conditions='厂家针Ø1.0，无推荐孔/铜环；工程finishedØ1.3/铜2.4须落实针/制板孔差。无EP/额外NPTH/槽；不得在模块下走线；不继承热保证。')
 add('UPW2A471MHD','项目封装_Nichicon_PW_D16_P7p5_工程铜环',
  'https://www.nichicon.com/en-us/datasheet/8296/',
  '8BE66D99 CAT8100N p5 exact100V470u16x30.5/p1径向图目视，pitch7.5±.5针Ø.8；负极条纹，项目1正2负',
  [pad(1,-3.75,0,2.2,2.2,drill_mm=1.1,shape='ELLIPSE'),pad(2,3.75,0,2.2,2.2,drill_mm=1.1,shape='ELLIPSE')],
  {'1':'+','2':'-'},False,manufacturer_hole_pattern_verified=True,manufacturer_package_body_mm=[16.5,16.5,32.5],
  project_drill_conditions='finishedØ1.1/铜2.2为工程值，非厂家指定PCBland；插装/孔差/正负丝印须落实。')
 add('RSF500JT-73-200R','项目封装_YAGEO_RSF500_32p5工程铜环',
  'https://yageogroup.com/content/datasheet/asset/file/YAGEO-RSF_DATASHEET',
  '7C434896 V4Apr1 2024 p2精确500/J/T/73/200R，73为编带非PCB73mm；p3真实24.5±1x8.5±1，针Ø.8±.05目视',
  [pad(1,-16.25,0,2.4,2.4,drill_mm=1.2,shape='ELLIPSE'),pad(2,16.25,0,2.4,2.4,drill_mm=1.2,shape='ELLIPSE')],
  {'1':'passive','2':'passive'},False,manufacturer_package_body_mm=[25.5,9.5,9.5],
  project_drill_conditions='水平工程成型32.5pitch/finishedØ1.2/铜2.4，非厂家唯一bend；焊接离板/弯脚/热边界交人类落实。')
 add('1777545','项目封装_Phoenix_MKDS5NHV_2_ZB6p35_真实交错孔',
  'https://www.phoenixcontact.com/us/products/1777545/pdf',
  '2013厂家AD67C6D3 p5名义钻图6.35横/9纵/Ø1.3+0.1；厂家2023 STEP3AA6E998实核塑壳10191(Y0两大接线口)/10419(Y15.85背面小扣孔)，针向-Z、装配7093..7100为identity；TOP开口朝下时x=X-6.35/y=9.25-Y，与当前孔位和壳偏移一致。3D右针中心9.505的20um偏差不改厂图名义孔距。独立4838同向窄审通过，非虚线投影推测',
  [pad(1,-3.175,-4.5,2.6,2.6,drill_mm=1.3,shape='ELLIPSE'),pad(2,3.175,4.5,2.6,2.6,drill_mm=1.3,shape='ELLIPSE')],{},False,
  manufacturer_hole_pattern_verified=True,manufacturer_package_body_mm=[12.7,15.85,27],
  manufacturer_body_center_offset_mm=[0,1.325],manufacturer_absolute_pin_numbering=False,
  geometry_orientation_verified=True,
  manufacturer_cad='公共/数据手册/Phoenix_1777545_厂家2023.stp',
  manufacturer_cad_sha256='3aa6e99814341ed78b7e60d747cf797e6091c2741f3827d3b406face09003553',
  manufacturer_cad_source='https://rspsupply.com/images/downloads/Phoenix/1/Phoenix%201777545/simplified%203d%20model%20of%20the%20item.stp',
  independent_orientation_receipt={'thread':'01a10719-4838-7493-b1dd-87d621c10127','status':'PASS_SCOPED_PHOENIX1777545_TOP_OPENING_ORIENTATION','scope':'实际厂家STEP拓扑和顶点坐标，非CAD内核原生渲染/库转换回读/制造放行'},
  numbering_basis='厂家没有绝对1/2：项目元件面TOP、接线口朝下、左上孔1正/右下孔2RETURN；按原厂名义6.35/9定孔，丝印和线束必须明确此项目编号。',
  project_drill_conditions='孔Ø1.3+0.1为厂商指定；铜Ø2.6工程值，非厂家唯一land；孔差/装配/丝印/工艺由人类layout落实，不放行制造。')
 for m,family,version in (('SPM10065VT-6R8M-D','VT','20200702'),('SPM10065VC-220M-D','VC','20251217')):
  add(m,'项目封装_TDK_SPM10065'+family+'_原厂推荐铜',
   'https://product.tdk.com/info/en/catalog/datasheets/inductor_automotive_power_spm10065'+family.lower()+'-d_en.pdf',
   version+'厂家PDF实际p1准确型号/p3图像核对；左右铜2.95x4.5、内距6.1、外距12，非外形猜测；无极性项目左1右2',
   [pad(1,-4.525,0,2.95,4.5),pad(2,4.525,0,2.95,4.5)],{'1':'passive','2':'passive'},
   manufacturer_package_body_mm=[10.9,10.4,6.5],
   manufacturer_absolute_pin_numbering=False,geometry_numbering_basis='无极性两端，项目左1右2，不把绕组起始标识当厂家绝对脚号。',
   lifecycle_notes='VT准确型号NRND，不自动替换为VC；VC镜像为20251217，主站20260420同land文字数值；不继承不同系列电气/饱和/热额定。',
   primary_comparison_url='https://product.tdk.com/en/search/inductor/inductor/smd/info?part_no='+m)
  # 可得精确原始嘉立创库时仍优先复用；本轮三个准确库码接口均403。
  if m in specs:specs[m]['prefer_manufacturer_geometry']=False
 for m in ('SMBJ12A','SMBJ33A'):
  add(m,'项目封装_Littelfuse_SMBJ_DO214AA_原厂推荐铜',
   'https://www.littelfuse.com/assetdocs/tvs-diodes-smbj-series-datasheet?assetguid=ba555e99-a12d-4f72-a0b6-86b06c67171e',
   '厂家2017镜像E33E2E68 p2准确单向型号/p5实际图像；与2025JC.07/04/25v4主站p5逐项机械文字一致。J=L2.16/I2.26/K内距2.74；左阴极带，项目1K2A',
   [pad(1,-2.45,0,2.16,2.26),pad(2,2.45,0,2.16,2.26)],{'1':'K','2':'A'},
   manufacturer_package_body_mm=[4.75,3.94,2.2],manufacturer_absolute_pin_numbering=False,
   outline_lines=[dict(start=[-1.8,-1.65],end=[-1.8,1.65],layer=3,width_mm=.15)],
   geometry_numbering_basis='厂家阴极带指示极性，无绝对数字；项目1阴极/2阳极；不可当双向CA。',
   mask_process_conditions='仅机械铜面复用。2025回流预热60..120s/峰附近30smax，不继承2017旧工艺；脉冲额定使用每端5x5mm铜条件，小推荐焊盘不证明热额定。')
  if m in specs:specs[m]['prefer_manufacturer_geometry']=False
 # 原始厂家资料在公共既有手册目录保全；临时下载路径不作为交付依赖。
 for m,case,outer,notch,shoulder,small_y in (
  ('NVMFS6B25NLT1G','488AA',2.775,-2.725,.905,2.795),
  ('NVMFS6B14NLT1G','488AA',2.775,-2.725,.905,2.795),
  ('NVMFS6H800NLT1G','506EZ',2.78,-2.95,.91,2.80),
  ('NVMFS015N10MCLT1G','506EZ',2.78,-2.95,.91,2.80)):
  polygon=[[-2.28,-3.2],[-1.53,-3.2],[-1.53,notch],[1.53,notch],[1.53,-3.2],[2.28,-3.2],
   [2.28,0],[outer,0],[outer,shoulder],[2.28,shoulder],[2.28,1.33],[-2.28,1.33],
   [-2.28,shoulder],[-outer,shoulder],[-outer,0],[-2.28,0]]
  mapping={str(n):str(n) for n in range(1,6)}
  if m=='NVMFS6H800NLT1G':mapping['6']='5'
  add(m,'项目封装_ON_CASE'+case+'_连续漏极铜',
   'https://www.onsemi.com/download/package-drawing/pdf/'+case.lower()+'.pdf',
   '原厂非WF确切订单p5和TOP针p1已目视；CASE'+case+'实际推荐铜图已核。4.56为主壁，含肩最大宽'+str(2*outer)+'；单一连续16顶点D铜，不能把paste/肩当独立脚。源6逻辑D_EP仅H800显式映射至物理5，同网强制检查。',
   [pad(n,x,small_y,.75,1) for n,x in enumerate((-1.905,-.635,.635,1.905),1)]+
   [pad(5,0,-.935,2*outer,4.53,shape='POLYGON',polygon_mm=polygon)],
   {'1':'S','2':'S','3':'S','4':'G','5':'D'},
   source_pin_to_pad=mapping,pin_function_aliases={'5':['D_EP']},internally_common_pins=[['1','2','3']],
   geometry_orientation_verified=True,manufacturer_exact_ordering_verified=True,
   drain_shape_dimensions_mm={'main_width':4.56,'maximum_width':2*outer,'top':-3.2,
    'notch_y':notch,'notch_edges_x':[-1.53,1.53],'shoulder_top':0,'shoulder_bottom':shoulder,'bottom':1.33},
   mechanical_drawing_file='公共/数据手册/onsemi_CASE'+case+'_厂家封装图.pdf',
   mechanical_drawing_sha256={'488AA':'3773b736e1c76415e19ec3914cd10bce66740ee5a0948766d96db03c9154bd62',
    '506EZ':'3bcba53b7c4a8ffafe12e3a8c2feaa0d434ecd001d2c3c8de0fd6a1f2057f332'}[case])
  if m in specs:assert sha(HW/specs[m]['mechanical_drawing_file'])==specs[m]['mechanical_drawing_sha256']
  if m=='NVMFS015N10MCLT1G' and m in specs:
   specs[m].update(manufacturer_datasheet_url='https://www.onsemi.com/download/data-sheet/pdf/nvmfs015n10mcl-d.pdf',
    exact_ordering_basis='NVMFS015N10MCL/D August2022 Rev3 p1标注非WF CASE506EZ及1..3S/4G/D(5,6)，p5订购表明确NVMFS015N10MCLT1G；物理5为独立CASE506EZ IssueC Jun18 2026底面连续EP，新源仅1..5五物理脚，无第6脚。',
    document_discrepancy='Rev3附录p6仍印旧CASE488AA；本铜面未消费该旧附录。独立当前506EZ厂家机械图为铜面依据，精确型号到case关联使用同一器件p1/p5。PB24035X只列NTM商业件，未冒称覆盖此NVM订单。',
    pin_function_aliases={'5':['D_EP']})
 add('BSS138-7-F','项目封装_Diodes_BSS138_SOT23_原厂推荐铜',
  'https://www.diodes.com/assets/Datasheets/BSS138.pdf',
  'DS30144Rev25-2June2024 p1准确7-F及G/S/D，p5建议铜实际目视；X1=1.35是中心至外缘而非pitch；两行中心距2mm。',
  [pad(1,-.95,1,.8,.9),pad(2,.95,1,.8,.9),pad(3,0,-1,.8,.9)],{'1':'G','2':'S','3':'D'},
  manufacturer_exact_ordering_verified=True,geometry_orientation_verified=True)
 add('PMV20XNER','项目封装_Nexperia_PMV20XNE_SOT23_原厂回流铜',
  'https://www.nexperia.com/product/PMV20XNE',
  'PMV20XNE厂家p2针与p11Fig19 reflow实际目视；铜.6x.7、x±.95、两行中心距2mm，非paste.5x.6或wave图。R后缀与base几何关联参照原厂CN202311018I索引行，完整PCN回读待补，不能称准确订单资格已通过。',
  [pad(1,-.95,1,.6,.7),pad(2,.95,1,.6,.7),pad(3,0,-1,.6,.7)],{'1':'G','2':'S','3':'D'},
  geometry_orientation_verified=True,manufacturer_exact_ordering_verified=False,
  exact_ordering_remaining='R供货后缀完整原厂PCN PDF回读；仅base型号厂家铜面/针序通过。',
  ordering_association_url='https://www.tti.com/content/dam/ttiinc/products/PCN/nexperia/Nexperia-PCN-CN-202311018I.pdf',
  ordering_association_observed='原厂PCN索引行934068845215/PMV20XNER/PMV20XNE/SOT23/TO236AB；完整PDF未取得，不把索引片段当已下载。')
 add('BZT52H-A18X','项目封装_Nexperia_BZT52H_SOD123F_原厂回流铜',
  'https://www.nexperia.com/products/diodes/zener-diodes/serie/bzt52h-series-automotive/',
  'BZT52H_SER厂家p2针1K2A及阴极带，p11Fig11/12实际目视；铜1.2方、中心x±1.4，非paste1.1。厂家现有订单表明确A18X/934663090115/SOD123F_115，不用C15电气替代。',
  [pad(1,-1.4,0,1.2,1.2),pad(2,1.4,0,1.2,1.2)],{'1':'K','2':'A'},
  manufacturer_exact_ordering_verified=True,manufacturer_orderable_code='934663090115',geometry_orientation_verified=True)
 add('39-30-1020','项目封装_Molex_5569_02A2_厂家TOP孔序',
  'https://www.molex.com/content/dam/molex/molex-dot-com/products/automated/en-us/salesdrawingpdf/556/5569/039300040_sd.pdf',
  '55690002-SD PSD000 RevA2018-02-22实读p1尺寸/p2准确订单1020=5569-02A2/PA66UL94V2 natural，非0020的V0。TOP针1原点，针2在y−5.5，NPTH在y+7.3；side/front核短腿1长腿2和开口朝+Y，不把插接面4.2当PCB孔距。',
  [pad(1,0,0,2.7,3.7,drill_mm=1.8,shape='RECT'),pad(2,0,-5.5,2.7,3.7,drill_mm=1.8,shape='ELLIPSE')],
  {'1':'PIN1','2':'PIN2'},False,manufacturer_hole_pattern_verified=True,
  manufacturer_exact_ordering_verified=True,geometry_orientation_verified=True,
  manufacturer_body_nominal_mm=[5.4,12.8],manufacturer_body_center_offset_mm=[0,7.5],
  body_nominal_bounds_mm=[-2.7,1.1,2.7,13.9],mating_opening_direction='+Y，定位孔侧',
  nonplated_holes=[{'x_mm':0,'y_mm':7.3,'diameter_mm':3.0}],
  project_drill_conditions='厂图完成信号孔Ø1.80±.05/定位孔Ø3.00±.05、pitch5.50±.10/peg7.30±.08；铜2.7x3.7为工程选择非厂家唯一land，最窄铜环在1.85孔时.425mm。板厚≤1.78mm；插接/锁扣包络、孔公差及工艺交人类落实。',
  packaging_conditions='准确1020为bulk；厂家不推荐因搬运损伤、建议新应用tray。保留作者型号，不擅自改订单；采购/安装须落实包装保护。',
  manufacturer_pdf_mirror='https://images.100y.com.tw/pdf_file/10-molex-350230006.pdf',
  original_mirror_sha256='1cebc38647ae18c58f2f29122924d4e8a854e203d976e7bc4c76023e29aeaff9',
  extracted_pages='原7页镜像仅4..7页准确完整厂图1..4；前三页其他型号产品资料排除。',
  independent_orientation_receipt='PASS_SCOPED_MOLEX39301020_FACTORY_TOP_PIN_HOLES_ORIENTATION / 4838只读实际厂图，非库或原生放行')
 # Current protection MPNs use inspected copper drawings, not the removed
 # IXTK package or a fictitious underside mounting-base pad.
 add('PSMN1R1-100CSE','项目封装_Nexperia_SOT8005A_12引线无底部EP',
  'https://assets.nexperia.com/documents/data-sheet/PSMN1R1-100CSE.pdf',
  '正式2025-10-20 PDF p2针序/p10 TOP露热面及gate和pin1标记/p11Fig19实际目视：12个1.3x1.7铜，pitch2，内距9.6/外距13得行中心±5.65；不混mask1.45x1.85/paste1.2x1.6。',
  [pad(n,-5+(n-1)*2,5.65,1.3,1.7) for n in range(1,7)]+
  [pad(12-i,-5+i*2,-5.65,1.3,1.7) for i in range(6)],
  {**{str(n):'S' for n in range(1,6)},'6':'G',**{str(n):'D' for n in range(7,13)}},
  internally_common_pins=[[str(n) for n in range(1,6)],[str(n) for n in range(7,13)]],
  geometry_orientation_verified=True,manufacturer_exact_ordering_verified=True,
  pcb_copper_count=12,underside_exposed_pad=False,
  top_mounting_surface={'factory_terminal':'mb','electrical_function':'D','PCB_solder_pad':False,'live':True},
  mask_process_conditions='厂家推荐stencil0.1mm；阻焊/钢网不是新增铜面。顶部mb带电D，6颗反串两管顶部电位不同，热接触/金属绝缘由人类机械layout落实；不加中央底部铜或第13pad。')
 add('MPLAD30KP43AE3','项目封装_Microchip_MPLAD_底阴极及单侧阳极',
  'https://ww1.microchip.com/downloads/aemDocuments/documents/HRDS/ProductDocuments/DataSheets/mplad30kp.pdf',
  'DS00005255A2024 p4§1.1金属底K/p12Fig5-1/5-2实际目视：K方11.81..12.07、A横2.41..2.67纵5.72..5.97、间隙1.02..1.27；采用范围中点，非厂家唯一中心尺寸。',
  [pad(1,0,0,11.94,11.94),pad(2,8.385,0,2.54,5.845)],{'1':'K','2':'A'},
  pin_function_aliases={'1':['K_BACKSIDE'],'2':['A_LEAD']},
  manufacturer_absolute_pin_numbering=False,geometry_orientation_verified=True,
  geometry_numbering_basis='厂家无数字脚号；项目1是底部K大铜、2是+X侧A单引线；前TVS K接输入，后TVS K接Q1D、A接commonS，不能沿用后TVS旧GND铜。',
  mask_process_conditions='矩形铜范围工程中点，原推荐K角部圆角工艺须落实。厂家260C/10s与热条件不作为整板制造/热资格通过。')
 add('BCX53-16,115','项目封装_Nexperia_SOT89_连续集电极铜',
  'https://assets.nexperia.com/documents/data-sheet/BCX53_SER.pdf',
  'Rev11/12Aug2026 p2实际1E/2C/3B，p9Fig10 reflow：外侧.7x1.1、pitch1.5；中央2mm宽热铜与.7mm引线铜连续成一个2号polygon，铜总高4.6；不混wave或paste。',
  [pad(1,-1.5,1.75,.7,1.1),
   pad(2,0,0,2,4.6,shape='POLYGON',polygon_mm=[[-1,-2.3],[1,-2.3],[1,.5],[.35,.5],[.35,2.3],[-.35,2.3],[-.35,.5],[-1,.5]]),
   pad(3,1.5,1.75,.7,1.1)],{'1':'E','2':'C','3':'B'},
  geometry_orientation_verified=True,manufacturer_exact_ordering_verified=False,
  exact_ordering_remaining='BCX53-16,115完整订货后缀关联待核；厂家base精确-16及针序/铜面已核。')
 add('BAS116,215','项目封装_Nexperia_BAS116_SOT23_原厂回流铜',
  'https://assets.nexperia.com/documents/data-sheet/BAS116.pdf',
  '5Aug2020原厂p1实际1A/2NC/3K，p7Fig8 reflow铜.6x.7、x±.95、行中心距2；不使用wave大铜或paste.5x.6。',
  [pad(1,-.95,1,.6,.7),pad(2,.95,1,.6,.7),pad(3,0,-1,.6,.7)],{'1':'A','2':'NC','3':'K'},
  mechanical_nc_numbers=['2'],geometry_orientation_verified=True,
  manufacturer_exact_ordering_verified=False,exact_ordering_remaining='BAS116,215原厂完整订购关联待核，不把基本型号针图称后缀合格。')
 for m in ('WSR58L000FEA','WSR5R0200FEA','WSR5R0500FEA'):
  add(m,'项目封装_Vishay_WSR5_原厂两铜及Kelvin引出条件',
   'https://www.vishay.com/docs/31059/wsrhighpower.pdf',
   'Doc31059Rev25Apr2024 p1 WSR5/L小于10mΩ/R/F1%/EA无铅编带，p2实际推荐a3.94/b5.84/l内距5.21；中心距9.15，无第三底焊盘。',
   [pad(1,-4.575,0,3.94,5.84),pad(2,4.575,0,3.94,5.84)],{'1':'terminal1','2':'terminal2'},
   manufacturer_absolute_pin_numbering=False,manufacturer_exact_ordering_verified=True,
   geometry_numbering_basis='无极性两端，项目左1右2，Kelvin取样在内缘引出；厂家0.51mm取样线不是额外焊盘。',
   manufacturer_body_height_max_mm=2.537,
   mask_process_conditions='5W额定要求端子温度≤120C；本绑定不证明已满足。0.008/0.020/0.050Ω各电气参数独立，不替换型号。')
 for m,case,x,w,h in (('C0805C822J1GACTU','0805',.9,1.15,1.45),
                      ('C2220C334J1GACTU','2220',2.65,1.5,5.4)):
  add(m,'项目封装_KEMET_C0G_'+case+'_原厂IPC密度B',
   'https://content.kemet.com/datasheets/KEM_C1003_C0G_SMD.pdf',
   'C1003_C0G20Feb2025原厂p12Table3/Figure实际目视：DensityB的C是原点至铜中心、Y为铜横长、X为纵高；case'+case+'，不把C当内距或庭院当铜。',
   [pad(1,-x,0,w,h),pad(2,x,0,w,h)],{'1':'terminal1','2':'terminal2'},
   manufacturer_absolute_pin_numbering=False,
   manufacturer_exact_ordering_verified=False,exact_ordering_remaining='仅完整型号对应厂家case与推荐铜面；电气/采购资格按作者及完整型号表单独核，不冒充替换其他容量。')
 for m in ('RC0805FR-0747RL','RC0805FR-073R3L'):
  add(m,'项目封装_YAGEO_RC0805_原厂回流铜',
   'https://www.yageogroup.com/content/Resource%20Library/Product%20Guide-Catalog/yageo_PYu-R_Mount_10_19050818_343.pdf',
   'MountingV10/13Feb2018 p4Fig4/Table1实际目视0805回流A3/B内1.2/C铜横.9/D铜纵1.2；铜中心±1.05，非wave表。',
   [pad(1,-1.05,0,.9,1.2),pad(2,1.05,0,.9,1.2)],{'1':'terminal1','2':'terminal2'},
   manufacturer_absolute_pin_numbering=False,
   manufacturer_exact_ordering_verified=False,exact_ordering_remaining='本批仅准确RC0805case厂家铜面；F/R/07/阻值/L订单解码及电气选型另核。')
 assets={
  'TPS7A4001DGNR':('tps7a4001.pdf',None,'63478c047e91a341a723bf4549689fb362a0fc9bf91e249db7e931e8b219e8a6'),
  'TPS37043DJOFDDFR':('tps3704.pdf',None,'2c191e129facf23a1f57fa351c47f4b8857aba1c04bc110166b64a5cd231b9cc'),
  'LM4040A50IDBZR':('LM4040A30IDBZR.pdf',None,'f43b6b6d3ecd51c8c90b70a7c4630c7e3140822b0073953ed2459df81b251c1c'),
  'TMUX1511PWR':('tmux1511.pdf',None,'c32b83722e3717c554dc8f68da05d9e02aa44087043d7b820f5e113713adbfcb'),
  'UPW2A471MHD':('Nichicon_PW.pdf',None,'8be66d99933e7589bc030a3417b3f6b3a6088523fa8ec09b637bf28ecf44b230'),
  'RSF500JT-73-200R':('YAGEO_RSF.pdf',None,'7c43489665a7e2848fcb4de40cb9ed51f173673c1eb6e49c0a7e0d89cca75694'),
  'LTC4368IMS-2#PBF':('ltc4368.pdf','codex-orderables-ec78b220c8fc467f95bb464b846e2565/ltc4368.pdf','8daaf750c3f6fa15be21f34fc785953c297fb82d71585e16500b9a04d918c09d'),
  'TPD2S300YFFR':('tpd2s300.pdf','codex-orderables-ec78b220c8fc467f95bb464b846e2565/tpd2s300.pdf','d1f89a59c7e19afb8bbfe5d51995ba47a9e191197587fe4e740e2e931fd53c04'),
  'LM5146RGYR':('LM5146Q1_RGY0020B厂家图.pdf','pcb-prelayout-LM5146Q1-RGY0020B-12f8be373500.pdf','12f8be37350023c37cc8477719c5ba86e0c42cf129e8430018f7b357a766b2b5'),
  'THN 15-4811WI':('THN15WI.pdf','pcb-prelayout-THN15WI-12cc102e9c38.pdf','12cc102e9c38c7f6ab50ba560aa05a6a685d50c52507133f96f735c71ef68d6c'),
  'THN 15-4812WI':('THN15WI.pdf','pcb-prelayout-THN15WI-12cc102e9c38.pdf','12cc102e9c38c7f6ab50ba560aa05a6a685d50c52507133f96f735c71ef68d6c'),
  '1777545':('Phoenix_1777545_厂家孔图2013.pdf','pcb-prelayout-1777545-factory-drawing-ad67c6d38cde.pdf','ad67c6d38cdefeb5bcf5e22acb6454f68aa1d82a1191e159cead7f34ed45be27'),
  'SPM10065VT-6R8M-D':('TDK_SPM10065VT_厂家20200702.pdf','TDK_VT_verified.pdf','abf552fefe0b7196e03cd5b21bc2026fd76f5711280ac7e9810b45d72da27f05'),
  'SPM10065VC-220M-D':('TDK_SPM10065VC_厂家20251217.pdf','TDK_VC_verified.pdf','92b7498cbe2029b8a61a73f6e09fecd8d3e33d2bab0cb14b1a93c10092dbacda'),
  'SMBJ12A':('Littelfuse_SMBJ_厂家2017机械图.pdf','Littelfuse_SMBJ_2017_verified.pdf','e33e2e68411f5a516252bb8363317f0da3e7c0094e150c0ee9e0b717c6a4c87b'),
  'SMBJ33A':('Littelfuse_SMBJ_厂家2017机械图.pdf','Littelfuse_SMBJ_2017_verified.pdf','e33e2e68411f5a516252bb8363317f0da3e7c0094e150c0ee9e0b717c6a4c87b'),
  'NVMFS6B25NLT1G':('NVMFS6B25NL_厂家2026.pdf',None,'28c7b339dff7c52bc4a1b6a012463e60e9fd44980239b14109d4c6b86f8966d8'),
  'NVMFS6B14NLT1G':('NVMFS6B14NL_厂家2026.pdf',None,'7ae07ce854385750f1ce5695e13343f47450626a62f7c37fff56b97492a1ba56'),
  'NVMFS6H800NLT1G':('NVMFS6H800NL_厂家2026.pdf',None,'b340f6342288e16701c0ee08c040bad94c7c9e645277f97fe03ad48ef669b6a8'),
  'BSS138-7-F':('Diodes_BSS138_厂家2024.pdf',None,'c93dcb33f41424e6a446a34f4222177b3a94e7dc27d2e2efb5e39eb245de3e17'),
  'PMV20XNER':('PMV20XNE_厂家.pdf',None,'ee38510a26efa8e5ecd27d80a426844435ae83b524b2f4cbd982e44a3cc3a390'),
  'BZT52H-A18X':('BZT52H-C15_115.pdf',None,'a5e54de45bdf1af712c2d9fdfb0fd092804cd83b26eb66e3656b12dea0c8b592'),
  '39-30-1020':('Molex_39301020_55690002SD_厂家RevA.pdf',None,'9f3d0bbbca473d6b6c045595f006914133de820daf76ff9c38b08b8cd27c5134'),
  'PSMN1R1-100CSE':('PSMN1R1-100CSE.pdf',None,'d382999798501f5ab433b9a90ac6c10c35e34b5371f493e4504ab653a2157cae'),
  'MPLAD30KP43AE3':('Microchip_MPLAD30KP.pdf',None,'f720f457e195410b7fa478f399d2c167061177cb8c18f180b1aada7004d717a5'),
  'BCX53-16,115':('BCX53_SER.pdf',None,'04f20158d054ccf4fa7bdc13a6540143c9eed829f875127bab25a4a4d4aa4f8c'),
  'BAS116,215':('BAS116.pdf',None,'91e10fe799c2f0803536da11c1f29991da8b3140d242b7777f14c214e3179f36'),
  'WSR58L000FEA':('Vishay_WSR5.pdf',None,'82e83849dae4e6c11018afd6870a7dd51385548fb6715f0bc776e2518ffafedd'),
  'WSR5R0200FEA':('Vishay_WSR5.pdf',None,'82e83849dae4e6c11018afd6870a7dd51385548fb6715f0bc776e2518ffafedd'),
  'WSR5R0500FEA':('Vishay_WSR5.pdf',None,'82e83849dae4e6c11018afd6870a7dd51385548fb6715f0bc776e2518ffafedd')}
 for m in ('C0805C822J1GACTU','C2220C334J1GACTU'):
  assets[m]=('KEM_C1003_C0G_SMD.pdf',None,'02d179914aeb9585eb2229ba8e18ef9d6b01c77c056de2af295d6950a2a5cc0d')
 for m in ('RC0805FR-0747RL','RC0805FR-073R3L'):
  assets[m]=('YAGEO_ChipResistor_Mounting.pdf',None,'591634ace247f61e9c6a263ca1ac98d7672fc163f5e87334c3460956f5c68b7b')
 for model,(filename,temporary,expected) in assets.items():
  if model not in models:continue
  dest=HW/'公共/数据手册'/filename
  if not dest.exists():
   assert temporary,'已有原厂手册缺失，不能无源生成'
   origin=Path(tempfile.gettempdir())/temporary;assert sha(origin)==expected
   shutil.copy2(origin,dest)
  assert sha(dest)==expected,(model,'原厂资料SHA不符，禁止覆写')
  specs[model].update(manufacturer_pdf=str(dest.relative_to(HW)),manufacturer_pdf_sha256=expected)
 if '1777545' in models:
  spec=specs['1777545'];dest=HW/spec['manufacturer_cad']
  if not dest.exists():
   origin=Path(tempfile.gettempdir())/'Phoenix1777545_factory_AP214.stp'
   assert sha(origin)==spec['manufacturer_cad_sha256'];shutil.copy2(origin,dest)
  assert sha(dest)==spec['manufacturer_cad_sha256']
 if 'LM5146RGYR' in models:
  assert sha(HW/'公共/数据手册/lm5146.pdf')=='830cbf80266d2542e187123fdb1f073104a4a71d9c10ec1d057120a44b0c693c'
  specs['LM5146RGYR']['nonQ1_electrical_pdf']={'file':'公共/数据手册/lm5146.pdf','sha256':'830cbf80266d2542e187123fdb1f073104a4a71d9c10ec1d057120a44b0c693c'}

def add_e4_reuse_specs(specs,models):
 """精确新版型号的几何复用；针功能来自原厂，制造仍未放行。"""
 def clone(model,baseline,**kw):
  if model not in models:return
  s=copy.deepcopy(specs[baseline]);s.update(kw);s.update(electrical_substitution=False,native_new_binding_readback='NOT_RUN_PENDING_E4',prefer_manufacturer_geometry=True)
  specs[model]=s
 def so8(model,pdf,functions,method):
  if model not in models:return
  specs[model]=dict(name='项目封装_TI_D0008A_原厂推荐',source='https://www.ti.com/lit/ds/symlink/'+pdf.lower(),
   manufacturer_pdf='公共/数据手册/'+pdf,manufacturer_pdf_sha256=sha(HW/'公共/数据手册'/pdf),method=method,
   pads=[dict(number=str(i+1),x_mm=-2.7,y_mm=-1.905+i*1.27,width_mm=1.55,height_mm=.6) for i in range(4)]+[dict(number=str(8-i),x_mm=2.7,y_mm=-1.905+i*1.27,width_mm=1.55,height_mm=.6) for i in range(4)],
   pin_functions=functions,manufacturer_landpattern_verified=True,prefer_manufacturer_geometry=True,electrical_substitution=False,
   native_new_binding_readback='NOT_RUN_PENDING_E4',manufacturing_released=False)
 if 'SM8S57A' in models:
  pdf=HW/'公共/数据手册/SM8S57A_Littelfuse_JC20250423_v2.pdf'
  assert sha(pdf)=='1827c56cf8493a585e6818a60c5df89e35a667c79d8f990204878938c45418cb'
  # Actual p4 recommended copper: one continuous T anode, not two
  # rectangles or a generic D2PAK/DO218 land. Origin is the land envelope
  # midpoint; y follows the manufacturer's drawing toward the small lead.
  anode=[[-5.25,-7.635],[5.25,-7.635],[5.25,-5.475],[4.445,-5.475],
         [4.445,1.535],[-4.445,1.535],[-4.445,-5.475],[-5.25,-5.475]]
  specs['SM8S57A']=dict(name='项目封装_Littelfuse_SMTO263_改脚_T形厂家铜',
   source='https://www.littelfuse.com/assetdocs/tvs-diode-sm8s-datasheet?assetguid=59636cd8-2d53-4eb3-b51b-1f5d4bf30c3e',
   manufacturer_pdf='公共/数据手册/SM8S57A_Littelfuse_JC20250423_v2.pdf',manufacturer_pdf_sha256=sha(pdf),
   manufacturer_pdf_mirror='https://datasheet.lcsc.com/datasheet/pdf/f3329d05d62fcc82fb5b5469c2433d72.pdf?productCode=C41550054',
   method='JC.04/23/25 v2 p2精确57A/p4推荐铜原图/p5阴极带实际目视；T头10.50x2.16、窄身8.89x7.01、小铜3.00x2.30、总长15.27；大铜与小铜间3.80',
   pads=[dict(number='1',x_mm=0,y_mm=6.485,width_mm=3,height_mm=2.30),
         dict(number='2',x_mm=0,y_mm=-3.05,width_mm=10.50,height_mm=9.17,shape='POLYGON',polygon_mm=anode)],
   pin_functions={'1':'K','2':'A'},manufacturer_absolute_pin_numbering=False,
   numbering_basis='原厂只有极性带没有绝对数字脚。项目1=靠阴极带的伸出小终端/小铜，2=另一端大T铜；当前TVS1接HV/LV高侧，2接BUS_MINUS。',
   manufacturer_landpattern_verified=True,geometry_orientation_verified=True,manufacturer_exact_ordering_verified=True,
   manufacturer_package_overall_max_mm=[10.67,15.24,4.78],manufacturer_paste_pattern_verified=False,
   outline_lines=[dict(start=[-1.75,4.90],end=[1.75,4.90],layer=3,width_mm=.12)],
   notes='p4 .81退台为(10.50-8.89)/2=.805的显示舍入；按10.50/8.89主尺寸落铜。单个T多边形同A网，无第三EP/NC铜。丝印线为项目K侧标识，不是厂家铜/壳外形。焊膏/阻焊/热铜与实际装配仍由layout工艺落实。',
   prefer_manufacturer_geometry=True,electrical_substitution=False,native_new_binding_readback='NOT_RUN_PENDING_E4',manufacturing_released=False)
 so8('REF5025EID','REF5025ID.pdf',dict(zip(map(str,range(1,9)),['EN','VIN','TEMP','GND','NR','VOUT','NC','DNC'])),
  '原厂SBOS410O p3 EI精确订单/p4独立增强EI针表；EN1不同于旧REF50 DNC1，p47 D0008A例铜仅同封装复用')
 # D and DGK share functions, not their package geometry.
 for model in ('INA241A2IDR','INA241A3IDR'):
  so8(model,'INA241A2IDGKR.pdf',{'1':'IN-','2':'GND','3':'REF2','4':'NC_RESERVED_GND','5':'OUT','6':'VS','7':'REF1','8':'IN+'},
   '原厂SBOSA30D p2/3 D及DGK针相同；p39 SOIC D0008A铜1.55x.6/P1.27/排5.4目视；不是DGK脚距')
  if model in specs:specs[model]['pin_requirements']={'4':'Reserved. Connect to ground.'}
 if 'INA241A2IDGKR' in models:
  clone('INA241A2IDGKR','INA241A1IDGKR',method='原厂SBOSA30D p2/3同族针表和p42 DGK铜；只复用DGK物理不替换增益')
 clone('CSS4J-4026K-2L00F','CSS4J-4026R-1L00F',body_height_max_mm=2.93,
  method='原厂CSS4J-4026 Rev01/26 p1精确K-2L00F/p2共同推荐铜面及K2L00高度2.93实际目视；同物理铜，材料/电阻/热额定仍单独',
  notes='厂家没有绝对1..4编号；项目1/2左右force、3/4同侧Kelvin。复用同系列共同推荐铜面，只高度上限改2.93；不继承R型电气额定。',
  pin_functions={'1':'terminal 1','2':'terminal 2','3':'terminal 3','4':'terminal 4'})
 clone('TMR1-1211','TMR1-1212',method='TMR1原厂2019 p1精确1211/p4 Single针1-VIN2+VIN4+VOUT6-VOUT，共用四脚物理；孔环工程选择，非厂家land',
  manufacturer_pdf='公共/数据手册/TMR1.pdf',manufacturer_pdf_sha256=sha(HW/'公共/数据手册/TMR1.pdf'),
  pin_functions={'1':'-VIN','2':'+VIN','4':'+VOUT','6':'-VOUT'},manufacturer_landpattern_verified=False)
 clone('C1210C104J5GACTU','C1210C104J1GACTU',method='KEMET C1003_C0G p1精确C/1210/104/J/5=50V/G/A/C/TU;p12常规1210密度B铜C1.50/Y1.15/X2.70目视；不继承100V厚度',
  manufacturer_pdf='公共/数据手册/KEM_C1003_C0G_SMD.pdf',manufacturer_pdf_sha256=sha(HW/'公共/数据手册/KEM_C1003_C0G_SMD.pdf'),
  notes='无极性项目1/2；铜面复用厂商共同1210密度B。不继承J1=100V的实体高度、3D、额定或温区资格。',pin_functions={'1':'terminal 1','2':'terminal 2'})
 if 'C1210C104J5GACTU' in specs:specs['C1210C104J5GACTU'].pop('机械尺寸_mm',None)
 clone('WSL2512R1000FEA','WSL2512R0200FEA',method='原厂Doc30100 p2 WSL2512 .007至.5ohm共同厂家铜面；.1ohm位于范围，不继承.02ohm热预算',pin_functions={'1':'terminal 1','2':'terminal 2'})
 # RNCF0805 now has exact Stackpole C346562 geometry; same-case family reuse below avoids a second inferred footprint.
 if 'TLP2361(TPL,E)' in models:
  specs['TLP2361(TPL,E)']=dict(name='项目封装_Toshiba_11_4L1S_五实体脚_厂家参考铜',
   source='https://toshiba.semicon-storage.com/us/semiconductor/design-development/package/detail.5pin%20SO6.html',
   manufacturer_pdf='公共/数据手册/TLP2361_厂家20260407.pdf',manufacturer_pdf_sha256=sha(HW/'公共/数据手册/TLP2361_厂家20260407.pdf'),
   manufacturer_land_image='公共/数据手册/Toshiba_11-4L1S_参考焊盘.gif',manufacturer_land_image_sha256=sha(HW/'公共/数据手册/Toshiba_11-4L1S_参考焊盘.gif'),
   method='官方11-4L1S原厂20260407 p16实体1/3/4/5/6及官网参考GIF目视；铜.8x1.2/P1.27/排距6.3，不添加无脚2',
   pads=[dict(number=str(n),x_mm=x,y_mm=y,width_mm=.8,height_mm=1.2) for n,x,y in [(1,-1.27,3.15),(3,1.27,3.15),(4,1.27,-3.15),(5,0,-3.15),(6,-1.27,-3.15)]],
   pin_functions={'1':'LED A','3':'LED K','4':'GND','5':'VO','6':'VCC'},manufacturer_landpattern_verified=True,
   prefer_manufacturer_geometry=True,electrical_substitution=False,native_new_binding_readback='NOT_RUN_PENDING_E4',manufacturing_released=False)
 if 'LTV-817C' in models:
  specs['LTV-817C']=dict(name='项目封装_LiteOn_LTV817_DIP4_工程孔环',source='https://optoelectronics.liteon.com/upload/download/DS70-2009-0035/LTV-817.pdf',
   manufacturer_pdf='公共/数据手册/LiteOn_LTV8x7_原厂系列图.pdf',manufacturer_pdf_sha256=sha(HW/'公共/数据手册/LiteOn_LTV8x7_原厂系列图.pdf'),
   method='LiteOn LTV8x7原厂系列图p3 LTV817(不带M/S)实际目视；7.62列/2.54节距；C为rank不是脚形',
   pads=[dict(number=str(n),x_mm=x,y_mm=y,width_mm=2,height_mm=2,drill_mm=1.2,shape='RECT' if n==1 else 'ELLIPSE') for n,x,y in [(1,-1.27,3.81),(2,1.27,3.81),(3,1.27,-3.81),(4,-1.27,-3.81)]],
   pin_functions={'1':'LED A','2':'LED K','3':'phototransistor E','4':'phototransistor C'},manufacturer_landpattern_verified=False,
   manufacturer_body_and_lead_verified=True,prefer_manufacturer_geometry=True,electrical_substitution=False,manufacturing_released=False,
   project_drill_conditions='1.2成品孔/2mm铜为工程选择；脚.5±.1/.26、p2.54±.25与列7.62..9.98须成形装配；非厂家孔环保证',native_new_binding_readback='NOT_RUN_PENDING_E4')
 if 'EEUFC2A221' in models:
  specs['EEUFC2A221']=dict(name='项目封装_Panasonic_FC_D16_P7p5_工程孔环',
   source='https://industrial.panasonic.com/ww/products/pt/aluminum-cap-lead/models/EEUFC2A221',
   method='精确型号官方polar径向D16/L25/P7.5；脚径.8mm，铜孔为项目候选；不继承其他容量/高度',
   pads=[dict(number=str(i+1),x_mm=x,y_mm=0,width_mm=3,height_mm=3,drill_mm=1.3,shape='RECT' if i==0 else 'ELLIPSE') for i,x in enumerate((-3.75,3.75))],
   pin_functions={'1':'positive','2':'negative'},pin_function_aliases={'1':['terminal 1','+'],'2':['terminal 2','-']},
   numbering_basis='厂家无数字脚；项目1正2负，负极本体条纹对应2，装配须对号',
   manufacturer_landpattern_verified=False,manufacturer_body_and_lead_verified=True,prefer_manufacturer_geometry=True,electrical_substitution=False,
   body_diameter_max_mm=16.5,body_length_max_mm=27,project_drill_conditions='1.3孔/3铜为工程选择，不宣称厂家推荐或插装已实测',native_new_binding_readback='NOT_RUN_PENDING_E4',manufacturing_released=False)
  if 'SN74AC07PWR' in models:
   ac07=copy.deepcopy(specs['TMUX1511PWR'])
   ac07.update(source='https://www.ti.com/product/SN74AC07/part-details/SN74AC07PWR',
    method='TI SN74AC07官方数据手册PW14逐针及PW package dimensions；复用本库已核PW0014A推荐铜面，不复用TMUX电气功能；左1..7、右14..8、P0.65',
    pin_functions={'1':'1A','2':'1Y','3':'2A','4':'2Y','5':'3A','6':'3Y','7':'GND',
                   '8':'4Y','9':'4A','10':'5Y','11':'5A','12':'6Y','13':'6A','14':'VCC'},
    manufacturer_pdf_url='https://www.ti.com/lit/ds/symlink/sn74ac07.pdf',
    manufacturer_package_body_mm=[4.5,5.1,1.2],
    notes='精确订购型号SN74AC07PWR为PW TSSOP-14；复用已核PW0014A铜面而非套用旧电气符号。无EP；三个开漏缓冲及闲置管脚由源逐脚映射。制造/装配与整板资格另验。')
   for key in ('manufacturer_pdf','manufacturer_pdf_sha256'):
    ac07.pop(key,None)
   specs['SN74AC07PWR']=ac07
  if 'UHW2A471MHD' in models:
   specs['UHW2A471MHD']=dict(name='项目封装_Nichicon_UHW2A471MHD_D12p5_P5_工程孔环',
    source='https://www.nichicon.com/en-us/part/uhw2a471mhd/6256/',
    manufacturer_pdf_url='https://www.nichicon.com/getmedia/fcd51685-9bcf-4441-98c2-6ed79a71564f/e-uhw5-11.pdf',
    method='Nichicon CAT.8100O p5精确UHW2A471MHD=470uF、12.5x40mm、2.86Arms；p0尺寸图：P=5±0.5，φ12.5且L>25脚径0.8mm；MHD6为18x25而非本型号。原厂未指定PCB铜land，采用项目孔环。',
    pads=[dict(number='1',x_mm=-2.5,y_mm=0,width_mm=2.4,height_mm=2.4,drill_mm=1.0,shape='ELLIPSE'),
          dict(number='2',x_mm=2.5,y_mm=0,width_mm=2.4,height_mm=2.4,drill_mm=1.0,shape='ELLIPSE')],
    pin_functions={'1':'positive','2':'negative'},numbering_basis='厂家径向电容无数字脚；继承当前电气源明确1=positive、2=negative，装配以本体负极条纹核对2。',
    manufacturer_landpattern_verified=False,manufacturer_body_and_lead_verified=True,
    manufacturer_exact_ordering_verified=True,manufacturer_case_size_nominal_mm=[12.5,40],
    manufacturer_lead_spacing_mm=5.0,manufacturer_lead_spacing_tolerance_mm=0.5,
    manufacturer_lead_diameter_mm=0.8,prefer_manufacturer_geometry=True,electrical_substitution=False,
    project_drill_conditions='1.0mm成品孔/2.4mm圆铜盘是工程选择；按厂家0.8mm引脚留装配间隙，不宣称厂家推荐land、装配或制板已通过。',
    native_new_binding_readback='NOT_RUN_PENDING_E4',manufacturing_released=False,
    notes='只绑定精确MHD本体和P5两针；不得混用MHD6尺寸/脚距。两只共用同封装，热/纹波资格仍按系统负载另验。')
  for model in ('43650-0215','43650-0217'):
   if model not in models:continue
   part='436500215' if model.endswith('0215') else '436500217'
   specs[model]=dict(name='项目封装_Molex_43650_0215_0217_2P_Vertical',
    source='https://www.molex.com/en-us/products/part-detail/'+part,
    manufacturer_drawing_url='https://www.molex.com/content/dam/molex/molex-dot-com/products/automated/en-us/salesdrawingpdf/436/43650/436500215_sd.pdf?inline=',
    geometry_reference_url='https://raw.githubusercontent.com/KiCad/kicad-footprints/master/Connector_Molex.pretty/Molex_Micro-Fit_3.0_43650-0215_1x02_P3.00mm_Vertical.kicad_mod',
    method='Molex SD-43650-001精确0215 2CKT竖直带PCB定位peg图；官网料号页核对0215/0217均2回路、P3、Vertical、kinked THT。KiCad库引用同一Molex drawing并明确0216/0217为兼容替代，孔/peg几何据此复核：P3、引脚孔1.02、双定位孔1.27、peg跨距9.0mm。铜盘是项目选择。',
    pads=[dict(number='1',x_mm=-1.5,y_mm=0,width_mm=1.5,height_mm=2.02,drill_mm=1.02,shape='ELLIPSE'),
          dict(number='2',x_mm=1.5,y_mm=0,width_mm=1.5,height_mm=2.02,drill_mm=1.02,shape='ELLIPSE')],
    pin_functions={'1':'terminal 1','2':'terminal 2'},
    nonplated_holes=[dict(x_mm=-4.5,y_mm=-1.96,diameter_mm=1.27),dict(x_mm=4.5,y_mm=-1.96,diameter_mm=1.27)],
    manufacturer_landpattern_verified=False,manufacturer_hole_pattern_verified=True,
    manufacturer_exact_ordering_verified=True,manufacturer_body_and_lead_verified=True,
    geometry_orientation_verified=True,prefer_manufacturer_geometry=True,electrical_substitution=False,
    manufacturer_pin_pitch_mm=3.0,manufacturer_peg_spacing_mm=9.0,
    manufacturer_pin_hole_diameter_mm=1.02,manufacturer_peg_hole_diameter_mm=1.27,
    compatible_geometry_models=['43650-0215','43650-0216','43650-0217'],
    project_copper_conditions='2.02mm长圆孔铜盘/1.02mm孔及1.27mm NPTH定位孔几何按原厂图；铜环/阻焊及制板孔公差须由layout落实，未声明工艺放行。',
    native_new_binding_readback='NOT_RUN_PENDING_E4',manufacturing_released=False,
    notes='项目源接触1=SC_MAINT_OK、2=BUS_MINUS；机械peg仅NPTH，不造电气pad。0215/0217表面镀层差异保留在完整料号身份中。')


def source_to_physical_pad(part,spec):
 """显式逻辑别名只能共用同一物理铜和同一源网，不能制造第二块D铜。"""
 pads={str(x['number']) for x in spec['pads']}
 mapping=spec.get('source_pin_to_pad') or {n:n for n in pads}
 assert set(mapping)==set(part['pins']) and set(mapping.values())==pads,(part['ref'],'源/物理针集合不匹配')
 groups=collections.defaultdict(list)
 for n,target in mapping.items():groups[target].append(n)
 for target,numbers in groups.items():
  assert len({part['pins'][n] for n in numbers})==1,(part['ref'],'同一物理铜别名在源中异网',target,numbers)
 for group in spec.get('internally_common_pins',[]):
  numbers=[n for n,target in mapping.items() if target in group]
  assert numbers and len({part['pins'][n] for n in numbers})==1,(part['ref'],'封装内共接引脚在板源中异网',group)
 return mapping

def bind(c):
 raw=raw_objects();blobs=archive(LIB/'可导入封装库.zip');supp=read(LIB/'封装补充依据.json')
 tools=module('补齐封装');template=json.loads(next(v for n,v in blobs.items() if n.endswith('.json')))
 specs=copy.deepcopy(supp['footprints'])
 specs.update(copy.deepcopy(supp.get('板级集成厂家封装',{})))
 # 已目视核对厂家PDF的同系列推荐焊盘；不由外形猜焊盘。
 for m in {p['mpn'] for p in c['parts']}:
  if m.startswith('XGL1313-'):
   specs[m]={'name':'项目封装_XGL1313_厂家推荐','source':'公共/数据手册/XGL1313.pdf',
    'method':'本地原厂XGL1313.pdf Doc1730-3 2026-02-19第3页目视核对',
    'manufacturer_pdf_sha256':sha(HW/'公共/数据手册/XGL1313.pdf'),
    'pads':[dict(number=str(i+1),x_mm=x,y_mm=0,width_mm=2.98,height_mm=11.2) for i,x in enumerate((-4.3,4.3))],
    'outline_lines':[dict(start=a,end=b,layer=13) for a,b in [((-6.7,-7.5),(6.7,-7.5)),((6.7,-7.5),(6.7,7.5)),((6.7,7.5),(-6.7,7.5)),((-6.7,7.5),(-6.7,-7.5))]],
    'notes':'PCB俯视、左1右2为项目编号；原厂标点指示绕组起始端，低dv/dt端由板作者复核；无极性。'}
  elif m.startswith('TNPW1206'):
   specs[m]={'name':'项目封装_TNPW1206_IPC回流','source':'https://www.vishay.com/doc?28950',
    'method':'TNPW Doc31006 p8明确引用Doc28950 p1 IPC回流1206：G1.75 Y1.15 X1.8 Z4.05mm',
    'manufacturer_pdf_sha256':sha(HW/'公共/数据手册/Vishay_ChipResistor_Pads.pdf'),
    'pads':[dict(number=str(i+1),x_mm=x,y_mm=0,width_mm=1.15,height_mm=1.8) for i,x in enumerate((-1.45,1.45))],
    'notes':'两端无极性；左1右2为项目编号；未覆盖本板散热、爬电/间距及工艺。'}
 # Complete exact MPN packages from inspected manufacturer drawings, not
 # similarly named packages or the board's own connection table.
 for m,pdf,pin_page,page,functions in (
  ('INA240A2D','INA240.pdf',3,34,{'1':'IN−','2':'GND','3':'REF2','4':'NC','5':'OUT','6':'VS','7':'REF1','8':'IN+'}),
  ('INA240A2DR','INA240.pdf',3,34,{'1':'IN−','2':'GND','3':'REF2','4':'NC','5':'OUT','6':'VS','7':'REF1','8':'IN+'}),
  ('INA240A4DR','INA240.pdf',3,34,{'1':'IN−','2':'GND','3':'REF2','4':'NC','5':'OUT','6':'VS','7':'REF1','8':'IN+'}),
  ('INA149AID','ina149.pdf',5,24,{'1':'REFB','2':'−IN','3':'+IN','4':'V−','5':'REFA','6':'VOUT','7':'V+','8':'NC'}),
  ('PCA9536DR','PCA9536.pdf',3,33,{'1':'P0','2':'P1','3':'P2','4':'GND','5':'P3','6':'SCL','7':'SDA','8':'VCC'}),
  ('PCA9536D','PCA9536.pdf',3,33,{'1':'P0','2':'P1','3':'P2','4':'GND','5':'P3','6':'SCL','7':'SDA','8':'VCC'})):
  if m not in {p['mpn'] for p in c['parts']}:continue
  geometry_mpn=m[:-1] if m.endswith('DR') else m
  if m=='INA240A4DR':geometry_mpn='INA240A2D'  # 同一D0008A几何，不替换增益型号。
  specs[m]={'name':'项目封装_'+geometry_mpn+'_TI_D0008A','source':'https://www.ti.com/lit/ds/symlink/'+pdf.lower(),
   'method':f'厂家PDF物理p{pin_page}逐针及p{page} D0008A推荐焊盘目视核对：1.55×0.60mm、1.27mm节距、两排中心5.4mm',
   'manufacturer_pdf':'公共/数据手册/'+pdf,'manufacturer_pdf_sha256':sha(HW/'公共/数据手册'/pdf),
   'manufacturer_landpattern_verified':True,'pin_functions':functions,
   'pads':[dict(number=str(i+1),x_mm=-2.7,y_mm=-1.905+i*1.27,width_mm=1.55,height_mm=.6) for i in range(4)]+
          [dict(number=str(8-i),x_mm=2.7,y_mm=-1.905+i*1.27,width_mm=1.55,height_mm=.6) for i in range(4)],
   'notes':'PCB顶视针1左上；同几何不代表同针功能或电气型号，逐型号核对；禁止套用INA240 PW的TSSOP针号；制造装配另验。'}
 for m in {p['mpn'] for p in c['parts']}:
  if m in ('INA241A1IDGKR','INA241A4IDGKR','INA241A5IDGKR'):
   specs[m]={'name':'项目封装_INA241_DGK0008A_厂家推荐','source':'https://www.ti.com/lit/ds/symlink/ina241a.pdf',
    'method':'INA241A/B SBOSA30D原厂PDF p2/3同系列逐针、p41/42 DGK0008A轮廓及推荐焊盘目视核对；八脚无额外热垫',
    'manufacturer_pdf':'公共/数据手册/INA241A2IDGKR.pdf','manufacturer_pdf_sha256':sha(HW/'公共/数据手册/INA241A2IDGKR.pdf'),
    'manufacturer_landpattern_verified':True,
    'pin_functions':{'1':'IN−','2':'GND','3':'REF2','4':'NC_RESERVED_GND','5':'OUT','6':'VS','7':'REF1','8':'IN+'},
    'pin_requirements':{'4':'Reserved. Connect to ground.'},'pin_function_aliases':{'4':['RESERVED_GND']},
    'pads':[dict(number=str(i+1),x_mm=-2.2,y_mm=-.975+i*.65,width_mm=1.4,height_mm=.45) for i in range(4)]+
           [dict(number=str(8-i),x_mm=2.2,y_mm=-.975+i*.65,width_mm=1.4,height_mm=.45) for i in range(4)],
    'notes':'PCB顶视针1左上；A4/A5只复用物理DGK几何，不替换增益；针4须接本地GND，PCB间距及热条件另验。'}
  elif m=='XAL8080-153MED':
   specs[m]={'name':'项目封装_XAL8080_厂家推荐','source':'https://www.coilcraft.com/getmedia/345e50d6-a804-4ecb-9a92-5185221faf3e/xal8080.pdf',
    'method':'Doc839-2 2026-05-01 p3推荐焊盘目视核对：宽1.78mm、高7.0mm、中心距5.16mm',
    'manufacturer_pdf':'公共/数据手册/XAL8080.pdf','manufacturer_pdf_sha256':sha(HW/'公共/数据手册/XAL8080.pdf'),
    'manufacturer_landpattern_verified':True,
    'pads':[dict(number=str(i+1),x_mm=x,y_mm=0,width_mm=1.78,height_mm=7.0) for i,x in enumerate((-2.58,2.58))],
    'outline_lines':[dict(start=a,end=b,layer=13) for a,b in [((-4.15,-4.4),(4.15,-4.4)),((4.15,-4.4),(4.15,4.4)),((4.15,4.4),(-4.15,4.4)),((-4.15,4.4),(-4.15,-4.4))]],
    'notes':'两端无极性，针号1左2右为项目编号；绕组短引线标点/高dvdt端由电气作者复核；不证明热额定。'}
  elif m=='AC03000001001JAC00':
   specs[m]={'name':'项目封装_AC03_轴向20mm','source':'https://www.vishay.com/docs/28730/ac_ac-at_ac-ni.pdf',
    'method':'Doc28730 2024-12-05 p2中性直引线型号、p10最大体长13mm/直径4.8mm/线径0.80±0.03mm；项目20mm弯脚孔距',
    'manufacturer_pdf':'公共/数据手册/Vishay_AC.pdf','manufacturer_pdf_sha256':sha(HW/'公共/数据手册/Vishay_AC.pdf'),
    'manufacturer_landpattern_verified':False,'manufacturer_body_and_lead_verified':True,
    'pads':[dict(number=str(i+1),x_mm=x,y_mm=0,width_mm=2,height_mm=2,drill_mm=1) for i,x in enumerate((-10,10))],
    'outline_lines':[dict(start=a,end=b,layer=13) for a,b in [((-6.5,-2.4),(6.5,-2.4)),((6.5,-2.4),(6.5,2.4)),((6.5,2.4),(-6.5,2.4)),((-6.5,2.4),(-6.5,-2.4))]],
    'notes':'中性直引线件需装配时按20mm孔距弯脚；孔径1mm/铜环2mm是项目工艺选择，非厂家指定焊盘。留出升高/散热空间，热边界另验。'}
  elif m=='43045-0400':
   specs[m]={'name':'项目封装_Molex_43045_0400_厂家孔位_NPTH','source':'https://www.molex.com/content/dam/molex/molex-dot-com/products/automated/en-us/salesdrawingpdf/430/43045/430450400_sd.pdf',
    'method':'Molex SD-43045-001 RevB原厂扫描图p1目视核对；官网RevH1文本同4针孔位：双排3mm，信号孔1.02mm，单NPTH3mm，针1排到定位孔4.32mm',
    'manufacturer_pdf':'公共/数据手册/Molex_43045_family.pdf','manufacturer_pdf_sha256':sha(HW/'公共/数据手册/Molex_43045_family.pdf'),
    'manufacturer_pdf_mirror':'https://www.official.cz/static/_dokumenty/1/3/5/2/9/430451200_sd.pdf',
    'manufacturer_landpattern_verified':False,'manufacturer_hole_pattern_verified':True,
    'pin_functions':{str(n):str(n) for n in range(1,5)},
    'pads':[dict(number=str(n),x_mm=x,y_mm=y,width_mm=2,height_mm=2,drill_mm=1.02,shape='RECT' if n==1 else 'ELLIPSE')
            for n,x,y in [(1,1.5,1.5),(2,-1.5,1.5),(3,1.5,-1.5),(4,-1.5,-1.5)]],
    'nonplated_holes':[dict(x_mm=0,y_mm=5.82,diameter_mm=3)],
    'notes':'元件侧顶视编号来自厂家4 CKT图；铜环2mm是工程选择，厂家明确孔径/孔位。直角座壳体及靠板边10.16mm限制由PCB设计落实；无端子NC触点仍保留实体焊盘。'}
 # GH top-entry geometry is independently read from JST eGH p2/3.
 # Reinforcement numbers are project CAD identifiers, not extra contacts.
 for count in (2,3,4,5,8,10,11):
  m=f'BM{count:02d}B-GHS-TBT(LF)(SN)'
  if m not in {p['mpn'] for p in c['parts']}:continue
  half=(count-1)*1.25/2
  specs[m]={'name':f'项目封装_JST_GH_BM{count:02d}_顶入_原厂推荐焊盘',
   'source':'https://www.jst-mfg.com/product/pdf/eng/eGH.pdf',
   'method':'JST eGH原厂PDF p2安装面推荐图/p3 BM型号表目视核对；非SM侧入式',
   'manufacturer_pdf':'公共/数据手册/SM05B-GHS-TB_LF_SN.pdf',
   'manufacturer_pdf_sha256':sha(HW/'公共/数据手册/SM05B-GHS-TB_LF_SN.pdf'),
   'manufacturer_landpattern_verified':True,'prefer_manufacturer_geometry':True,
   'pin_functions':{**{str(n):str(n) for n in range(1,count+1)},
                    str(count+1):'MECHANICAL_NC',str(count+2):'MECHANICAL_NC'},
   'mechanical_nc_numbers':[str(count+1),str(count+2)],
   'pads':[dict(number=str(n),x_mm=half-(n-1)*1.25,y_mm=0,width_mm=.6,height_mm=1.7)
           for n in range(1,count+1)]+
          [dict(number=str(n),x_mm=x,y_mm=3.35,width_mm=1,height_mm=2.8)
           for n,x in ((count+1,-half-1.85),(count+2,half+1.85))],
   'notes':'PCB安装面：信号排上、固定片下，针1最右；固定片左N+1/右N+2为项目CAD号，必须NC，不替代厂家触点编号。信号0.6×1.7/固定片1×2.8mm；总Y跨距5.6mm；厂家标注尺寸为参考值。仅厂家推荐焊盘，不凭焊盘猜壳体轮廓，不声明自动庭院/3D/工艺及整板放行。'}
 if 'CSS4J-4026R-1L00F' in {p['mpn'] for p in c['parts']}:
  shunt=copy.deepcopy(specs['CSS4J-4026R-1L00F'])
  assert shunt['name']=='项目封装_四端采样电阻_CSS4J4026' and len(shunt['pads'])==4
  shunt.update(manufacturer_pdf='公共/数据手册/CSS4J-4026.pdf',
   manufacturer_pdf_sha256=sha(HW/'公共/数据手册/CSS4J-4026.pdf'),
   method='Bourns CSS4J-4026 Rev01/26 p1完整1L00F型号/p2四端推荐焊盘及1L00x Hmax2.70mm目视核对；不套用L200x 4.00mm',
   body_height_max_mm=2.70,model_variant_dimension_verified=True,
   manufacturer_landpattern_verified=True,prefer_manufacturer_geometry=True,
   native_new_binding_readback='NOT_RUN_PENDING_SHARED_LIBRARY_BATCH')
  shunt['notes']=shunt['notes'].replace('同系列1mΩ器件高度上限4.00mm','本型号1mΩ器件高度上限2.70mm；4.00mm只属于L200x')
  shunt['numbering_basis']='厂家未编号；项目1/2为左右force大焊盘、3/4为左右Kelvin小焊盘。针功能项目分配须源端及原生回读独立核对，不伪称厂家1..4。'
  specs['CSS4J-4026R-1L00F']=shunt
 for model,pdf,land_page,functions in (
  ('SN74AHCT1G32DBVR','sn74ahct1g32.pdf',17,{'1':'A','2':'B','3':'GND','4':'Y','5':'VCC'}),
  ('SN74LVC1G07DBVR','sn74lvc1g07.pdf',37,{'1':'NC','2':'A','3':'GND','4':'Y','5':'VCC'}),
  ('SN74LVC1G06DBVR','sn74lvc1g06.pdf',25,{'1':'NC','2':'A','3':'GND','4':'Y','5':'VCC'})):
  if model not in {p['mpn'] for p in c['parts']}:continue
  # Reuse only manufacturer-proven DBV0005A copper geometry, not the
  # electrical function of a different device in the same package.
  base=copy.deepcopy(specs['SN74LVC1G14DBVR'])
  assert base['name']=='项目封装_TI_DBV0005A_原厂推荐' and len(base['pads'])==5
  base.update(source='https://www.ti.com/lit/ds/symlink/'+pdf,
   method=f'独立厂家PDF p3 DBV逐针/p{land_page} DBV0005A 4214839/K 08/2024推荐铜面目视核对；完整DBVR订购型号在原厂表中；复用已核同几何而非换逻辑型号',
   manufacturer_pdf='公共/数据手册/'+pdf,
   manufacturer_pdf_sha256=sha(HW/'公共/数据手册'/pdf),
   pin_functions=functions,prefer_manufacturer_geometry=True,
   electrical_substitution=False,native_new_binding_readback='NOT_RUN_PENDING_SHARED_LIBRARY_BATCH')
  if model in ('SN74LVC1G07DBVR','SN74LVC1G06DBVR'):
   base['pin_function_aliases']={'4':['Y_OPEN_DRAIN']}
   base['output_qualification']='原厂Y为开漏输出；1G07同相缓冲、1G06反相，不互相替代；Y_OPEN_DRAIN仅此已核型号的功能注记别名'
  specs[model]=base
 # Newly added protection/proof parts: verify the exact MPN pin diagram and
 # package option before reusing copper from an independently read TI drawing.
 for model,pdf,pin_page,land_page,functions in (
  ('TPS7B6950QDBVRQ1','tps7b69-q1.pdf',3,21,{'1':'IN','2':'NC','3':'GND','4':'GND','5':'OUT'}),
  ('TLV3601DBVR','tlv3601.pdf',3,37,{'1':'OUT','2':'VEE','3':'IN+','4':'IN−','5':'VCC'})):
  if model not in {p['mpn'] for p in c['parts']}:continue
  spec=copy.deepcopy(specs['SN74LVC1G14DBVR'])
  assert spec['name']=='项目封装_TI_DBV0005A_原厂推荐' and len(spec['pads'])==5
  spec.update(source='https://www.ti.com/lit/ds/symlink/'+pdf,
   manufacturer_pdf='公共/数据手册/'+pdf,
   manufacturer_pdf_sha256=sha(HW/'公共/数据手册'/pdf),
   method=f'精确型号原厂订购表及p{pin_page}针脚/p{land_page} DBV0005A 4214839/K 08/2024原图目视核对；只复用同推荐铜面，不替换型号或针功能',
   pin_functions=functions,prefer_manufacturer_geometry=True,electrical_substitution=False,
   native_new_binding_readback='NOT_RUN_PENDING_SHARED_LIBRARY_BATCH')
  spec.pop('pin_function_aliases',None)
  specs[model]=spec
 if 'TLV9002IDR' in {p['mpn'] for p in c['parts']}:
  specs['TLV9002IDR']={'name':'项目封装_TI_D0008A_原厂推荐',
   'source':'https://www.ti.com/lit/ds/symlink/tlv9002.pdf',
   'manufacturer_pdf':'公共/数据手册/tlv9002.pdf',
   'manufacturer_pdf_sha256':sha(HW/'公共/数据手册/tlv9002.pdf'),
   'method':'原厂物理p8 TLV9002 D逐针/p41 TLV9002IDR SOIC(D)订购表/p88 D0008A 4214825/C 02/2019推荐铜面目视核对；不套用DSG裸焊盘或PW针间距',
   'pin_functions':{'1':'OUT1','2':'IN1−','3':'IN1+','4':'V−','5':'IN2+','6':'IN2−','7':'OUT2','8':'V+'},
   'pin_function_aliases':{'1':['OUTA'],'2':['INA−'],'3':['INA+'],'5':['INB+'],'6':['INB−'],'7':['OUTB']},
   'pads':[dict(number=str(i+1),x_mm=-2.7,y_mm=-1.905+i*1.27,width_mm=1.55,height_mm=.6) for i in range(4)]+
          [dict(number=str(8-i),x_mm=2.7,y_mm=-1.905+i*1.27,width_mm=1.55,height_mm=.6) for i in range(4)],
   'manufacturer_landpattern_verified':True,'prefer_manufacturer_geometry':True,
   'body_height_max_mm':1.75,'manufacturer_pad_corner_radius_mm':.05,
   'native_new_binding_readback':'NOT_RUN_PENDING_SHARED_LIBRARY_BATCH','electrical_substitution':False,
   'notes':'PCB顶视1左上；OUT1/IN1对应项目A通道、OUT2/IN2对应B，别名仅通道标记。无第9热焊盘；当前铜面采用推荐矩形包络，原图R0.05圆角及阻焊/钢网工艺仍须落实，不声明庭院/3D/制造或整板放行。'}
 if 'TLV809EA30DBZR' in {p['mpn'] for p in c['parts']}:
  specs['TLV809EA30DBZR']={'name':'项目封装_TI_DBZ0003A_原厂推荐',
   'source':'https://www.ti.com/lit/ds/symlink/tlv803e.pdf',
   'manufacturer_pdf':'公共/数据手册/TLV803EA30DBZR.pdf',
   'manufacturer_pdf_sha256':sha(HW/'公共/数据手册/TLV803EA30DBZR.pdf'),
   'method':'原厂物理p3命名/p4默认DBZ针1GND/p5功能/p31完整订购型号/p40 DBZ0003A 4214838/F 08/2024推荐铜面目视核对；不混R/V针序变体及DCK/DPW',
   'pin_functions':{'1':'GND','2':'RESET','3':'VDD'},'pin_function_aliases':{'2':['RESET_N']},
   'pads':[dict(number=n,x_mm=x,y_mm=y,width_mm=1.3,height_mm=.6)
           for n,x,y in [('1',-1.05,-.95),('2',-1.05,.95),('3',1.05,0)]],
   'manufacturer_landpattern_verified':True,'prefer_manufacturer_geometry':True,
   'body_height_max_mm':1.12,'manufacturer_pad_corner_radius_mm':.05,
   'native_new_binding_readback':'NOT_RUN_PENDING_SHARED_LIBRARY_BATCH','electrical_substitution':False,
   'notes':'完整型号为推挽低有效复位、默认DBZ针1GND/2RESET/3VDD；尾部DBZR的R为包装，不是阈值前R针序变体。当前铜面采用推荐矩形包络，R0.05圆角/阻焊/钢网及庭院/3D未作为工艺放行；器件额定及整板资格另验。'}
 # Exact four-MPN delta: source roles are application annotations, never
 # invented manufacturer contacts. Through-hole lands are project choices.
 models={p['mpn'] for p in c['parts']}
 if 'IXTH140P10T' in models:
  specs['IXTH140P10T']={'name':'项目封装_IXTH_TO247_项目孔径2p4_P5p46',
   'source':'https://www.littelfuse.com/assetdocs/littelfuse-discrete-mosfets-ixt-140p10t-datasheet?assetguid=95e755d2-ac37-4694-bdef-2a410a93c143',
   'manufacturer_pdf':'公共/数据手册/IXTH140P10T.pdf',
   'manufacturer_pdf_sha256':sha(HW/'公共/数据手册/IXTH140P10T.pdf'),
   'method':'DS100371B(01/13) p1完整IXTH型号/p2下部TO-247正面1G/2D/3S、Tab同D、e5.2至5.72mm及矩形脚最大1.4×0.8mm目视核对；不套TO-268',
   'pin_functions':{'1':'G','2':'D','3':'S'},'pin_function_aliases':{'2':['D and tab']},
   'manufacturer_landpattern_verified':False,'manufacturer_body_and_lead_verified':True,
   'prefer_manufacturer_geometry':True,'electrical_substitution':False,
   'pads':[dict(number=str(i+1),x_mm=x,y_mm=0,width_mm=4,height_mm=4,drill_mm=2.4,shape='ELLIPSE') for i,x in enumerate((-5.46,0,5.46))],
   'project_drill_conditions':{'finished_hole_mm':2.4,'hole_tolerance_mm':.05,'hole_position_axis_tolerance_mm':.03,
    'lead_section_max_mm':[1.4,.8],'pitch_range_mm':[5.2,5.72],'outer_lead_pitch_offset_max_mm':.26,
    'conservative_corner_radius_mm':((.7+.26+.03)**2+(.4+.03)**2)**.5,
    'minimum_hole_radius_mm':1.175,'minimum_nominal_annular_ring_mm':.775,
    'qualification':'工程孔径/铜环及要求的工艺条件，非厂家推荐landpattern；需控制居中与孔位，引脚保持未额外变形；装配与钻孔偏差超此条件须重核，不宣称工艺已实测。'},
   'manufacturer_package_D_max_mm':21.46,'native_new_binding_readback':'NOT_RUN_PENDING_SHARED_LIBRARY_BATCH',
   'notes':'正面器件竖装、脚向下时1左2中3右；Tab为D，不加第四电气针。Ø3.55至3.65是金属本体安装孔，不生成PCB第四焊盘或NPTH；壳体/散热安装与PCB机械布局由人类落实；不伪造庭院/3D或热额定。'}
 if 'RT2010FKE0715KL' in models:
  specs['RT2010FKE0715KL']={'name':'项目封装_YAGEO_RT2010_原厂回流铜面',
   'source':'https://www.yageogroup.com/content/Resource%20Library/Product%20Guide-Catalog/yageo_PYu-R_Mount_10_19050818_343.pdf',
   'manufacturer_pdf':'公共/数据手册/YAGEO_ChipResistor_Mounting.pdf',
   'manufacturer_pdf_sha256':sha(HW/'公共/数据手册/YAGEO_ChipResistor_Mounting.pdf'),
   'manufacturer_ordering_pdf':'公共/数据手册/YAGEO_RT_PYU_RT.pdf',
   'manufacturer_ordering_pdf_sha256':sha(HW/'公共/数据手册/YAGEO_RT_PYU_RT.pdf'),
   'method':'RT V17 p2订购2010/F1%/K压花带/E50ppm/07/15K/L、p4本体5.00±0.10×2.50±0.15mm；Mounting V10 p4 Fig4 Table1回流2010 A6.1/B3.3/C1.4/D2.4mm目视核对；不混波峰表',
   'pin_functions':{'1':'terminal1','2':'terminal2'},'manufacturer_landpattern_verified':True,
   'prefer_manufacturer_geometry':True,'electrical_substitution':False,
   'pads':[dict(number=str(i+1),x_mm=x,y_mm=0,width_mm=1.4,height_mm=2.4) for i,x in enumerate((-2.35,2.35))],
   'body_height_max_mm':.65,'native_new_binding_readback':'NOT_RUN_PENDING_SHARED_LIBRARY_BATCH',
   'notes':'无极性两端；1左2右为项目CAD编号，非原厂极性定义；只绑定铜面及订购型号，热负载/阻焊钢网/制造与整板放行另验。'}
 if 'RSF2WSJR-M-750R' in models:
  for resistor in ('RSF2WSJR-M-68R','RSF2WSJR-M-390R','RSF2WSJR-M-620R','RSF2WSJR-M-750R'):
   spec=copy.deepcopy(specs.get(resistor,specs['RSF2WSJR-M-68R']))
   assert spec['name']=='项目封装_RSF2WS_M_P15' and len(spec['pads'])==2
   old_description={k:copy.deepcopy(spec[k]) for k in ('body_size_mm','notes','method') if k in spec}
   spec.pop('body_size_mm',None)  # H is lead forming, not installed top height.
   spec.update(source='https://www.yageogroup.com/content/Resource%20Library/Datasheet/YAGEO-RSF_DATASHEET.pdf',
    manufacturer_pdf='公共/数据手册/YAGEO_RSF.pdf',manufacturer_pdf_sha256=sha(HW/'公共/数据手册/YAGEO_RSF.pdf'),
    method='RSF V4 2024-04-01 p2订购/p3 RSF2WS尺寸/p4 E24范围/p12 M TYPE P15±1/H12.5±1mm目视核对；不是MB的H1=6/H2=5',
    pin_functions={'1':'terminal1','2':'terminal2'},manufacturer_landpattern_verified=False,
    manufacturer_body_and_lead_verified=True,prefer_manufacturer_geometry=True,electrical_substitution=False,
    manufacturer_dimensions_mm={'body_length':[10.5,12.5],'body_diameter':[4,5],'lead_diameter':[.75,.85],'M_pitch':[14,16],'M_lead_form_H':[11.5,13.5]},
    native_new_binding_readback='NOT_RUN_PENDING_SHARED_LIBRARY_BATCH')
   spec['notes']='无极性端子1/2为项目编号；M型H12.5±1是引线成形图尺寸，不冒充安装总高；原旧H1/H2属于MB型。复用已有15mm孔距/1.2mm成品孔/2.4mm铜面，均为项目工艺选择非厂家焊盘；装配前引脚校形成15mm，孔隙不吸收全部±1mm节距公差，不靠焊点拉扯成形。750R不继承其他阻值0.429W热预算。壳体二维包络保留，但不声明3D/庭院/制造资格。'
   if resistor!='RSF2WSJR-M-750R':
    if 'body_size_mm' in old_description or 'H1=6' in old_description.get('notes',''):
     if old_description not in spec.setdefault('尺寸说明修正历史',[]):spec['尺寸说明修正历史'].append(old_description)
    supp['footprints'][resistor]=copy.deepcopy(spec)
   specs[resistor]=spec
 if 'SM06B-GHS-TB(LF)(SN)' in models:
  specs['SM06B-GHS-TB(LF)(SN)']={'name':'项目封装_JST_GH_SM06_侧入_原厂推荐焊盘',
   'source':'https://www.jst-mfg.com/product/pdf/eng/eGH.pdf',
   'manufacturer_pdf':'公共/数据手册/SM05B-GHS-TB_LF_SN.pdf',
   'manufacturer_pdf_sha256':sha(HW/'公共/数据手册/SM05B-GHS-TB_LF_SN.pdf'),
   'method':'eGH p2右侧Side entry安装面图/p3 SM06完整型号A6.25/B10.75mm目视核对；信号1.25节距、0.6×1.7mm、固定片1×2.7mm；不镜像套BM顶出图',
   'pin_functions':{**{str(n):'CONTACT'+str(n) for n in range(1,7)},'7':'MECHANICAL_NC','8':'MECHANICAL_NC'},
   'pin_function_aliases':{'1':['isolated proof +5V'],'2':['P_MINUS proof return'],'3':['PF_RETURN_MID dry series'],'4':['BMS_B_MINUS_ISO dry return'],'5':['UNUSED_CONTACT5'],'6':['UNUSED_CONTACT6'],'7':['MECHANICAL_PAD7'],'8':['MECHANICAL_PAD8']},
   'application_role_alias_qualification':'1至6为厂家六个通用触点；proof等名称仅已冻结板合同的应用标注，不伪称原厂电气功能；7/8只为CAD机械号，非额外触点。',
   'mechanical_nc_numbers':['7','8'],'manufacturer_landpattern_verified':True,
   'prefer_manufacturer_geometry':True,'electrical_substitution':False,
   'pads':[dict(number=str(n),x_mm=-3.125+(n-1)*1.25,y_mm=4.55,width_mm=.6,height_mm=1.7) for n in range(1,7)]+
          [dict(number=str(n),x_mm=x,y_mm=1.35,width_mm=1,height_mm=2.7) for n,x in ((7,-4.975),(8,4.975))],
   'native_new_binding_readback':'NOT_RUN_PENDING_SHARED_LIBRARY_BATCH',
   'notes':'PCB安装面号1最左、1至6从左至右；原点为六针X中心与固定片下缘，+Y向信号排。号5/6未用电气触点及机械号7/8须保留实体盘且NC；无定位钻孔；不猜壳体/庭院/3D/制造或整板放行。'}
 if 'TS5A63157DBVR' in models:
  specs['TS5A63157DBVR']={'name':'项目封装_TI_DBV0006A_原厂推荐',
   'source':'https://www.ti.com/lit/ds/symlink/ts5a63157.pdf',
   'manufacturer_pdf':'公共/数据手册/TS5A63157.pdf','manufacturer_pdf_sha256':sha(HW/'公共/数据手册/TS5A63157.pdf'),
   'method':'SCDS203B p3六针DBV逐针/p25完整DBVR订购/p33 DBV0006A 4214840/G 08/2024推荐铜面实际原图目视核对；非五针DBV0005A或六针DCK',
   'pin_functions':{'1':'NO','2':'GND','3':'NC','4':'COM','5':'V+','6':'IN'},
   'pin_requirements':{'3':'NC means normally closed analog terminal, NOT unused pin; preserve its actual ground connection in this application.'},
   'manufacturer_landpattern_verified':True,'prefer_manufacturer_geometry':True,'electrical_substitution':False,
   'pads':[dict(number=str(i+1),x_mm=-1.3,y_mm=-.95+i*.95,width_mm=1.1,height_mm=.6) for i in range(3)]+
          [dict(number=str(6-i),x_mm=1.3,y_mm=-.95+i*.95,width_mm=1.1,height_mm=.6) for i in range(3)],
   'body_height_max_mm':1.45,'manufacturer_pad_corner_radius_mm':.05,
   'native_new_binding_readback':'NOT_RUN_PENDING_SHARED_LIBRARY_BATCH',
   'notes':'PCB顶视1左上；低IN选常闭3，高IN选常开1；应用3接本地GND不改成未连接标记。铜面采用原图矩形包络，R0.05/阻焊钢网及工艺由PCB落实；无热焊盘/额外NC/庭院3D或整板放行。'}
 for model,size,x,width,height in (('RT2512BKD07300RL','2512',3.1,1.8,4),('RT1206BRD07220RL','1206',1.6,1,1.5)):
  if model not in models:continue
  specs[model]={'name':'项目封装_YAGEO_RT'+size+'_原厂回流铜面',
   'source':'https://www.yageogroup.com/content/Resource%20Library/Product%20Guide-Catalog/yageo_PYu-R_Mount_10_19050818_343.pdf',
   'manufacturer_pdf':'公共/数据手册/YAGEO_ChipResistor_Mounting.pdf',
   'manufacturer_pdf_sha256':sha(HW/'公共/数据手册/YAGEO_ChipResistor_Mounting.pdf'),
   'manufacturer_ordering_pdf':'公共/数据手册/YAGEO_RT_PYU_RT.pdf',
   'manufacturer_ordering_pdf_sha256':sha(HW/'公共/数据手册/YAGEO_RT_PYU_RT.pdf'),
   'method':f'RT V17 p2订购{size}/B0.1%/'+('K压花带' if size=='2512' else 'R纸带')+'/D25ppm/07/'+('300R' if size=='2512' else '220R')+f'/L，p4实体尺寸；Mounting V10 p4 Fig4/Table1回流{size}原图目视核对，非波峰焊尺寸',
   'pin_functions':{'1':'terminal1','2':'terminal2'},'manufacturer_landpattern_verified':True,
   'prefer_manufacturer_geometry':True,'electrical_substitution':False,
   'pads':[dict(number=str(i+1),x_mm=q,y_mm=0,width_mm=width,height_mm=height) for i,q in enumerate((-x,x))],
   'native_new_binding_readback':'NOT_RUN_PENDING_SHARED_LIBRARY_BATCH',
   'notes':'两端无极性；1左2右是项目CAD编号。2512回流A8/B4.4/C1.8/D4mm，1206回流A4.2/B2.2/C1/D1.5mm；封装绑定不替代精度/电压/功率降额核算，不继承其他阻值热预算；不声明制造/整板放行。'}
 if 'NX3008PBK,215' in models:
  specs['NX3008PBK,215']={'name':'项目封装_Nexperia_SOT23_NX3008_原厂回流铜面',
   'source':'https://assets.nexperia.com/documents/data-sheet/NX3008PBK.pdf',
   'manufacturer_pdf':'公共/数据手册/NX3008PBK.pdf','manufacturer_pdf_sha256':sha(HW/'公共/数据手册/NX3008PBK.pdf'),
   'manufacturer_exact_ordering_source':'https://www.nexperia.com/chemical-content/NX3008PBK.html',
   'manufacturer_exact_ordering_identity':'NX3008PBK,215 / 12NC934065642215 / SOT23(TO-236AB)',
   'method':'Rev1 2011-08-01(版权2017) p2 1G/2S/3D及SOT23订购，p11顶视编号/p12 Fig19回流铜面0.6×0.7mm、双端距1.9/两排中心距2.0实际原图目视核对；非Fig20波峰或paste0.5×0.6',
   'pin_functions':{'1':'G','2':'S','3':'D'},'manufacturer_landpattern_verified':True,
   'prefer_manufacturer_geometry':True,'electrical_substitution':False,
   'pads':[dict(number=n,x_mm=x,y_mm=y,width_mm=.6,height_mm=.7) for n,x,y in [('1',-.95,1),('2',.95,1),('3',0,-1)]],
   'body_height_max_mm':1.1,'native_new_binding_readback':'NOT_RUN_PENDING_SHARED_LIBRARY_BATCH',
   'notes':'标准文件顶视Y向下：1左下G、2右下S、3上中D。Fig19无编号铜面作整体180度旋转，再按p2/p11编号，不镜像换S/D。三铜盘，无EP；钢网/阻焊/工艺及整板资格另验，不混相似SOT23型号针序。'}
 if 'BSC050N10NS5ATMA1' in models:
  # One continuous drain polygon carries terminal 5 and the exposed metal;
  # 6..8 overlap their actual fingers, retaining physical numbering without
  # splitting the drain into islands or inventing an exposed-pad pin 9.
  fingers=[-1.905,-.635,.635,1.905]
  drain_outline=[(-2.205,1.130),(2.205,1.130),(2.205,-3.325)]
  for i,x in enumerate(reversed(fingers)):
   if i:drain_outline.append((x+.3,-3.325))
   drain_outline.extend(((x-.3,-3.325),(x-.3,-2.525)))
   if i<3:drain_outline.append((fingers[2-i]+.3,-2.525))
  drain_outline.append((-2.205,1.130))
  copper=[dict(number=str(i+1),x_mm=x,y_mm=2.863,width_mm=.5,height_mm=.925) for i,x in enumerate(fingers)]
  copper.append(dict(number='5',x_mm=0,y_mm=-1.0975,width_mm=4.410,height_mm=4.455,shape='POLYGON',polygon_mm=drain_outline))
  copper.extend(dict(number=str(n),x_mm=x,y_mm=-2.925,width_mm=.6,height_mm=.8) for n,x in ((6,.635),(7,-.635),(8,-1.905)))
  for pad in copper:pad.update(paste_expansion_mm=-25.4,solder_expansion_mm=.05)
  paste=[{'points_mm':[(x-.2,2.863-.4125),(x+.2,2.863-.4125),(x+.2,2.863+.4125),(x-.2,2.863+.4125)]} for x in fingers]
  paste.extend({'points_mm':[(x-.25,-2.9-.375),(x+.25,-2.9-.375),(x+.25,-2.9+.375),(x-.25,-2.9+.375)]} for x in fingers)
  paste.extend({'points_mm':[(x0,y0),(x1,y0),(x1,y1),(x0,y1)]} for x0,x1 in ((-1.7,-.1),(.1,1.6)) for y0,y1 in ((-2.325,-.825),(-.625,.875)))
  specs['BSC050N10NS5ATMA1']={'name':'项目封装_BSC050_TDSON8_连续D5及真实6至8_工程候选',
   'source':'https://www.infineon.com/dgdl/Infineon-BSC050N10NS5-DataSheet-v02_03-EN.pdf?fileId=5546d462636cc8fb0164366daea34f7d',
   'manufacturer_pdf':'公共/数据手册/BSC050N10NS5ATMA1.pdf','manufacturer_pdf_sha256':sha(HW/'公共/数据手册/BSC050N10NS5ATMA1.pdf'),
   'manufacturer_ordering_source':'https://www.infineon.com/part/BSC050N10NS5',
   'manufacturer_package_source':'https://www.infineon.com/package/PG-TDSON-8-7',
   'method':'Rev2.3 p1真实1至3S/4G/5至8D及底部D金属、p10外形/p11 Fig2左铜右钢网实际原图目视核对；铜形从标注尺寸及接脚对齐关系工程推导，非八个独立铜岛',
   'pin_functions':{**{str(n):'S' for n in (1,2,3)},'4':'G',**{str(n):'D' for n in (5,6,7,8)}},
   'internally_common_pins':[['1','2','3'],['5','6','7','8']],
   'manufacturer_landpattern_verified':False,'manufacturer_body_lead_and_common_drain_verified':True,
   'manufacturer_annotated_pad_and_stencil_dimensions_verified':True,
   'prefer_manufacturer_geometry':True,'electrical_substitution':False,'pads':copper,'paste_mask_regions':paste,
   'physical_terminal_centers_mm':{**{str(i+1):[x,2.863] for i,x in enumerate(fingers)},**{str(8-i):[x,-2.925] for i,x in enumerate(fingers)}},
   'copper_derivation':'D总纵包络4.455/上缘-3.325，下缘+1.130。横宽4.410=2×1.905+0.6是Fig2接脚外侧对齐工程推导，非厂家独立尺寸；接脚0.6×0.8，间槽深0.8按既有原库拓扑工程构形。D5大面中心非接脚5中心；6至8实体接脚铜完整重叠在D5中，不另造EP9。',
   'mask_qualification':'铜盘自动锡膏全关闭，12个原图推导钢网窗独立顶锡膏层；阻焊每盘+0.05是项目工艺选择非厂保证，重叠D开窗须客户端实际回读。铜、mask、paste不互相冒充；本轮原生/工艺均未放行。',
   'stencil_derivation':'下1至4窗0.4×0.825中心y2.863；上5至8窗0.5×0.75中心y-2.900。大D四窗左宽1.6/右宽1.5、高1.5、横纵间隙0.2；上小窗下缘-2.525再留0.2至大窗顶-2.325。中心及绝对边界按Fig2相对尺寸工程推导，不声称额外厂标数字。',
   'native_new_binding_readback':'NOT_RUN_PENDING_SHARED_LIBRARY_BATCH','native_continuous_drain_and_stencil_readback':'NOT_RUN',
   'notes':'顶视标准文件Y向下，1左下S/4右下G/8左上D/5右上D。底部金属和5至8同D；四编号铜面重叠连续，禁止NC或假第9针。不声明厂家完整landpattern/自动庭院3D/钢网实际工艺或电气热layout放行；本候选原生转换必须核8真实针与连续铜/12钢网窗再使用。'}
 if 'IPT015N10N5ATMA1' in {p['mpn'] for p in c['parts']}:
  def window_rect(x0,y0,x1,y1):
   return {'points_mm':[(x0,y0),(x1,y0),(x1,y1),(x0,y1)]}
  source_edges=(-3.45,-2.4,-1.2,0,1.2,2.4,3.6,4.65)
  terminal_x=[-4.2+i*1.2 for i in range(8)]
  # Copper partition numbers preserve all seven physical source terminals;
  # the union is ONE continuous bar, not seven isolated copper islands.
  copper=[dict(number='1',x_mm=-4.2,y_mm=5.29,width_mm=.9,height_mm=2.9)]
  copper += [dict(number=str(i+2),x_mm=(a+b)/2,y_mm=5.29,width_mm=b-a,height_mm=2.9)
             for i,(a,b) in enumerate(zip(source_edges,source_edges[1:]))]
  copper += [dict(number='9',x_mm=0,y_mm=-2.61,width_mm=10.2,height_mm=8.1)]
  for pad in copper:
   pad.update(paste_expansion_mm=-25.4,solder_expansion_mm=-25.4)
  masks=[window_rect(-4.6,3.89,-3.8,6.69),
         window_rect(-3.4,3.89,4.6,4.69),
         window_rect(-5.05,-6.61,5.05,-5.11),
         window_rect(-4.35,-5.11,4.35,-2.31),
         window_rect(-4.85,-2.31,4.85,1.39)]
  masks += [window_rect(x-.4,4.69,x+.4,6.69) for x in terminal_x[1:]]
  paste=[window_rect(x-.4,3.99,x+.4,6.69) for x in terminal_x]
  for row in range(6):
   xs=terminal_x if row in (0,4,5) else terminal_x[1:-1]
   paste += [dict(shape='circle',x_mm=x,y_mm=-5.79+row*1.2,diameter_mm=1) for x in xs]
  specs['IPT015N10N5ATMA1']={
   'name':'项目封装_IPT015_PG_HSOF_8_1_原厂窗口_共源铜面候选',
   'source':'https://www.infineon.com/package/PG-HSOF-8-1',
   'method':'IPT015N10N5原厂p1 Gate1/Source2至8/Drain Tab；原厂PG-HSOF-8-1 FPD图尺寸指向黑色阻焊边界，灰色铜区与开口分开实现',
   'manufacturer_pdf':'公共/数据手册/Infineon_PG_HSOF_8_1_推荐焊盘.pdf',
   'manufacturer_pdf_sha256':sha(HW/'公共/数据手册/Infineon_PG_HSOF_8_1_推荐焊盘.pdf'),
   'manufacturer_pin_pdf':'公共/数据手册/IPT015N10N5ATMA1.pdf',
   'manufacturer_pin_pdf_sha256':sha(HW/'公共/数据手册/IPT015N10N5ATMA1.pdf'),
   'manufacturer_package_association':'IPT015N10N5官网型号页Package链接为PG-HSOF-8-1；OPN IPT015N10N5ATMA1',
   'manufacturer_landpattern_verified':False,'manufacturer_mask_and_stencil_dimensions_verified':True,
   'copper_margin_mm':.05,'copper_margin_qualification':'项目候选：按原图灰色连续矩形铜面保留0.05mm边裕；原图未独立标注该边裕，不声称厂家保证值；制造工艺仍未放行',
   'native_mask_and_paste_readback':'NOT_RUN_PENDING_SHARED_LIBRARY_BATCH',
   'prefer_manufacturer_geometry':True,
   'pin_functions':{'1':'G',**{str(n):'S' for n in range(2,9)},'9':'D'},
   'pin_function_aliases':{'9':['D/tab']},
   'cad_number_aliases':{'9':'厂家Drain Tab；9是项目CAD编号，非厂家第9脚'},
   'internally_common_pins':[[str(n) for n in range(2,9)]],
   'physical_terminal_centers_mm':{str(i+1):[x,5.29] for i,x in enumerate(terminal_x)},
   'source_copper_union_mm':[-3.45,3.84,4.65,6.74],
   'pads':copper,'solder_mask_regions':masks,'paste_mask_regions':paste,
   'notes':'PCB顶视Gate1左下，Source2至8同网且相邻铜分区无缝共接；铜分区中心不冒充端子中心。9仅代表Drain Tab。自动阻焊/锡膏窗口显式关闭，厂家尺寸窗口独立绘制；42个直径1mm圆属于顶锡膏层，不是钻孔/热过孔。原厂推荐窗口尺寸已核，铜边裕、原生转换回读及工艺资格未放行；不加未核壳体/庭院/3D。'}
 add_final_batch_specs(specs,models)
 if c['board']=='配电':add_pd_remaining_specs(specs,models)
 if c.get('e4_stable'):
  for m in list(specs):
   if m.startswith('RNCF0805TKY'):specs.pop(m)
  add_e4_reuse_specs(specs,models)
  if 'RNCF0805TKY66K5' in models:
   prior=supp.get('板级集成厂家封装',{}).get('RNCF0805TKY100K')
   assert prior and prior['name']=='项目封装_Stackpole_RNCF0805_工程铜面'
   specs['RNCF0805TKY66K5']=copy.deepcopy(prior)
   specs['RNCF0805TKY66K5'].update(method='同厂RNCF0805两无极性端子；66.5k精确型号复用已核100k工程铜面，不继承阻值额定或声称厂家landpattern',electrical_substitution=False)
 old=read(LIB/'封装绑定.json');oldmodels={b['型号']:b for b in old['位号绑定'] if b.get('封装')}
 for prior_board in old.get('板级绑定',{}).values():
  for b in prior_board['位号绑定']:
   if b.get('封装'):oldmodels.setdefault(b['型号'],b)
 # 仅同厂家、同系列、同case的两端无极性器件可复用真实几何；保留机械待审门。
 def family(m):
  for f in ('CRCW0603','CRCW1206','CRCW2512','C1608','C2012','C3216','C3225','C0805C','C1206C','RT0805','RC0805','RT1206','RNCF0805'):
   if m.startswith(f):return f
  return None
 families={}
 for m,r in raw.items():
  f=family(m.upper())
  if f and set(r['pins'])==set(r['pads'])=={'1','2'}:families.setdefault(f,(m,r))
 bindings=[];new_specs={};function_differences=[]
 for p in c['parts']:
  m=p['mpn'];r=raw.get(m.casefold());b={'位号':p['ref'],'型号':m,'安装':p['installation'] if c['board']=='FOC' else ('板上' if p['onboard'] else '板外'),
   '封装':'','引脚映射':{n:n for n in p['pins']},'封装状态':'未绑定','制造商':p['manufacturer'],
   '数量':p['quantity'],'装配':p.get('assembly','候选装配禁止生产'),'来源':p.get('source',''),
   '逐脚功能已核':False,'厂家推荐焊盘已核':False,'制造放行':False}
  name='';doc=None;evidence={};same=set(p['pins'])
  numbering=supp.get('raw_pin_number_aliases',{}).get(m)
  if r and numbering and same==set(numbering['number_to_source'].values()):
   numbering=copy.deepcopy(numbering);mapping=numbering['number_to_source']
   assert r['code']==numbering['raw_code'] and hashlib.sha256(r['blob']).hexdigest()==numbering['raw_sha256']
   assert sha(HW/numbering['manufacturer_pdf'])==numbering['manufacturer_pdf_sha256']
   assert set(r['pins'])==set(r['pads'])==set(mapping)
   for number,count in numbering['expected_pad_multiplicity'].items():assert r['pads'].count(number)==count
   r=copy.deepcopy(r);r['pads']=[mapping[n] for n in r['pads']]
   r['pins']={mapping[n]:numbering.get('merged_functions',{}).get(mapping[n],f) for n,f in r['pins'].items()}
   renumbered=[]
   for shape in r['footprint']['shape']:
    if shape.startswith('PAD~'):
     fields=shape.split('~');fields[8]=mapping[fields[8]];shape='~'.join(fields)
    renumbered.append(shape)
   r['footprint']['shape']=renumbered
  if not p['onboard']:
   b['封装状态']='板外，不放PCB'
  elif specs.get(m,{}).get('geometry_orientation_verified') is False:
   b['封装状态']='厂商孔距已核；元件面镜像方向未证，禁止沿用候选绑定'
  elif r and same==set(r['pins'])==set(r['pads']) and not specs.get(m,{}).get('prefer_manufacturer_geometry'):
   name='立创封装_'+r['code'];doc=copy.deepcopy(r['footprint'])
   if numbering and same==set(numbering['number_to_source'].values()):name+='_审定编号'
   evidence={'method':'完整型号原始立创库；同针号集合','source':'https://easyeda.com/api/products/'+r['code']+'/components',
    'library_code':r['code'],'package_uuid':r['uuid'],'raw_sha256':hashlib.sha256(r['blob']).hexdigest(),'pin_functions':r['pins']}
   if numbering and same==set(numbering['number_to_source'].values()):evidence['explicit_numbering_alias']=numbering
   source_functions={n:p.get('names',{}).get(n,'') for n in same if p.get('names',{}).get(n)}
   diff=compare_pin_functions(source_functions,r['pins'],source_functions)
   if diff:function_differences.append({'位号':p['ref'],'型号':m,'差异':diff})
   b['逐脚功能已核']=not diff and bool(p.get('names'))
  elif m in specs and set(specs[m].get('source_pin_to_pad') or {str(x['number']):str(x['number']) for x in specs[m]['pads']})==same:
   spec=specs[m];name=spec['name'];doc=tools.build_footprint(name,spec,template)
   b['引脚映射']=source_to_physical_pad(p,spec)
   for group in spec.get('required_parallel_terminal_pairs',[]):
    assert len({p['pins'][n] for n in group})==1,(p['ref'],'厂家要求外部并接的绕组端子在板源中异网',group)
   for n in spec.get('mechanical_nc_numbers',[]):
    assert p['pins'][n].startswith('NC_'),(p['ref'],n,'机械固定片不得接电气网络')
   evidence={k:v for k,v in spec.items() if k!='pads'}
   # Manufacturer pin functions are independent evidence, never source echoes.
   physical_functions=spec.get('pin_functions',{})
   functions={n:physical_functions[target] for n,target in b['引脚映射'].items() if target in physical_functions}
   evidence['source_pin_to_pad']=b['引脚映射']
   evidence['mapped_manufacturer_pin_functions']=functions
   source_functions=p.get('names') or p.get('factory_pin_functions') or p.get('pinmap_metadata',{}).get('pin_functions',{})
   evidence['source_pin_functions']=source_functions
   if functions and source_functions:
    diff=compare_pin_functions(source_functions,functions,same)
    for n,target in b['引脚映射'].items():
     aliases=spec.get('pin_function_aliases',{}).get(target,[])
     if n in diff and any(normalize_pin_function(source_functions.get(n,''))==normalize_pin_function(a) for a in aliases):
      del diff[n]
    if diff:function_differences.append({'位号':p['ref'],'型号':m,'差异':diff})
    b['逐脚功能已核']=not diff and set(functions)==same
   b['厂家推荐焊盘已核']=bool(spec.get('manufacturer_landpattern_verified')) or m.startswith(('XGL1313-','TNPW1206'))
   prior_spec=supp.get('板级集成厂家封装',{}).get(m,{})
   history=copy.deepcopy(prior_spec.get('限定库证据历史',[]))
   for key in ('公共库限定自检','独立限定验收'):
    if key in prior_spec:
     historical={'证据类别':key,'原证据':copy.deepcopy(prior_spec[key]),'适用性':'仅原证据明确的源/工具/成员SHA；不继承为本轮新源放行'}
     if historical not in history:history.append(historical)
   if history:spec['限定库证据历史']=history
   new_specs[m]=spec
  elif m in supp.get('approved_geometry_aliases',{}):
   alias=supp['approved_geometry_aliases'][m];br=raw[alias['geometry_model'].casefold()]
   assert same==set(br['pins'])==set(br['pads'])
   assert sha(HW/alias['manufacturer_pdf'])==alias['manufacturer_pdf_sha256']
   name='立创封装_'+br['code'];doc=copy.deepcopy(br['footprint']);evidence=copy.deepcopy(alias)
   evidence.update(geometry_raw_sha256=hashlib.sha256(br['blob']).hexdigest(),library_code=br['code'],electrical_substitution=False)
   if alias.get('pin_functions'):
    functions=alias['pin_functions'];source_functions=p.get('names') or {}
    assert set(functions)==same,(p['ref'],'独立同几何型号针功能覆盖不全')
    diff=compare_pin_functions(source_functions,functions,same)
    if diff:function_differences.append({'位号':p['ref'],'型号':m,'差异':diff})
    b['逐脚功能已核']=bool(source_functions) and not diff
  elif m in oldmodels and set(oldmodels[m]['引脚映射'])==same:
   ob=oldmodels[m]
   if ob.get('库文件') in blobs and set(ob['引脚映射'].values())==same:
    name=ob['封装'];doc=json.loads(blobs[ob['库文件']]);evidence=ob.get('依据',{})
  elif p.get('mechanical_reference_mpn') and p.get('fitted') is False and p.get('procurement_quantity')==0 and same=={'1','2'}:
   reference=p['mechanical_reference_mpn'];br=raw.get(reference.casefold())
   if br and set(br['pins'])==set(br['pads'])==same:
    name='立创封装_'+br['code'];doc=copy.deepcopy(br['footprint'])
    evidence={'method':'作者明确DNP机械槽合同；不替换工作型号、不增加采购或电气额定',
     'mechanical_reference_mpn':reference,'geometry_raw_sha256':hashlib.sha256(br['blob']).hexdigest(),
     'library_code':br['code'],'fitted':False,'procurement_quantity':0,'electrical_substitution':False}
  elif family(m) in families and same=={'1','2'}:
   bm,br=families[family(m)];name='立创封装_'+br['code'];doc=copy.deepcopy(br['footprint'])
   evidence={'method':'同系列同case无极性两端件复用真实几何候选；厂家目标landpattern待审',
    'source':p.get('source',''),'geometry_model':bm,'library_code':br['code'],
    'geometry_raw_sha256':hashlib.sha256(br['blob']).hexdigest(),'pin_functions':p.get('names',{})}
  if doc:
   doc['head']['c_para']['package']=name;doc['head']['uuid']=uuid.uuid5(uuid.NAMESPACE_URL,'foc-library/'+(r['uuid'] if r and same==set(r['pads']) else name)).hex
   member='封装/'+name+'.json'
   if member in blobs:
    cached=json.loads(blobs[member]);geometry=lambda x:[s for s in x['shape'] if not s.startswith('SVGNODE~')]
    assert geometry(cached)==geometry(doc),(name,'已有封装几何冲突')
    content=blobs[member]
   else:content=dump(doc).encode('utf8');blobs[member]=content
   b.update(封装=name,库文件=member,封装SHA256=hashlib.sha256(content).hexdigest(),封装状态='已绑定候选；制造未放行',依据=evidence)
  bindings.append(b)
 save_archive(LIB/'可导入封装库.zip',blobs)
 supp.setdefault('板级集成厂家封装',{}).update(new_specs);write(LIB/'封装补充依据.json',supp)
 prior=old.setdefault('板级绑定',{}).get(c['board'])
 if prior and prior['板源文件SHA256']!=c['hashes']:
  history=old.setdefault('板级绑定历史',{}).setdefault(c['board'],[])
  if prior not in history:history.append(copy.deepcopy(prior))
 old['板级绑定'][c['board']]={'源SHA256':c['digest'],'板源文件SHA256':c['hashes'],'位号绑定':bindings,'逐脚功能差异':function_differences,'制造放行':False}
 write(LIB/'封装绑定.json',old)
 return {b['位号']:b for b in bindings},function_differences

def record_pd_binding_batch(c):
 """库补齐是独立阶段，不能把尚未更新的正式工程缺口改成已消除。"""
 assert c['board']=='配电'
 rows=read(LIB/'封装绑定.json')['板级绑定']['配电'];assert rows['板源文件SHA256']==c['hashes']
 by={x['位号']:x for x in rows['位号绑定']};specs={}
 add_pd_remaining_specs(specs,{p['mpn'] for p in c['parts']})
 selected=[p for p in c['parts'] if (p['mpn'] in specs or p['mpn']=='RT1206BRD0710KL') and by[p['ref']].get('库文件')]
 affected=[copy.deepcopy(by[p['ref']]) for p in selected]
 blobs=archive(LIB/'可导入封装库.zip')
 for b in affected:assert hashlib.sha256(blobs[b['库文件']]).hexdigest()==b['封装SHA256']
 remaining=[{'ref':p['ref'],'mpn':p['mpn']} for p in c['parts'] if p['onboard'] and not by[p['ref']].get('库文件')]
 r=validation_result(c)
 r['公共库配电剩余封装补齐']={'源文件SHA256':c['hashes'],'工具SHA256':sha(__file__),
  '批次新增位号':len(affected),'批次型号数':len({p['mpn'] for p in selected}),
  '位号绑定':affected,'库阶段剩余板上缺封装':remaining,'剩余位号数':len(remaining),
  '剩余型号数':len({p['mpn'] for p in remaining}),
  '公共封装库SHA256':sha(LIB/'可导入封装库.zip'),'公共绑定JSONSHA256':sha(LIB/'封装绑定.json'),
  '原生回读':'NOT_RUN_PENDING_REMAINING_MODELS','原正式工程未改':True,
  '边界':'仅公共库增量24位号；正式722位号工程仍是原版，原62缺封装及无有效网表结论未覆盖。未把库阶段38写作原生阶段38。'}
 update(c,r)
 print(dump({'证据文件':str(c['report'].relative_to(ROOT)),'证据SHA256':sha(c['report']),
  '库阶段新增':len(affected),'库阶段剩余':len(remaining),'正式原生新增绑定已执行':False}))

def packet(c): return c.get('packet_path',CACHE/c['board']/'集成输入.json')

def prepare_current_pd_library(expected_sha):
 """作者自然提交后仅绑定公共库，不改正式原生或其旧版证据。"""
 saved=CONFIG['配电']
 assert sha(HW/'配电与水泵/设计源.py')==expected_sha
 try:
  CONFIG['配电']=saved[:5]+({'设计源.py':expected_sha},)
  c=source('配电')
 finally:CONFIG['配电']=saved
 assert len(c['parts'])==731 and sum(len(p['pins']) for p in c['parts'])==2225
 previous=copy.deepcopy(read(LIB/'封装绑定.json')['板级绑定']['配电'])
 previous_by={v['位号']:v for v in previous['位号绑定']}
 formal_before={p.relative_to(HW/'配电与水泵/原生工程').as_posix():sha(p)
  for p in (HW/'配电与水泵/原生工程').rglob('*') if p.is_file()}
 binding,differences=bind(c)
 blobs=archive(LIB/'可导入封装库.zip')
 for row in binding.values():
  if row.get('库文件'):
   assert hashlib.sha256(blobs[row['库文件']]).hexdigest()==row['封装SHA256']
   doc=json.loads(blobs[row['库文件']]);pads=[s.split('~')[8] for s in doc['shape'] if s.startswith('PAD~')]
   assert set(pads)==set(row['引脚映射'].values()),row['位号']
 missing=[{'ref':p['ref'],'mpn':p['mpn']} for p in c['parts'] if p['onboard'] and not binding[p['ref']].get('库文件')]
 selected=[row for ref,row in binding.items() if row.get('库文件') and not previous_by.get(ref,{}).get('库文件')]
 retained=[binding[p['ref']] for p in c['parts'] if p['mpn'] in ('1777545','SPM10065VT-6R8M-D','SPM10065VC-220M-D','SMBJ12A','SMBJ33A')]
 assert len(retained)==9 and all(row.get('库文件') for row in retained)
 for row in retained:
  before=previous_by[row['位号']]
  assert all(row[k]==before[k] for k in ('型号','库文件','封装SHA256','引脚映射')),'已验收9位号几何/绑定不得被新批静默改变'
 copper=verify_pd_incremental_geometry(c,selected,blobs)
 assert formal_before=={p.relative_to(HW/'配电与水泵/原生工程').as_posix():sha(p)
  for p in (HW/'配电与水泵/原生工程').rglob('*') if p.is_file()},'公共库准备不得改正式工程'
 record={'状态':'PUBLIC_LIBRARY_ONLY_NATIVE_NOT_RUN','作者稳定但电气未定稿':True,
  '源文件SHA256':c['hashes'],'源位号':len(c['parts']),'源端子':2225,'工具SHA256':sha(__file__),
  '本次厂图新增':selected,'绑定位号':sum(bool(v.get('库文件')) for v in binding.values()),
  '新增实际库铜面回读':copper,'既有9位号库成员及映射未变':True,
  '仍待完整原厂订单关联':[row['位号'] for row in binding.values() if row.get('依据',{}).get('manufacturer_exact_ordering_verified') is False],
  '板上缺封装':missing,'剩余位号数':len(missing),'剩余型号数':len({p['mpn'] for p in missing}),
  '逐脚功能差异':differences,'公共绑定JSONSHA256':sha(LIB/'封装绑定.json'),'公共封装库SHA256':sha(LIB/'可导入封装库.zip'),
  '旧正式工程保持不变':True,'新源原生已消费':False,'新源有效官方网表':'NOT_RUN','新源官方ERC':'NOT_RUN',
  '准确嘉立创接口本轮检查':{'C2047831':403,'C151251':403,'C224019':403},
  '正式工程保持原字节SHA256':formal_before,
  '边界':'作者源按本记录逐文件SHA为准，不等于电气定稿；D855正式722/2213与原62缺封装只属旧输入。本记录仅公共库，不继承旧原生/ERC/网表；PMV的R后缀完整原厂订单关联仍待核。旧限定验收按原成员SHA保留，原共享库整体SHA不代表新增后的共享文件。'}
 assert sha(HW/'配电与水泵/设计源.py')==expected_sha,'活源已改变，禁止写准备指针'
 j=read(c['report'])
 if j.get('当前源公共库准备'):
  history=j.setdefault('公共库准备历史',[])
  if j['当前源公共库准备'] not in history:history.append(copy.deepcopy(j['当前源公共库准备']))
 j['当前源公共库准备']=record
 if '配电' in j.get('current_delivery_index',{}):
  j['current_delivery_index']['配电'].update(当前作者源SHA256=c['hashes'],源文件与当前活源逐字节一致=False,
   当前作者源正式原生已消费=False,旧原生对当前电气源适用=False)
 write(c['report'],j)
 print(dump({'源文件SHA256':c['hashes'],'源位号':731,'源端子':2225,
  '本次厂图新增位号':len(selected),'绑定位号':record['绑定位号'],
  '剩余位号数':len(missing),'剩余型号数':record['剩余型号数'],'功能差异条目':len(differences),
  '新源原生已消费':False,'证据文件':str(c['report'].relative_to(ROOT)),'证据SHA256':sha(c['report'])}))

def verify_pd_incremental_geometry(c,rows,blobs):
 """回读实际ZIP铜面，与已核厂家数值独立对照；不把此检查冒充原生验收。"""
 expected={
  'NVMFS6B25NLT1G':(.75,1,2.795,5.55,-2.725,.905),
  'NVMFS6B14NLT1G':(.75,1,2.795,5.55,-2.725,.905),
  'NVMFS6H800NLT1G':(.75,1,2.80,5.56,-2.95,.91),
  'BSS138-7-F':(.8,.9),'PMV20XNER':(.6,.7),'BZT52H-A18X':(1.2,1.2)}
 by={p['ref']:p for p in c['parts']};out=[]
 for row in rows:
  data=blobs[row['库文件']];assert hashlib.sha256(data).hexdigest()==row['封装SHA256']
  doc=json.loads(data);pads=[s.split('~') for s in doc['shape'] if s.startswith('PAD~')]
  assert len({p[8] for p in pads})==len(pads),'新增物理铜不得用重复号掩盖重叠'
  assert set(row['引脚映射'])==set(by[row['位号']]['pins'])
  assert {p[8] for p in pads}==set(row['引脚映射'].values())
  actual={p[8]:dict(x=(float(p[2])-4000)*.254,y=(float(p[3])-3000)*.254,
   w=float(p[4])*.254,h=float(p[5])*.254,layer=p[6],drill=float(p[9])*.508,shape=p[1]) for p in pads}
  near=lambda a,b:abs(a-b)<3e-8
  model=row['型号'];values=expected.get(model)
  if values:
   assert all(p['layer']=='1' and p['drill']==0 for p in actual.values())
   assert row['逐脚功能已核'],'本批有厂家针序，逐脚功能差异不得跳过'
  if model.startswith('NVMFS6'):
   w,h,sy,dw,ny,shoulder=values
   assert len(pads)==5 and set(actual)=={'1','2','3','4','5'}
   for n,x in enumerate((-1.905,-.635,.635,1.905),1):
    p=actual[str(n)];assert all((near(p['x'],x),near(p['y'],sy),near(p['w'],w),near(p['h'],h)))
   drain=next(p for p in pads if p[8]=='5');assert drain[1]=='POLYGON'
   xy=list(map(float,drain[10].split()));points=[((x-4000)*.254,(y-3000)*.254) for x,y in zip(xy[::2],xy[1::2])]
   reference=[(-2.28,-3.2),(-1.53,-3.2),(-1.53,ny),(1.53,ny),(1.53,-3.2),(2.28,-3.2),
    (2.28,0),(dw/2,0),(dw/2,shoulder),(2.28,shoulder),(2.28,1.33),(-2.28,1.33),
    (-2.28,shoulder),(-dw/2,shoulder),(-dw/2,0),(-2.28,0)]
   assert len(points)==16 and all(near(x,a) and near(y,b) for (x,y),(a,b) in zip(points,reference))
   from shapely.geometry import Polygon
   copper=Polygon(points)
   assert copper.is_valid and copper.geom_type=='Polygon' and not copper.interiors,'D铜不得自交、分岛或虚造孔'
   p=actual['5'];assert near(p['x'],0) and near(p['y'],-.935) and near(p['w'],dw) and near(p['h'],4.53)
   if model=='NVMFS6H800NLT1G':assert row['引脚映射']['6']==row['引脚映射']['5']=='5'
  elif model in ('BSS138-7-F','PMV20XNER'):
   assert len(pads)==3
   for n,x,y in (('1',-.95,1),('2',.95,1),('3',0,-1)):
    p=actual[n];assert near(p['x'],x) and near(p['y'],y) and near(p['w'],values[0]) and near(p['h'],values[1])
  elif model=='BZT52H-A18X':
   assert len(pads)==2
   for n,x in (('1',-1.4),('2',1.4)):
    p=actual[n];assert near(p['x'],x) and near(p['y'],0) and near(p['w'],1.2) and near(p['h'],1.2)
  elif model=='39-30-1020':
   assert len(pads)==2 and set(actual)=={'1','2'} and row['逐脚功能已核']
   for n,y in (('1',0),('2',-5.5)):
    p=actual[n];assert near(p['x'],0) and near(p['y'],y) and near(p['w'],2.7) and near(p['h'],3.7)
    assert near(p['drill'],1.8) and p['layer']=='11'
   holes=[s.split('~') for s in doc['shape'] if s.startswith('HOLE~')]
   assert len(holes)==1
   hole=holes[0];assert near((float(hole[1])-4000)*.254,0) and near((float(hole[2])-3000)*.254,7.3) and near(float(hole[3])*.508,3)
  else:raise AssertionError((model,'新增封装须补实际几何对照'))
  nonplated=[s.split('~') for s in doc['shape'] if s.startswith('HOLE~')]
  actual_holes=[{'x_mm':(float(h[1])-4000)*.254,'y_mm':(float(h[2])-3000)*.254,'diameter_mm':float(h[3])*.508,'plated':False} for h in nonplated]
  out.append({'ref':row['位号'],'model':model,'member':row['库文件'],'member_sha256':row['封装SHA256'],
   'copper_records':len(pads),'physical_pin_to_pad':row['引脚映射'],'actual_pads_mm':actual,
   'nonplated_holes':actual_holes,
   'status':'PASS_SCOPED_ACTUAL_MEMBER_COPPER_PIN_MAPPING_NOT_NATIVE','manufacturing_released':False})
 return out

def record_current_pd_incremental_checks():
 """补记本批实际成员及失效别名检查，保持新增计数与旧限定验收。"""
 path=HW/'配电与水泵/核验.json';j=read(path);record=j['当前源公共库准备']
 expected=record['源文件SHA256']['设计源.py'];saved=CONFIG['配电']
 try:
  CONFIG['配电']=saved[:5]+({'设计源.py':expected},);c=source('配电')
 finally:CONFIG['配电']=saved
 blobs=archive(LIB/'可导入封装库.zip');rows=record['本次厂图新增']
 record['新增实际库铜面回读']=verify_pd_incremental_geometry(c,rows,blobs)
 specs={};add_pd_remaining_specs(specs,{p['mpn'] for p in c['parts']})
 part=copy.deepcopy(next(p for p in c['parts'] if p['mpn']=='NVMFS6H800NLT1G'))
 source_to_physical_pad(part,specs[part['mpn']]);part['pins']['6']='INVALID_ALIAS_TEST_NET'
 rejected=False
 try:source_to_physical_pad(part,specs[part['mpn']])
 except AssertionError:rejected=True
 assert rejected,'源6与5异网必须失败，不可静默合并'
 record['限定实际验证']={'状态':'PASS_SCOPED_NEW_COPPER_MAPPING_AND_ALIAS_GUARD',
  '执行工具SHA256':sha(__file__),'新增位号':len(rows),
  '实际铜记录':sum(row['copper_records'] for row in record['新增实际库铜面回读']),
  'D铜有效单一连续多边形无内孔':True,'H800源6别名异网拒绝':rejected,
  '当前源SHA256':c['hashes'],'公共库SHA256':sha(LIB/'可导入封装库.zip'),
  '实际原生消费':False,'ERC通过':False,'制造放行':False}
 record['既有9位号独立限定验收']={
  '状态':'PASS_SCOPED_PD_PUBLIC_LIBRARY_9REF_18COPPER',
  '责任聊天':'01a10719-4838-7493-b1dd-87d621c10127',
  '原作者源SHA256':'210cd232dd06164ba215d71fbc1ee2c122ffdcebcd93c84413f190a462563837','原核验JSONSHA256':'023672f5607523d2b80dd618f3f151530bd372bd581d140072f9ee21f55cb30e',
  '原执行工具SHA256':'f667dee3c2f48491a0910c5de4171d4f313dba15ec16e8d0eafaf73fbd0b82a5',
  '原绑定JSONSHA256':'7b7104d5ef3abfdb3778742c57c3b55cd3fc3f6ef71bcf4fb800b6afa75ed6b1',
  '原公共库SHA256':'849d53308ae1ddbcf0734f2bcaf86c9addf5853989642418c94ea77318552a90',
  '原限定结论':'9实际成员SHA/针序/源网/中心尺寸/孔层一致，最大误差9.2e-9mm；真实厂家图已读，原65功能差异/正式未消费/制造未放行仍保留。',
  '本批9位号库成员及映射保持不变':record['既有9位号库成员及映射未变'],
  '边界':'历史210CD限定验收，不把上述原整体JSON/ZIP SHA称为当前共享文件SHA，不扩成新22验收。'}
 assert sha(HW/'配电与水泵/设计源.py')==expected
 write(path,j);print(dump({'新增实际位号':len(rows),'实际铜记录':record['限定实际验证']['实际铜记录'],
  '剩余缺封装':record['剩余位号数'],'核验JSONSHA256':sha(path),'执行工具SHA256':sha(__file__)}))

def record_pd_on_small_independent_review(receipt):
 """新增Molex后仅把原22/95限定验收挂回原批，不继承原整体库SHA。"""
 path=HW/'配电与水泵/核验.json';j=read(path)
 historical=next(r for r in j['公共库准备历史'] if len(r['本次厂图新增'])==22 and
  r['公共封装库SHA256']=='f3928c994f47fb865c33992a8c58c0bb07a5f67569b5a37c67bfaea7953b8451')
 historical['独立限定验收']={'状态':'PASS_SCOPED_PD_PUBLIC_LIBRARY_ON_SMALL_22REF_95COPPER',
  '责任聊天':'01a10719-4838-7493-b1dd-87d621c10127','完整原文':receipt,
  '原核验JSONSHA256':'028d992c27d9414416609add3346f19103e533eaf86708601d2df41e2783fd1d',
  '边界':'只属本记录源/22成员95铜及原整体ZIP绑定SHA；Molex后新增成员不继承这个限定PASS。'}
 current=j['当前源公共库准备'];saved=CONFIG['配电'];expected=current['源文件SHA256']['设计源.py']
 try:
  CONFIG['配电']=saved[:5]+({'设计源.py':expected},);c=source('配电')
 finally:CONFIG['配电']=saved
 blobs=archive(LIB/'可导入封装库.zip')
 current['新增实际库铜面回读']=verify_pd_incremental_geometry(c,current['本次厂图新增'],blobs)
 bindings=read(LIB/'封装绑定.json')['板级绑定']['配电']['位号绑定']
 current['仍待完整原厂订单关联']=[b['位号'] for b in bindings if b.get('依据',{}).get('manufacturer_exact_ordering_verified') is False]
 current['限定实际验证']={'状态':'PASS_SCOPED_MOLEX_MEMBER_TWO_COPPER_ONE_NPTH_NOT_NATIVE',
  '执行工具SHA256':sha(__file__),'新增位号':len(current['本次厂图新增']),
  '实际铜记录':sum(r['copper_records'] for r in current['新增实际库铜面回读']),
  '实际NPTH':sum(len(r['nonplated_holes']) for r in current['新增实际库铜面回读']),
  '原生消费':False,'制造放行':False}
 write(path,j);print(dump({'当前新增位号':len(current['本次厂图新增']),
  '缺封装':current['剩余位号数'],'仍待订单关联':current['仍待完整原厂订单关联'],
  '公共库SHA256':sha(LIB/'可导入封装库.zip'),'绑定JSONSHA256':sha(LIB/'封装绑定.json'),
  '核验JSONSHA256':sha(path),'本轮限定回读工具SHA256':sha(__file__)}))

def prepare_revz_foc_inputs():
 """保全作者最终自然提交，只准备受影响两板单页输入，不重AUX原生。

 已失效：本函数要从"当前活源"重放 RevZ 历史输入，但活源已被后续版本取代、且 储能模块.py 已改名为 中央稳压模块.py，指纹核对不可能通过。保留函数仅为定位历史；历史证据在 .cache/板级集成/FOC/RevZ-197103dc101a/ 内。"""
 raise RuntimeError('prepare_revz_foc_inputs 已失效：当前活源非 RevZ 版本且 储能模块.py 已改名，无法重放；历史证据见 .cache/板级集成/FOC/RevZ-197103dc101a/')
 rev='RevZ-197103dc101a';hashes={'设计数据.py':'197103dc101ae2da8f80afdd9b404238dad9bd6c68754b74b110000b7229e1b3',
  '储能模块.py':'87cd6ef9083f5dcdaf382a76ba446712ad7984863dfe3dc4246de89876117d44'}
 live=HW/'FOC驱动与储能';dest=CACHE/'FOC'/rev
 assert all(sha(live/f)==h for f,h in hashes.items())
 dest.mkdir(exist_ok=True)
 for f,h in hashes.items():
  target=dest/f
  if target.exists():assert sha(target)==h,'同版保全输入冲突，禁止覆盖'
  else:shutil.copy2(live/f,target)
 c=source('FOC',revision=rev);assert len(c['parts'])==1616
 old=source('FOC',revision='RevY-bb5d2188be94')
 by={p['ref']:p for p in c['parts']};prior={p['ref']:p for p in old['parts']}
 aux={r:p for r,p in by.items() if p['board']=='辅助电源板'}
 previous={r:p for r,p in prior.items() if p['board']=='辅助电源板'}
 assert aux.keys()==previous.keys() and len(aux)==22
 note_changes=[]
 for ref,p in aux.items():
  q=previous[ref]
  assert {k:v for k,v in p.items() if k!='note'}=={k:v for k,v in q.items() if k!='note'},(ref,'AUX非备注改变，不能跳过原生')
  if p.get('note')!=q.get('note'):note_changes.append({'ref':ref,'before':q.get('note'),'after':p.get('note')})
 assert {x['ref'] for x in note_changes}=={'F_MAIN1','F_MOD1','F_MOD2'}
 bindings,differences=bind(c)
 missing=[p['ref'] for p in c['parts'] if p['onboard'] and not bindings[p['ref']].get('库文件')]
 assert not missing,('FOC新版板上缺真实封装',missing)
 board_input=[]
 for physical in ('驱动主板','中央稳压模块'):
  scope=dest/physical;scope.mkdir(exist_ok=True)
  own=dict(c,parts=[p for p in c['parts'] if p['board']==physical],structured_regions=True,
   physical_board=physical,build_root=scope,name=physical+'原理图',target=scope/'原生工程',
   report=scope/'原理图核验.json',packet_path=scope/'单页工具集成输入.json',exchange_target=scope/(physical+'原理图.epro2'))
  single_sheet_candidate(own)
  candidate=read(candidate_path(own));assert len(candidate['sheets'])==1
  assert len({p['位号'] for p in candidate['inventory']})==len(own['parts'])
  board_input.append({'板':physical,'位号':len(own['parts']),'端子':sum(len(p['pins']) for p in own['parts']),
   '候选单页输入':str(candidate_path(own).relative_to(ROOT)),'候选SHA256':sha(candidate_path(own)),
   '页数':1,'原生已消费':False})
 assert all(sha(live/f)==h for f,h in hashes.items())
 j=read(live/'原理图核验.json')
 j['当前源原生准备']={'版本':rev,'源文件SHA256':hashes,'源总位号':1616,'源总端子':5130,
  '当前源公共封装绑定':{'板上缺封装':0,'完整绑定JSONSHA256':sha(LIB/'封装绑定.json'),'封装库SHA256':sha(LIB/'可导入封装库.zip'),'逐脚功能差异':differences},
  '两板单页输入':board_input,'新增位号':sorted(by.keys()-prior.keys()),
  '辅助板':{'位号':22,'除了note全部字段等价':True,'完整PARTS相等':False,'note差异':note_changes,
   '本轮未重官方':True,'旧原生备注尚未同步':True,'ERC边界':'原始ERC及限定分类保持原版','整板放行':False},
  '边界':'仅作者最终源保全、公共库和一板一原理图一页候选输入；两板新原生/有效网表/ERC未执行；不覆盖旧版原生通过，不等于图面实际可读性验收。'}
 write(live/'原理图核验.json',j)
 print(dump({'准备版本':rev,'板上缺封装':0,'两板单页输入':board_input,'AUX备注差额':len(note_changes),'新原生已执行':False}))

def prepare_pd_stable_inputs():
 """仅保全作者839实例稳定源/BOM并验证逐行，不执行域源主程序。"""
 rev='RevAC-3e3b44b2029f';live=HW/'配电与水泵';dest=CACHE/'配电'/rev
 inputs={'设计源.py':(live/'设计源.py','3e3b44b2029f8ebe3ab3a68e5365672b742f064fb4475fcac479b9ad94ec6abf'),
  '作者同版BOM.csv':(live/'原生工程/系统辅助板BOM.csv','181c3e0e7b440346b86981c6ba07e851d6cbbb5961fdee35a0ccd803cbfb5387')}
 companion={'硬件/整车验证/动能回收.py':'b4df5cfcc076b84a64c37b16881c6c0ae295aa984779868436c6595d3627b72a',
  '软件/使用说明.md':'a8059df90d06b6ebaf47e75c97b9721e5d160d5d6a7784fefa10ce3f222f37ee',
  '软件/测试结果.md':'96a74139912b824c54308355ab09705f601c9d2c5ed04194e71a63100aeb575d'}
 assert all(sha(ROOT/p)==h for p,h in companion.items()),'作者五文件同版入口已改变'
 assert all(sha(p)==h for p,h in inputs.values())
 dest.mkdir(exist_ok=True)
 for name,(origin,expected) in inputs.items():
  target=dest/name
  if target.exists():assert sha(target)==expected,'同版保全输入冲突'
  else:shutil.copy2(origin,target)
 c=source('配电',revision=rev)
 assert len(c['parts'])==839 and sum(len(p['pins']) for p in c['parts'])==2510
 with (dest/'作者同版BOM.csv').open(encoding='utf-8-sig',newline='') as f:rows=list(csv.DictReader(f))
 assert len(rows)==839 and len({r['位号'] for r in rows})==839
 by={p['ref']:p for p in c['parts']};assert set(by)=={r['位号'] for r in rows}
 for row in rows:
  p=by[row['位号']]
  assert row['完整型号']==p['mpn'] and row['数值']==str(p['value']) and row['制造商']==p['manufacturer']
  assert row['源SHA256'].lower()==c['digest'] and row['制造放行']=='否'
 report=live/'核验.json';j=read(report)
 prior=j.get('当前源原生准备')
 if prior and prior['源文件SHA256']!=c['hashes'] and prior not in j.setdefault('原生输入准备历史',[]):
  j['原生输入准备历史'].append(copy.deepcopy(prior))
 j['当前源原生准备']={'源文件SHA256':c['hashes'],'作者同版BOMSHA256':inputs['作者同版BOM.csv'][1],
  '源实例':839,'源项目端子':2510,'BOM逐行核对':'PASS_SCOPED_REF_MODEL_VALUE_MANUFACTURER_SOURCE',
  '五文件同版SHA256':{**companion,'硬件/配电与水泵/设计源.py':c['digest'],'硬件/配电与水泵/原生工程/系统辅助板BOM.csv':inputs['作者同版BOM.csv'][1]},
  '稳定输入保全':str(dest.relative_to(ROOT)),'原生已消费':False,'旧97AA证据适用':False,
  '电气资格':'INPUT_PROTECTION_NOT_RELEASED','范围':'准备受影响配电单页工程；公共绑定、实际原生/ERC/网表各自验收，不继承旧731源。'}
 write(report,j)
 if not c['report'].exists():write(c['report'],{'native_validation':{},'输入保全':j['当前源原生准备']})
 c.update(structured_regions=True,name='配电板原理图',build_root=dest,
  packet_path=dest/'单页工具集成输入.json',exchange_target=dest/'配电板原理图.epro2')
 assert all(not p['onboard'] for p in c['parts'] if p['mpn']=='NH050R3600FE02')
 assert len([p for p in c['parts'] if p['ref'].startswith('J_R_') and '_HS_LIMIT' in p['ref']])==6
 print(dump({'保全839实例及2510端子':True,'BOM839行同版核对':True,'缓存':str(dest.relative_to(ROOT))}),flush=True)
 return c

def candidate_path(c):return c.get('build_root',CACHE/c['board'])/'单页图面候选.json'
def refresh_aggregate(c,j):
 formal=j.get('native_validation',{}).get('正式单板原生目录',{})
 if (c.get('physical_board') or c['board']=='配电') and formal:
  applicable=formal.get('对应源文件SHA256')==c['hashes']
  entry=ROOT/formal['入口'];folder=entry.parent
  actual={p.relative_to(folder).as_posix():sha(p) for p in folder.rglob('*') if p.is_file()}
  same_live=all((c['live_base']/f).is_file() and sha(c['live_base']/f)==h for f,h in c['hashes'].items())
  current=applicable and same_live and actual==formal.get('正式入口重开后目录SHA256')
  persisted=current and formal.get('实际入口独立重开',False) and (formal.get('显示修正官方保存关闭独立重开',False) or formal.get('正式入口SVG显示等价独立重开',False))
  net=formal.get('修正后官方网表',{}).get('JLCEDA_PRO',{})
  if not net and formal.get('有效官方网表') and formal.get('正式入口SVG显示等价独立重开'):
   net={'状态':'PASS','文件':formal.get('官方网表文件','missing'),'SHA256':formal.get('官方网表SHA256')}
  topology=current and net.get('状态')=='PASS' and (ROOT/net.get('文件','missing')).is_file() and sha(ROOT/net['文件'])==net['SHA256']
  j.update(native_source_hashes_match=applicable,current_source_hashes_match=same_live,
   native_validation_current_source=current,
   native_evidence_scope='仅'+c.get('physical_board',c['board'])+'正式工程；源/四文件/网表SHA分别确认，ERC与视觉保留缺口，不代表其他物理板',
   official_edit_save_reopen_status='PASS_CURRENT_PHYSICAL_BOARD_NATIVE_SHA' if persisted else 'PENDING_CURRENT_PHYSICAL_BOARD_NATIVE',
   effective_netlist_and_ERC_status='SCOPED_CURRENT_NETLIST_PASS_ERC_NOT_PASSED' if topology and not formal.get('ERC通过') else 'SEE_PHYSICAL_BOARD_NETLIST_AND_ERC')
  if 'gates' in j:j['gates'].update(official_edit_save_reopen=bool(persisted),effective_netlist=bool(topology),ERC=bool(current and formal.get('ERC通过')))
  return
 results=j.get('native_validation_boards',{}) if c['board'] in SPLIT_BOARDS else {c['board']:j.get('native_validation',{})}
 selected=[results.get(board,{}) for board in ('BMS板','外充板')] if c['board'] in SPLIT_BOARDS else list(results.values())
 applicable=all(r.get('板源文件SHA256')==c['hashes'] for r in selected)
 identities=[]
 for r in selected:
  native=c['base']/r.get('原生工程','missing')
  bom=c['base']/r.get('BOM文件','missing')
  exchange=c['base']/r.get('官方同版交换导出','missing')
  layout=r.get('图面组织核验',{})
  page_counts=layout.get('按板页数',{})
  expected_boards={c['physical_board']} if c.get('physical_board') else ({'驱动主板','辅助电源板','中央稳压模块','系统接线'} if c['board']=='FOC' else {next((b for b,v in results.items() if v is r),c['board'])})
  identities.append(bool(layout.get('一块板一张原理图')) and set(page_counts)==expected_boards and
   all(count==1 for count in page_counts.values()) and all(
   path.is_file() and sha(path)==expected for path,expected in (
    (native,r.get('原生工程SHA256')),(bom,r.get('BOM_SHA256')),(exchange,r.get('官方同版交换SHA256')))))
 current=applicable and all(identities)
 persisted=current and all(r.get('官方保存关闭独立重开') for r in selected)
 erc=current and all(r.get('官方ERC已执行') for r in selected)
 topology=current and all(r.get('有效官方网表') for r in selected)
 j.update(native_source_hashes_match=applicable,native_validation_current_source=current,
  native_evidence_scope='当前功能图原生/交换/BOM SHA逐项确认；各验收门独立' if current else '新功能图候选在制；旧版原生及PASS仅属于历史工程，不作为当前验收',
  official_edit_save_reopen_status='PASS_CURRENT_NATIVE_SHA' if persisted else 'PENDING_CURRENT_NATIVE_SAVE_CLOSE_REOPEN',
  effective_netlist_and_ERC_status=('PASS_CURRENT_NATIVE_SHA' if topology and erc and all(r.get('ERC通过') for r in selected) else 'CURRENT_NATIVE_TOPOLOGY_OR_ERC_FAIL') if erc else 'PENDING_CURRENT_NATIVE_TOPOLOGY_AND_ERC')
 if 'gates' in j:
  j['gates'].update(official_edit_save_reopen=persisted,effective_netlist=topology,ERC=erc and all(r.get('ERC通过') for r in selected))
 if 'status' in j:j['status']='CURRENT_FUNCTIONAL_NATIVE_VALIDATED_WITH_REMAINING_GATES' if persisted else 'FUNCTIONAL_SCHEMATIC_REPAIR_PENDING_NATIVE_VALIDATION'
 if '原生同步状态' in j:j['原生同步状态']='当前功能图工程SHA已绑定；保存关闭重开及拓扑/ERC分别见分板证据' if persisted else '新功能图候选在制；旧图PASS不能覆盖当前版面，等待同版原生保存关闭重开/拓扑/ERC'

def record_final_review(receipt):
 """并入既有记录，保留独立验收原文和原始未通过项。"""
 reports=[CACHE/'FOC/RevW-c64d726f5775/驱动主板/原理图核验.json',
  CACHE/'FOC/RevY-bb5d2188be94/储能模块/原理图核验.json',
  CACHE/'BMS/RevX-6b0d0383f697/原理图核验.json']
 for path in reports:
  j=read(path);j.setdefault('独立窄验收',{})['2026-10-05_10:31最终批']={
   '责任聊天':'01a10719-4838-7493-b1dd-87d621c10127','完整原文':receipt,
   '整板放行':False,'边界':'原文各板各源各正式文件SHA的分项结论，不把跨板摘要或ERCfalse改为PASS'}
  write(path,j)
  print(dump({'独立原文并入':str(path.relative_to(ROOT)),'SHA256':sha(path)}),flush=True)

def correct_final_evidence_indexes():
 """修正文案和正式网表索引，不改已执行的冻结库与工程。"""
 path=LIB/'封装补充依据.json';j=read(path);s=j['板级集成厂家封装']['SN74LXC1T45DBVR']
 s['被撤销的复用功能说明']=s['notes']
 s['notes']='PCB顶视DBV6：1VCCA、2GND、3A、4B、5DIR、6VCCB；DIR高为A到B，低为B到A。仅复用同封装铜面，不继承TS5A常开/常闭功能。阻焊钢网及工艺由PCB落实，不构成整板放行。'
 write(path,j)
 binding_path=LIB/'封装绑定.json';binding=read(binding_path)
 for group in binding['板级绑定'].values():
  for row in group['位号绑定']:
   if row.get('型号')=='SN74LXC1T45DBVR':
    basis=row.setdefault('依据',{});basis['被撤销的复用功能说明']=basis.get('notes');basis['notes']=s['notes']
 write(binding_path,binding)
 for rev,physical in [('RevW-c64d726f5775','驱动主板'),('RevY-bb5d2188be94','储能模块')]:
  c=source('FOC',revision=rev);c.update(physical_board=physical,report=c['base']/physical/'原理图核验.json')
  r=validation_result(c);f=r['正式单板原生目录'];actual=f['修正后官方网表']['JLCEDA_PRO']
  assert actual['状态']=='PASS' and sha(ROOT/actual['文件'])==actual['SHA256']
  f.setdefault('候选阶段官方网表证据保留',copy.deepcopy(f['官方网表证据']))
  f['官方网表证据']=copy.deepcopy(actual);f['正式网表索引口径']='正式入口实际保存关闭重开后导出的JLCEDA_PRO；候选与Protel2失败证据分别保留'
  update(c,r);print(dump({'正式网表索引':physical,'SHA256':actual['SHA256'],'核验SHA256':sha(c['report'])}),flush=True)

def record_pd_final_review(receipt):
 c=source('配电',revision='RevR-d85512098789');r=validation_result(c)
 r.setdefault('独立窄验收',{})['最终双IPT实际18脚']={'责任聊天':'01a10719-4838-7493-b1dd-87d621c10127','完整原文':receipt,'整板放行':False}
 update(c,r);print(dump({'配电最终窄审记录':str(c['report'].relative_to(ROOT)),'SHA256':sha(c['report'])}),flush=True)

def record_revz_independent_review(receipt):
 """并入独立只读窄审，订正正式双板适用关系；不重跑原生或继承ERC。"""
 c=source('FOC',revision='RevZ-197103dc101a')
 for board in ('驱动主板','储能模块'):
  own=dict(c,physical_board=board,parts=[p for p in c['parts'] if p['board']==board],report=c['base']/board/'原理图核验.json')
  r=validation_result(own);formal=r['正式单板原生目录']
  assert formal['对应源文件SHA256']==c['hashes']
  folder=(ROOT/formal['入口']).parent
  actual={p.relative_to(folder).as_posix():sha(p) for p in folder.rglob('*') if p.is_file()}
  assert actual==formal['正式入口重开后目录SHA256']
  net=formal['修正后官方网表']['JLCEDA_PRO'];assert net['状态']=='PASS' and sha(ROOT/net['文件'])==net['SHA256']
  r.setdefault('独立窄验收',{})['RevZ正式双板同源及增量']={
   '责任聊天':'01a10719-4838-7493-b1dd-87d621c10127',
   '状态':'PASS_SCOPED_REVZ_TWO_NATIVE_INDEX_NETS_INCREMENT_SHA',
   '完整原文':receipt,'本板正式目录SHA256':actual,'本板有效网表SHA256':net['SHA256'],
   '范围':'只读正式索引/四文件/全量逐脚/BOM与新增库成员；无新的官方执行或ERC分类，不放行整板。'}
  assert formal['ERC通过'] is False and formal['整板放行'] is False
  update(own,r)
 livepath=c['live_base']/CONFIG['FOC'][4];live=read(livepath)
 live['native_evidence_scope']='正式逐板证据见current_delivery_index：驱动/储能RevZ同源保存重开及有效逐脚网表通过；AUX三条note未同步，不能把双板分项推广为整个FOC域当前源完全同步。ERC/视觉各自保留缺口。'
 live['official_edit_save_reopen_status']='PASS_SCOPED_CURRENT_DRIVER_STORAGE_AUX_NOTE_SYNC_PENDING'
 live['effective_netlist_and_ERC_status']='SCOPED_CURRENT_DRIVER_STORAGE_NETLIST_PASS_ERC_NOT_PASSED'
 write(livepath,live)
 print(dump({'正式两板独立窄审原文已并入':True,'原生未改':True,
  '记录SHA256':{b:sha(c['base']/b/'原理图核验.json') for b in ('驱动主板','储能模块')}}))

def record_aux_manual_erc(report_path, independent_receipt):
 """人类当前正式入口的原始报告，与磁盘/实际输入关联；不改官方布尔。"""
 c=source('FOC',revision='RevV-8a893cee9b2b')
 c['parts']=[p for p in c['parts'] if p['board']=='辅助电源板']
 c.update(physical_board='辅助电源板',report=c['base']/'辅助电源板/原理图核验.json')
 r=validation_result(c);f=r['正式单板原生目录'];folder=(ROOT/f['入口']).parent
 manifest={p.relative_to(folder).as_posix():sha(p) for p in folder.rglob('*') if p.is_file()}
 assert manifest==f['正式入口重开后目录SHA256']
 raw_path=Path(report_path);payload=raw_path.read_bytes()
 assert hashlib.sha256(payload).hexdigest()=='cd915365c230bc8e75fcbd383c321da70f52179a7919489a020720b79e43b809'
 text=payload.decode('utf-8-sig');fatal=re.findall(r'\[致命错误\].*?元件 (\S+) 缺少',text)
 warnings=re.findall(r'\[警告\].*?导线 (\S+) \S+ 是单网络',text)
 info=re.findall(r'\[信息\].*?元件 (\S+) 的位号不符合',text)
 expected={'F_AUXBAT','F_AUXBUS','F_MOD1','F_MAIN1','F_MOD2','F_BACKUP_AUX','F_COIL_AUX'}
 receivers={'BACKUP_BUS_FUSED':'J_BACKUP_AUX_IN','COIL_AUX_IN':'J_COIL_AUX_IN',
  'MOD5_IN':'J_MOD5_IN','MOD15_IN':'J_MOD15_IN','MOD_MAIN12_IN':'J_MAIN12_IN'}
 assert set(fatal)==expected and len(fatal)==7 and set(warnings)==set(receivers) and len(warnings)==5 and len(info)==17
 live=source('FOC',revision='RevY-bb5d2188be94')
 # 执行活源最终PARTS，不能将早期定义grep结果冒充当前对象。
 current=runpy.run_path(str(live['live_base']/'设计数据.py'))
 actual={p['ref']:p for p in current['PARTS'] if p['board']=='辅助电源板'}
 normalized={p['ref']:p for p in live['parts'] if p['board']=='辅助电源板'}
 # source()另加导出字段，比较原作者完整对象使用保全作者源原始PARTS。
 frozen=runpy.run_path(str(live['base']/'设计数据.py'))
 assert actual=={p['ref']:p for p in frozen['PARTS'] if p['board']=='辅助电源板'}
 by={p['ref']:p for p in live['parts']};items=[]
 for ref in fatal:
  p=by[ref];assert not p['onboard'] and p.get('pcb_footprint_required') is False
  items.append({'severity':'fatal','ref':ref,'classification':'ACCEPTED_OFFBOARD_NOT_CONVERTED_TO_PCB',
   'mpn':p['mpn'],'pins':p['pins'],'installation':p['installation'],'pcb_footprint_required':False})
 for net in warnings:
  left=[(p['ref'],pin) for p in c['parts'] for pin,n in p['pins'].items() if n==net]
  j=by[receivers[net]];assert len(left)==1 and j['board']=='驱动主板' and j['onboard'] and j['pins']=={'1':net,'2':'GND'}
  items.append({'severity':'warn','net':net,'classification':'ACCEPTED_EXPLICIT_OFFBOARD_TO_OTHER_BOARD_HARNESS',
   'source_pin':left[0],'receiver_ref':j['ref'],'receiver_pins':j['pins'],
   'actual_receiver_official_netlist_sha256':'522c44ae1da26ebbcee6e0c594cab954f8839f62ade1834aede0c625467c58ed',
   'boundary':'必须实际线束连接；同名网络不是物理连接，无新增虚假辅助板插座。'})
 for ref in info:
  assert ref in actual
  items.append({'severity':'info','ref':ref,'classification':'ACCEPTED_PROJECT_DESIGNATOR_STYLE'})
 saved=c['report'].parent/'官方ERC原始报告.txt'
 if saved.exists():assert saved.read_bytes()==payload
 else:write_exclusive(saved,payload)
 result={'status':'PASS_SCOPED_AUX_MANUAL_ERC_CLASSIFICATION','raw_passed':False,
  'raw_counts':{'fatal':7,'error':0,'warn':5,'info':17},'分类接受':True,
  '原始报告':str(saved.relative_to(ROOT)),'原始报告SHA256':sha(saved),'导出时间':'2026-10-05 11:36:02',
  '正式入口':f['入口'],'正式目录SHA256':manifest,'原生实际执行输入SHA256':f['对应源文件SHA256'],
  '当前作者源SHA256':{name:sha(live['live_base']/name) for name in live['hashes']},
  '22位号原作者完整对象等价':True,'有效官方网表':f['官方网表证据'],'items':items,
  '人工版本关联边界':'报告自身无项目UUID/源SHA；用户声明当前正式AUX，四文件未变，22对象等价及全部错误集合命中作关联，不伪称报告内含SHA。',
  '独立限定验收':independent_receipt,
  '未覆盖':'保险启动/故障全清除I²t/导体热/线束L/R/总负载/电气设计及其他五板ERC；不改raw7/0/5/17为零，不放行layout。'}
 r['当前正式ERC分类验收']=result;f['ERC分类验收']=result
 assert f['ERC通过'] is False
 update(c,r)
 assert {p.relative_to(folder).as_posix():sha(p) for p in folder.rglob('*') if p.is_file()}==manifest
 print(dump({'状态':result['status'],'原始计数':result['raw_counts'],'原始报告SHA256':sha(saved),'核验JSONSHA256':sha(c['report']),'正式目录未变':True}))

def probe_candidate_erc_detail(c):
 """在隔离副本上保存后探测当前版本公开ERC返回，不改原候选。"""
 assert c['board']=='FOC' and c.get('e4_stable') and c.get('physical_board')=='中央稳压模块'
 document=read(c['report']);r=document['native_validation'];record=r['结构图面候选']
 entry=ROOT/record['候选完整eprj3目录']['工程索引'];folder=entry.parent
 before={p.relative_to(folder).as_posix():sha(p) for p in folder.rglob('*') if p.is_file()}
 assert before==record['候选完整目录文件SHA256']
 source_before={name:sha(Path(c['source_paths'][name])) for name in c['hashes']}
 assert source_before==c['hashes']
 attempt=Path(tempfile.mkdtemp(prefix='候选ERC明细隔离-回读-',dir=folder.parent))
 clone_folder=attempt/'完整工程';shutil.copytree(folder,clone_folder)
 clone_entry=clone_folder/entry.name
 clone_before={p.relative_to(clone_folder).as_posix():sha(p) for p in clone_folder.rglob('*') if p.is_file()}
 assert clone_before==before
 d=module('原理图交付');session=None
 e={'隔离副本工程索引':str(clone_entry.relative_to(ROOT)),'隔离副本初始目录SHA256':clone_before,
  '原候选目录SHA256_前':before,'源文件SHA256_前':source_before,'读取工具SHA256':TOOL_SHA,
  '官方运行环境':d.cli(EXE,'doctor')['value']}
 def invoke(code):return d.cli(EXE,'invoke','--session',session,'--ext-uuid','eda','--timeout','60000','--code',code)['value']
 try:
  sessions=d.cli(EXE,'session','list')['value']
  active=[s for s in sessions if s.get('status') not in ('closed','destroyed')]
  assert not active,('仍有活动官方会话，拒绝并行操作',active)
  e['调用前全部官方会话已关闭']=True
  session=d.cli(EXE,'open','--path',clone_entry.as_posix(),'--headless','true')['value']['sessionId']
  d.wait_for_project(invoke,attempts=90)
  pages=invoke('return await eda.dmt_Schematic.getAllSchematicPagesInfo();')
  assert len(pages)==1,('隔离候选非单页',pages)
  d.open_document(invoke,pages[0]['uuid'])
  active_page=invoke('return await eda.dmt_Schematic.getCurrentSchematicPageInfo();')
  assert active_page and active_page.get('uuid')==pages[0]['uuid'],('候选页未激活',active_page)
  e['页UUID']=pages[0]['uuid']
  e['官方保存']=invoke('return await eda.sch_Document.save();')
  assert e['官方保存'] is True,'隔离副本官方保存失败'
  time.sleep(9)
  e['保存后拓扑稳定等待秒']=9
  e['详细重载探测']=invoke('try{const raw=await eda.sch_Drc.check(true,false,true);return {type:Array.isArray(raw)?"array":typeof raw,raw};}catch(error){return {error:String(error)};}')
  e['布尔重载核验']=invoke('try{const raw=await eda.sch_Drc.check(true,false,false);return {type:typeof raw,raw};}catch(error){return {error:String(error)};}')
  detail=e['详细重载探测']
  raw=detail.get('raw') if isinstance(detail,dict) else None
  e['详细返回含逐条规则字段']=bool(detail.get('type')=='array' and isinstance(raw,list) and all(
   isinstance(x,dict) and 'rule' in x and isinstance(x.get('primitives'),list) for x in raw))
 except Exception as error:e['探针错误']=str(error)
 finally:
  if session:
   try:d.cli(EXE,'session','close','--session',session,'--destroy')
   except Exception as error:e['关闭错误']=str(error)
  try:
   sessions_after=d.cli(EXE,'session','list')['value']
   e['调用后活动官方会话']=[s for s in sessions_after if s.get('status') not in ('closed','destroyed')]
  except Exception as error:e['调用后会话读取错误']=str(error)
  original_after={p.relative_to(folder).as_posix():sha(p) for p in folder.rglob('*') if p.is_file()}
  clone_after={p.relative_to(clone_folder).as_posix():sha(p) for p in clone_folder.rglob('*') if p.is_file()}
  source_after={name:sha(Path(c['source_paths'][name])) for name in c['hashes']}
  e['原候选目录SHA256_后']=original_after;e['原候选未变化']=original_after==before
  e['隔离副本关闭后目录SHA256']=clone_after;e['源文件SHA256_后']=source_after
  e['冻结源未变化']=source_after==source_before
  e['探针完整']=not e.get('探针错误') and not e.get('关闭错误') and e.get('调用后活动官方会话')==[]
  record.setdefault('ERC明细探针历史',[]).append(e)
  write(c['report'],document)
 detail=e.get('详细重载探测',{})
 print(dump({'官方运行环境':e.get('官方运行环境'),'详细原始返回':detail,'布尔原始返回':e.get('布尔重载核验'),
  '详细返回含逐条规则字段':e.get('详细返回含逐条规则字段'),'原候选未变化':e.get('原候选未变化'),
  '冻结源未变化':e.get('冻结源未变化'),'探针完整':e.get('探针完整'),'探针错误':e.get('探针错误')}),flush=True)
 if not e['探针完整'] or not e['原候选未变化'] or not e['冻结源未变化']:
  raise AssertionError('隔离候选ERC探针未完整完成或原候选/源哈希不满足不变性')

def probe_current_erc_detail(c):
 """取正式工程或隔离候选的公开ERC返回；数组以外绝不充当逐条错误。"""
 r=validation_result(c)
 if r.get('结构图面候选') and c.get('candidate_only'):
  return probe_candidate_erc_detail(c)
 f=r['正式单板原生目录'];entry=ROOT/f['入口'];folder=entry.parent
 before={p.relative_to(folder).as_posix():sha(p) for p in folder.rglob('*') if p.is_file()}
 assert before==f['正式入口重开后目录SHA256']
 d=module('原理图交付');session=None;e={'正式入口':f['入口'],'正式目录SHA256':before,'读取工具SHA256':TOOL_SHA}
 def invoke(code):return d.cli(EXE,'invoke','--session',session,'--ext-uuid','eda','--timeout','60000','--code',code)['value']
 try:
  assert not [s for s in d.cli(EXE,'session','list')['value'] if s.get('status') not in ('closed','destroyed')]
  session=d.cli(EXE,'open','--path',entry.as_posix(),'--headless','true')['value']['sessionId'];d.wait_for_project(invoke,attempts=90)
  pages=invoke('return await eda.dmt_Schematic.getAllSchematicPagesInfo();');assert len(pages)==1;d.open_document(invoke,pages[0]['uuid'])
  e['官方返回']=invoke('const before=await eda.sys_Log.sort();const raw=await eda.sch_Drc.check(true,true,false);const logs=await eda.sys_Log.sort();return {boolean:raw,beforeLogs:before,afterLogs:logs};')
  e['详细重载探测']=invoke('try{const raw=await eda.sch_Drc.check(true,false,true);return {type:Array.isArray(raw)?"array":typeof raw,raw};}catch(error){return {error:String(error)};}')
  e['仅排除警告的辅助诊断']=invoke('return {passed:await eda.sch_Drc.check(false,false,false),scope:"公开strict=false仅区分fatal/error与warn，不是完整ERC通过"};')
  invoke('const ESYS_BottomPanelTab={LOG:"log"};eda.sys_PanelControl.openBottomPanel(ESYS_BottomPanelTab.LOG);return true;')
  time.sleep(2)
  e['公开标签页缓存']=invoke('eda.sys_PanelControl.closeBottomPanel();const tree=await eda.dmt_EditorControl.getSplitScreenTree();const tabs=[];function walk(node){for(const t of node.tabs||[])tabs.push({tabId:t.tabId,keys:Object.keys(t),dataKeys:Object.keys(t.data||{}),erc:t.data?.cachedSchDrcLog||null});for(const c of node.children||[])walk(c);}walk(tree);return tabs;')
  e['切换焦点后的公开标签页缓存']=invoke('const tree=await eda.dmt_EditorControl.getSplitScreenTree();const tabs=[];function walk(node,out){out.push(...node.tabs||[]);for(const c of node.children||[])walk(c,out);}walk(tree,tabs);const page=tabs.find(t=>t.data?.doctype===1);const home=tabs.find(t=>t.tabId==="tab_page1");if(!page||!home)return {skipped:true,types:tabs.map(t=>({tabId:t.tabId,type:t.data?.doctype}))};const switched=await eda.dmt_EditorControl.activateDocument(home.tabId);const after=[];walk(await eda.dmt_EditorControl.getSplitScreenTree(),after);const log=after.find(t=>t.tabId===page.tabId)?.data?.cachedSchDrcLog||null;const restored=await eda.dmt_EditorControl.activateDocument(page.tabId);return {switched,restored,log};')
  detail=e['详细重载探测'];e['可逐条分类']=detail.get('type')=='array' and all(isinstance(x,dict) and 'rule' in x and isinstance(x.get('primitives'),list) for x in detail.get('raw',[]))
  e['边界']='4.1.60未承诺详细重载；实返回非逐条对象数组时仅保留原始结果，日志不能证明未记录错误为0。未关闭规则或修改工程。'
 except Exception as error:e['读取失败']=str(error)
 finally:
  if session:d.cli(EXE,'session','close','--session',session,'--destroy')
  after={p.relative_to(folder).as_posix():sha(p) for p in folder.rglob('*') if p.is_file()}
  e['读取后正式目录SHA256']=after;e['正式目录未变']=after==before
  r.setdefault('当前正式ERC明细路径取证历史',[]).append(e);update(c,r)
 print(dump({'板':c.get('physical_board',c['board']),'布尔':e.get('官方返回',{}).get('boolean'),
  '日志条数':len(e.get('官方返回',{}).get('afterLogs',[])),'详细实际返回':e.get('详细重载探测'),
  '可逐条分类':e.get('可逐条分类'),'正式目录未变':e.get('正式目录未变'),'读取失败':e.get('读取失败')}),flush=True)

def associate_unchanged_board(board,oldrev,newrev,physical=None):
 """只关联逐板完整对象等价，不冒充重新执行官方保存。"""
 old=source(board,revision=oldrev);new=source(board,revision=newrev)
 if physical:
  old['parts']=[p for p in old['parts'] if p['board']==physical]
  new['parts']=[p for p in new['parts'] if p['board']==physical]
  old.update(physical_board=physical,report=old['base']/physical/'原理图核验.json')
 assert {p['ref']:p for p in old['parts']}=={p['ref']:p for p in new['parts']}
 r=validation_result(old);f=r['正式单板原生目录'];target=(ROOT/f['入口']).parent
 actual={p.relative_to(target).as_posix():sha(p) for p in target.rglob('*') if p.is_file()}
 assert actual==f['正式入口重开后目录SHA256']
 proof={'原始官方输入版本':oldrev,'关联当前输入版本':newrev,'原始源SHA256':old['hashes'],
  '当前源SHA256':new['hashes'],'完整逐板对象数':len(old['parts']),'完整PARTS字段完全相同':True,
  '正式完整目录SHA256':actual,'未重跑官方':True,'未改原始执行工具和库SHA':True,
  '边界':'只关联该物理板对象完全不变的当前源；ERC及电气未通过原样保留，不扩为其他板或整包放行'}
 r['逐板完整对象等价当前源']=proof;r['逐板版本适用']=True;f['逐板版本适用']=True
 update(old,r)
 print(dump({'逐板等价关联':physical or board,'对象':len(old['parts']),'证据SHA256':sha(old['report'])}),flush=True)

def update(c,result):
 source_paths=c.get('source_paths',{})
 verified_sources={}
 for f,h in c['hashes'].items():
  path=Path(source_paths.get(f,c['base']/f))
  assert sha(path)==h, '源改变，不能记入同版核验'
  verified_sources[f]={'path':str(path.resolve()),'sha256':h}
 if c.get('stable_manifest_path'):
  result['稳定输入快照']={'manifest_path':c['stable_manifest_path'],
   'manifest_sha256':c['stable_manifest_sha'],'source_files':verified_sources}
 j=read(c['report']) if c['report'].exists() else {}
 if c['board'] in SPLIT_BOARDS:
  splitpath=c['base']/'当前源-分板输入.json' if c.get('frozen') and not c.get('revision') else c['base']/c['board']/'分板输入.json'
  assert sha(splitpath)==c['split_input_sha256'],'分板输入改变'
  result['分板输入SHA256']=c['split_input_sha256']
  j.setdefault('native_validation_boards',{})[c['board']]=result
 else:j['native_validation']=result
 refresh_aggregate(c,j)
 if c.get('frozen'):
  result['当前电气源适用']=bool(j.get('native_validation_current_source'))
  if not j.get('native_validation_current_source'):
   j.update(native_validation_current_source=False,工具验证范围='保全旧源上的工具开发；不放行当前电气设计')
  else:j['工具验证范围']='保全输入与活源字节一致的本物理板正式原生分项；不放行电气或制造'
 if c.get('e4_stable'):
  result['当前作者源字节匹配']=all(sha(c['live_base']/f)==h for f,h in c['hashes'].items())
  j['工具验证范围']='E4作者同版稳定输入的逐实体板候选原生；各门及FAIL分别核证，不代替电气或制造放行'
 write(c['report'],j)
 if c.get('frozen'):
  live_report=c['live_base']/CONFIG[c['board']][4]
  live=read(live_report)
  check_key='单页工具验证'+('·'+c['revision'] if c.get('revision') else '')+('·'+c['physical_board'] if c.get('physical_board') else '')
  live.setdefault('integration_tool_checks',{}).setdefault(c['board'],{})[check_key]={
   '板源文件SHA256':c['hashes'],'当前源适用':False,'工具SHA256':c['tool_sha'],
   '证据文件':str(c['report'].relative_to(ROOT)),'证据SHA256':sha(c['report'])}
  scope=c.get('physical_board',c['board']);formal=result.get('正式单板原生目录',{});folder=result.get('官方文件夹工程',{})
  structured=result.get('结构图面候选',{})
  if structured:
   folder=structured.get('候选完整eprj3目录',{})
  delivery={
   '输入版本':c.get('revision'),'源文件SHA256':c['hashes'],
   '源文件与当前活源逐字节一致':all((c['live_base']/f).is_file() and sha(c['live_base']/f)==h for f,h in c['hashes'].items()),
   '关联双源包SHA256':c['digest'] if c['board'] in SPLIT_BOARDS else None,
   '摘要口径':'BMS/外充的关联双源包SHA256 = SHA256(json.dumps(两源文件SHA256字典,sort_keys=True).encode())；不是设计数据.py单文件SHA，也不是交换文件SHA' if c['board'] in SPLIT_BOARDS else '源文件SHA256以逐文件字典为准',
   '逐板版本适用':result.get('逐板版本适用',formal.get('逐板版本适用')),
   '当前版面正式eprj3入口':formal.get('入口'),
   '当前版面缓存eprj3入口':folder.get('工程索引'),
   '当前版面保存关闭重开':bool(formal.get('实际入口独立重开')) if formal else bool(structured.get('官方编辑保存独立重开',result.get('官方编辑保存独立重开'))),
   '当前版面逐脚BOM官方回读':bool(formal.get('实际入口逐脚BOM回读')) if formal else bool(structured.get('官方独立重开交换逐脚回读',structured.get('官方重开全量逐脚BOM',result.get('官方独立重开交换逐脚回读')))),
   '当前版面有效官方网表':bool(formal.get('实际入口独立重开') and formal.get('有效官方网表')) if formal else bool(structured.get('有效官方网表',folder.get('有效官方网表',result.get('有效官方网表')))),
   '当前版面ERC通过':bool(formal.get('实际入口独立重开') and formal.get('ERC通过')) if formal else bool(structured.get('ERC通过',folder.get('ERC通过',result.get('ERC通过')))),
   '正式入口验收失败':formal.get('入口验收失败'),
   '当前版面ERC':((structured.get('官方ERC结果') or result.get('官方ERC结果') or {}).get('summary')
    or (structured.get('官方ERC结果') or result.get('官方ERC结果') or {}).get('raw')),
   '当前版面ERC分类':structured.get('ERC分类'),
   '图面':{'视觉验收':structured.get('视觉验收'),'实际图面核对':structured.get('图面实际阅读核对')} if structured else result.get('单板图面核验',{'视觉验收':'当前布局未完成官方图面渲染验收'}),
   '既有完整历史目录仅供参考':[{'入口':v['官方文件夹工程'].get('工程索引'),
     '本版面适用':False,'说明':'源相同也不代表版面相同；不能继承本次图面和原生通过'}
     for v in j.get('native_validation_history',{}).get(c['board'],[]) if v.get('官方文件夹工程',{}).get('工程索引')],
   '证据文件':str(c['report'].relative_to(ROOT)),'证据SHA256':sha(c['report']),
   '完整证据字段':('native_validation_boards.'+c['board']) if c['board'] in SPLIT_BOARDS else 'native_validation',
   '总状态':'候选及缺口如上；此索引不替代完整核验，不构成整板电气或制造放行'}
  if structured:
   candidate_delivery=copy.deepcopy(delivery)
   candidate_delivery.update(当前版面正式eprj3入口=None,正式入口验收失败=None,
    当前版面保存关闭重开=bool(structured.get('官方编辑保存独立重开')),
    当前版面逐脚BOM官方回读=bool(structured.get('官方独立重开交换逐脚回读',structured.get('官方重开全量逐脚BOM'))),
    当前版面有效官方网表=bool(structured.get('有效官方网表')),
    当前版面ERC通过=bool(structured.get('ERC通过')),
    当前版面ERC=((structured.get('官方ERC结果') or {}).get('summary')
     or (structured.get('官方ERC结果') or {}).get('raw')),
    当前版面ERC分类=structured.get('ERC分类'),
    图面={'视觉验收':structured.get('视觉验收'),
     '官方SVG':structured.get('官方SVG'),'SVG_SHA256':structured.get('SVG_SHA256'),
     '实际图面核对':structured.get('图面实际阅读核对'),
     '说明':'候选图面证据，不代替实际正式入口图面'})
   live.setdefault('integration_candidate_index',{})[scope]=candidate_delivery
  if formal:
   delivery['当前版面ERC']=formal.get('修正后原始ERC',formal.get('原始ERC',{})).get('summary')
   delivery['当前版面ERC分类']=formal.get('ERC分类')
   manual=result.get('当前正式ERC分类验收')
   if manual and manual.get('正式目录SHA256')==formal.get('正式入口重开后目录SHA256'):
    assert manual['raw_passed'] is False and formal['ERC通过'] is False
    delivery['当前版面ERC']=manual['raw_counts']
    delivery['当前版面ERC分类']={'status':manual['status'],'详细错误集合可得':True,
     'raw_passed':manual['raw_passed'],'分类接受':manual['分类接受'],
     '原始报告':manual['原始报告'],'原始报告SHA256':manual['原始报告SHA256'],
     'items':manual['items'],'人工版本关联边界':manual['人工版本关联边界'],'未覆盖':manual['未覆盖']}
   delivery['图面']={'视觉验收':formal.get('图面视觉验收'),
    '官方SVG':formal.get('官方SVG'),'SVG_SHA256':formal.get('SVG_SHA256'),
    '实际图面核对':formal.get('实际正式图面阅读',formal.get('独立设计窄审',{}).get('独立实际正式图面阅读')),
    '说明':'只关联已发布正式入口；候选图面阅读见独立候选索引及完整核验'}
   live.setdefault('current_delivery_index',{})[scope]=delivery
  elif not structured:
   # Preview evidence is not the published entry. Never erase an existing
   # formal path or change its source version while developing a candidate.
   live.setdefault('integration_candidate_index',{})[scope]=delivery
  write(live_report,live)

def validation_result(c):
 if c.get('preview_only') and not c['report'].exists():return {}
 j=read(c['report'])
 if c.get('preview_only') and c['board'] in SPLIT_BOARDS:
  # The sibling physical board may already have a candidate record in this
  # exact-source file. It is not evidence for a board not built yet.
  return j.get('native_validation_boards',{}).get(c['board'],{})
 return j['native_validation_boards'][c['board']] if c['board'] in SPLIT_BOARDS else j['native_validation']

def preserve_previous_validation(c,build_dir):
 j=read(c['report'])
 if c['board'] in SPLIT_BOARDS and c['board'] not in j.get('native_validation_boards',{}):return
 old=copy.deepcopy(validation_result(c))
 if not old:return
 history=j.setdefault('native_validation_history',{}).setdefault(c['board'],[])
 if any(x.get('原生工程SHA256')==old.get('原生工程SHA256') and x.get('板源文件SHA256')==old.get('板源文件SHA256') for x in history):return
 origin=c['base']/old['原生工程'] if old.get('原生工程') else None
 if origin and origin.is_file() and sha(origin)==old.get('原生工程SHA256'):
  prior=old.get('官方网表格式核验',{}).get('Protel2',{});clone=ROOT/prior.get('隔离副本','missing')
  if not clone.is_file() or sha(clone)!=sha(origin):
   clone=build_dir/'修图前原件.eprj2';write_exclusive(clone,origin.read_bytes())
  old['历史原生工程保全']={'文件':str(clone.relative_to(ROOT)),'SHA256':sha(clone)}
 if packet(c).is_file():
  saved=build_dir/'修图前集成输入.json';write_exclusive(saved,packet(c).read_bytes())
  old['历史集成输入保全']={'文件':str(saved.relative_to(ROOT)),'SHA256':sha(saved)}
 bom=c['base']/old['BOM文件'] if old.get('BOM文件') else None
 if bom and bom.is_file() and sha(bom)==old.get('BOM_SHA256'):
  saved=build_dir/('修图前_'+bom.name);write_exclusive(saved,bom.read_bytes())
  old['历史BOM保全']={'文件':str(saved.relative_to(ROOT)),'SHA256':sha(saved)}
 exchange=c['base']/old['官方同版交换导出'] if old.get('官方同版交换导出') else None
 if exchange and exchange.is_file() and sha(exchange)==old.get('官方同版交换SHA256'):
  saved=build_dir/'修图前官方交换.epro2';write_exclusive(saved,exchange.read_bytes())
  old['历史官方交换保全']={'文件':str(saved.relative_to(ROOT)),'SHA256':sha(saved)}
 old['历史汇总状态']={key:j[key] for key in ('official_edit_save_reopen_status','effective_netlist_and_ERC_status','native_validation_current_source','native_evidence_scope','status','原生同步状态','gates') if key in j}
 history.append(old);write(c['report'],j)

def enrich_bom(c):
 """实际元件属性回读之外，明确合入同SHA源的线束装配采购合同。"""
 result=validation_result(c);assert result['板源文件SHA256']==c['hashes']
 path=c['base']/result['BOM文件']
 with path.open(encoding='utf-8-sig',newline='') as f:
  reader=csv.DictReader(f);fields=list(reader.fieldnames);rows=list(reader)
 parts={p['ref']:p for p in c['parts']}
 assert len(rows)==len(parts) and {r['位号'] for r in rows}==set(parts)
 for field in ('配套件','配套件来源'):
  if field not in fields:fields.append(field)
 for row in rows:
  accessories=parts[row['位号']].get('accessories','')
  row['配套件']=accessories if isinstance(accessories,str) else dump(accessories)
  row['配套件来源']='来自同SHA源合同 '+c['digest']+'；未声称机械/封装验收' if accessories else '同SHA源未列配套件'
 with path.open('w',encoding='utf-8-sig',newline='') as f:
  writer=csv.DictWriter(f,fieldnames=fields);writer.writeheader();writer.writerows(rows)
 result['BOM_SHA256']=sha(path)
 result['BOM源合同补列']={'字段':['配套件','配套件来源'],'源SHA256':c['digest'],'来源':'同SHA源各位号accessories；非官方原生属性，不代表机械/工艺验收','数量':sum(bool(parts[r['位号']].get('accessories')) for r in rows)}
 update(c,result)

def outward(shape,api):
 """标准库P.rotation可能与实际线方向冲突；以引脚线几何确定外接方向。"""
 num,x,y,rotation=api.pin_info(shape);path=shape.split('^^')[2].split('~')[0]
 tokens=re.findall('[MmLlHhVv]|'+api.NUM,path);points=[];i=0;px=py=0
 while i<len(tokens):
  cmd=tokens[i];i+=1;size=1 if cmd.upper() in ('H','V') else 2
  v=list(map(float,tokens[i:i+size]));i+=size
  if cmd.upper() in ('M','L'):px,py=(v[0]+px,v[1]+py) if cmd.islower() else v
  elif cmd.upper()=='H':px=v[0]+px if cmd.islower() else v[0]
  elif cmd.upper()=='V':py=v[0]+py if cmd.islower() else v[0]
  points.append((px,py))
 ix,iy=max(points,key=lambda v:abs(v[0]-x)+abs(v[1]-y));vx,vy=ix-x,iy-y
 assert vx or vy,(num,path)
 return (-180 if vx>0 else 180,0) if abs(vx)>=abs(vy) else (0,-100 if vy>0 else 100)

def physical_connection_contract(parts,bindings):
 """Keep every source terminal traceable; collapse only explicit same-net aliases."""
 nets={};nc=set();aliases=[]
 for p in parts:
  mapping=bindings[p['ref']]['引脚映射'];assert set(mapping)==set(p['pins'])
  for logical,net in p['pins'].items():
   physical=mapping[logical];key=(p['ref'],physical)
   if logical!=physical:aliases.append({'ref':p['ref'],'source_terminal':logical,'physical_pad':physical,'net':net})
   if net.startswith('NC_'):
    assert key not in nets,(key,'共铜别名不能同时开路和有网');nc.add(key)
   else:
    assert key not in nc and (key not in nets or nets[key]==net),(key,'同铜别名异网')
    nets[key]=net
 return nets,nc,aliases

def complete_functional_groups(parts,title,is_rail):
 """芯片加实际相邻外围为完整块；不按件数拆分或猜BOM最近芯片。"""
 by={p['ref']:p for p in parts};assert len(by)==len(parts)
 basename=lambda ref:ref.rsplit('__',1)[-1]
 nets=collections.defaultdict(set)
 for p in parts:
  for net in p['pins'].values():
   if net.startswith('NC_') or is_rail(basename(net)):continue
   nets[net].add(p['ref'])
 adjacency={r:set() for r in by}
 for refs in nets.values():
  for r in refs:adjacency[r].update(refs-{r})
 anchors={r for r,p in by.items() if basename(r).startswith(('U','PSU')) and len(p['pins'])>=4}
 import heapq
 queue=[(0,r,r) for r in sorted(anchors)];heapq.heapify(queue);best={}
 while queue:
  distance,anchor,r=heapq.heappop(queue)
  if r in best:continue
  best[r]=(distance,anchor)
  for neighbour in sorted(adjacency[r]):
   if neighbour not in best:heapq.heappush(queue,(distance+1,anchor,neighbour))
 groups={r:title+'·'+anchor for r,(distance,anchor) in best.items()}
 # Source-designated local bypass capacitors stay with their actual IC.
 short={basename(r):r for r in by}
 for r in by:
  local=basename(r)
  candidates=[local[2:], 'U_'+local[2:]] if local.startswith('C_') else []
  matching=[short[name] for name in candidates if name in short and short[name] in anchors]
  if len(matching)==1:groups[r]=title+'·'+matching[0]
 remaining=set(by)-set(groups)
 while remaining:
  seed=min(remaining);component={seed};todo=[seed];remaining.remove(seed)
  while todo:
   r=todo.pop()
   for neighbour in sorted(adjacency[r]&remaining):
    component.add(neighbour);todo.append(neighbour);remaining.remove(neighbour)
  terminal=min(component,key=lambda r:(not basename(r).startswith('J'),r))
  for r in component:groups[r]=title+'·独立支路-'+terminal
 assert set(groups)==set(by)
 return groups

def complete_circuit_positions(group,preparations,is_rail):
 """以芯片针脚及外围连接深度布局；不以BOM顺序、器件数量切块。"""
 by={p['ref']:p for p in group};assert len(by)==len(group)
 def signal(net):
  short=net.rsplit('__',1)[-1]
  return not net.startswith('NC_') and not is_rail(net) and not re.fullmatch(
   r'(?:.*_)?(?:GND|AGND|DGND|VCC|VDD|VSS|[+-]?\d+(?:V\d*)?|EP)',short)
 nets=collections.defaultdict(set)
 for p in group:
  for net in p['pins'].values():
   if signal(net):nets[net].add(p['ref'])
 adjacency={r:set() for r in by}
 for refs in nets.values():
  for r in refs:adjacency[r].update(refs-{r})
 anchors=[p for p in group if p['ref'].startswith(('U','PSU','J_IC_'))]
 if not anchors:anchors=[p for p in group if p['ref'].startswith('J')]
 anchor=max(anchors,key=lambda p:(len(preparations[p['ref']][1]),p['ref'])) if anchors else min(group,key=lambda p:p['ref'])
 ar=anchor['ref'];pinpoints={str(n):(x,y) for n,x,y,_ in preparations[ar][1]}
 mapped={str(preparations[ar][3]['引脚映射'].get(n,n)):net for n,net in anchor['pins'].items()}
 contacts=collections.defaultdict(list)
 for n,net in mapped.items():
  if signal(net):contacts[net].append(pinpoints[n])
 # Multi-source BFS retains the side and pin row of the real anchor contact
 # through RC, dividers and gate chains, rather than distributing by count.
 import heapq
 queue=[];best={}
 for r,p in by.items():
  if r==ar:continue
  hits=[xy for net in p['pins'].values() for xy in contacts.get(net,())]
  if hits:
   x=sum(v[0] for v in hits)/len(hits);y=sum(v[1] for v in hits)/len(hits)
   heapq.heappush(queue,(1,-1 if x<0 else 1,y,r))
 while queue:
  depth,side,y,r=heapq.heappop(queue)
  if r==ar or r in best:continue
  best[r]=(depth,side,y)
  for neighbour in sorted(adjacency[r]-{ar}):
   if neighbour not in best:heapq.heappush(queue,(depth+1,side,y,neighbour))
 # Capacitors sharing the exact same two electrical nets are parallel
 # branches, regardless of whether that rail's name is recognized. Draw
 # that topology as a horizontal bank rather than a long vertical list.
 banks=collections.defaultdict(list);parallel=collections.defaultdict(list)
 for r,p in by.items():
  if r.startswith('C') and len(p['pins'])==2:
   parallel[tuple(sorted(p['pins'].values()))].append(r)
 bank_members=set()
 for bus,members in parallel.items():
  if len(members)>1:
   banks[bus].extend(sorted(members));bank_members.update(members)
   for r in members:best.pop(r,None)
 disconnected=sorted(set(by)-set(best)-{ar}-bank_members)
 # Single supply-only bypasses and standalone branches stay near the IC.
 for r in disconnected:
  p=by[r]
  if r.startswith('C') and all(not signal(net) for net in p['pins'].values()):
   bus=tuple(sorted(net for net in p['pins'].values() if not re.search(r'(?:^|_)(?:A|D)?GND$',net)))
   banks[bus].append(r)
  else:best[r]=(0,0,0)
 bounds={r:preparations[r][2] for r in by}
 step=math.ceil(max(400,max(v[2]-v[0]+280 for v in bounds.values()))/5)*5
 left=max((depth for depth,side,y in best.values() if side<0),default=0)
 ax=200+(left+1)*step;ay=math.ceil(max(340,200-bounds[ar][1])/5)*5
 positions={ar:(ax,ay)};occupied=collections.defaultdict(list)
 for r,(depth,side,relative_y) in sorted(best.items(),key=lambda v:(v[1],v[0])):
  a,b,z,d=bounds[r]
  if side==0:
   x=ax;y=max(ay+bounds[ar][3]+220,200-b)
  else:x=ax+side*depth*step;y=max(ay+relative_y,200-b)
  y=math.ceil(y/5)*5
  # Same electrical branch remains in its own depth column. Only move down
  # to reserve complete symbol/attribute space, never to a different circuit.
  for low,high in sorted(occupied[x]):
   if y+d+55<=low:break
   if y+b-55<high:y=math.ceil((high-b+55)/5)*5
  occupied[x].append((y+b-55,y+d+55));positions[r]=(x,y)
 # Parallel bypass banks are electrical arrays adjacent to the IC, not one
 # long vertical list. Wrap by their actual symbol/attribute span, not a count.
 bank_width=max(2200,max(positions[r][0]+bounds[r][2]+420 for r in positions))
 bank_y=max(positions[r][1]+bounds[r][3] for r in positions)+220
 for bus,members in sorted(banks.items()):
  x=200;line_height=0
  for r in members:
   a,b,z,d=bounds[r];span=max(350,z-a+240)
   if x+span>bank_width-100 and x>200:
    x=200;bank_y+=line_height+90;line_height=0
   positions[r]=(math.ceil((x-a)/5)*5,math.ceil((bank_y-b)/5)*5)
   x+=span;line_height=max(line_height,d-b+70)
  bank_y+=line_height+90
 width=math.ceil(max(positions[r][0]+bounds[r][2]+420 for r in by)/5)*5
 height=math.ceil(max(positions[r][1]+bounds[r][3]+180 for r in by)/5)*5
 return positions,max(2200,width),max(1250,height)

def signal_path_rows(blocks):
 """真实输出→输入关系从左至右；反馈环相邻，整块按实际宽度换行。"""
 if not blocks:return []
 outputs=collections.defaultdict(set);inputs=collections.defaultdict(set)
 for i,b in enumerate(blocks):
  for net in b['metadata'].get('signal_outputs',[]):outputs[net].add(i)
  for net in b['metadata'].get('signal_inputs',[]):inputs[net].add(i)
 edges={i:set() for i in range(len(blocks))}
 for net,drivers in outputs.items():
  if len(drivers)!=1:continue
  source=next(iter(drivers));edges[source].update(inputs[net]-{source})
 # Tarjan SCC: latch/feedback networks are one circuit layer, not fake DAGs.
 serial=0;stack=[];active=set();index={};low={};components=[]
 def visit(v):
  nonlocal serial
  index[v]=low[v]=serial;serial+=1;stack.append(v);active.add(v)
  for w in sorted(edges[v]):
   if w not in index:visit(w);low[v]=min(low[v],low[w])
   elif w in active:low[v]=min(low[v],index[w])
  if low[v]==index[v]:
   component=[]
   while True:
    w=stack.pop();active.remove(w);component.append(w)
    if w==v:break
   components.append(sorted(component))
 for v in edges:
  if v not in index:visit(v)
 owner={v:i for i,component in enumerate(components) for v in component}
 incoming={i:set() for i in range(len(components))}
 for v,neighbours in edges.items():
  for w in neighbours:
   if owner[v]!=owner[w]:incoming[owner[w]].add(owner[v])
 remaining=set(incoming);sequence=[]
 while remaining:
  ready=sorted((i for i in remaining if not incoming[i]&remaining),key=lambda i:min(components[i]))
  assert ready,'反馈环必须先收缩'
  sequence.extend(blocks[v] for i in ready for v in components[i]);remaining.difference_update(ready)
 assert sorted(map(id,sequence))==sorted(map(id,blocks))
 return [sequence]

def functional_sheets(c,bindings,raw,api):
 """Arrange verified local circuits on one complete sheet per physical board."""
 if c['board']=='FOC':
  assert c.get('physical_board') in ('驱动主板','中央稳压模块','辅助电源板'), '生成原理图须选择一块实体板；整域绑定不等于多板合工程'
 assert c.get('structured_regions'), '新图面必须走功能拓扑组织，禁止回退旧排列版'
 import heapq,inspect
 engine_path=HW/'FOC驱动与储能/工具/分板原理图.py';engine_sha=sha(engine_path)
 engine=runpy.run_path(str(engine_path))
 scope=engine['generate'].__globals__;original_function=scope['_function']
 original_positions=scope['_positions']
 if c['board']=='FOC' and c.get('structured_regions'):
  foc_base_positions=original_positions
  foc_local_width=scope['WIDTH']
  scope['_board']=lambda p,b:p['board']
  def structured_foc_positions(group,preparations,title):
   scope['WIDTH']=4300 if title=='限流回充·主功率与输出隔离' else max(foc_local_width,2200) if c.get('physical_board')=='中央稳压模块' else foc_local_width
   storage_port_positions={
    '高压端·熔断停流分流、隔离及预充':{
     'J_SC_BUS':(150,330),'F_SC_HV':(470,330),'R_SC_HV_OFF_SHUNT':(740,330),
     'Q_SC_HVA':(1050,330),'Q_SC_HVB':(1570,330),
     'R_SC_HV_GS':(1260,750),'R_SC_HV_GATE_LOCK':(1260,960),
     'R_SC_HV_PRE':(1650,970),'U_SC_HV_PRE':(650,850)},
    '低压端·熔断、隔离预充及总量分流':{
     'F_SC_LV':(200,330),'Q_SC_LVA':(680,330),'Q_SC_LVB':(1220,330),
     'R_SC_CAP_CURRENT':(1720,330),'R_SC_LV_GS':(940,740),
     'R_SC_LV_GATE_LOCK':(940,960),'R_SC_LV_PRE':(1470,1000),'U_SC_LV_PRE':(360,850)}}
   if c.get('physical_board')=='中央稳压模块' and title in storage_port_positions:
    pos=storage_port_positions[title]
    assert set(pos)=={p['ref'] for p in group},('储能端口隔离预充合同改变，须重新组织',title)
    return pos
   if c.get('physical_board')=='中央稳压模块' and title=='20节超容串联功率':
    # 20节实体串联链：两列各10节，每列自下而上为低端到高端。逐节常驻检修
    # 泄放支路已于2026-10-07整体取消（改手持泄放棒），本页只摆20节实体电容。
    pos={}
    for n in range(1,21):
     column,rank=divmod(n-1,10)
     pos[f'C_SC_CELL{n}']=(350+column*620,190+(9-rank)*130)
    assert set(pos)=={p['ref'] for p in group},'超容串联链变化，须按源重新组织'
    scope['WIDTH']=max(scope.get('WIDTH',0),1800)
    scope['HEIGHT']=max(scope.get('HEIGHT',0),1600)
    return pos
   if c.get('physical_board')=='中央稳压模块' and title in ('双向功率相1','双向功率相2'):
    phase=title[-1]
    pos={f'Q_SC_{phase}H':(650,360),f'Q_SC_{phase}L':(650,850),
     f'R_SC_G{phase}H':(360,360),f'R_SC_GS{phase}H':(360,550),
     f'R_SC_G{phase}L':(360,850),f'R_SC_GS{phase}L':(360,1030),
     f'L_SC_PHASE{phase}':(1180,660),f'R_SC_PHASE{phase}':(1540,660),
     f'R_SC_BOOT{phase}':(270,160),f'D_SC_BOOT{phase}':(520,160),
     f'C_SC_BOOT{phase}':(960,330),f'C_SC_HV_FILM{phase}':(180,730),
     f'R_SC_CSA{phase}':(1290,940),f'R_SC_CSB{phase}':(1730,940),
     f'C_SC_CS{phase}':(1510,1080)}
    assert set(pos)=={p['ref'] for p in group},('储能相桥实际回路变化，须按新源重新组织',title)
    return pos
   power_positions={
    '输入功率链·01 端子、主熔断与手动断路':{'J_BAT_1':(220,330),'F1':(560,330),'K1':(1080,330),'J_BAT_2':(220,950)},
    '输入功率链·04 主接触器及并联预充':{'K2':(900,700),'F_PRE':(420,300),'R_PRE':(860,300)},
    '输入功率链·05 主分流、母线电容与钳位':{
     'R_BAT':(330,420),'D_TVS':(330,870),'R_BLEED':(330,1110),
     **{f'C_BUS{i}':(670+((i-1)%4)*265,610+((i-1)//4)*350) for i in range(1,9)}},
    '输入功率链·06 桥输入分流':{'R_BRIDGE':(500,420)},
    '限流回充·主功率与输出隔离':{
     'F_RG_IN':(220,330),'C_RG_IN':(430,700),
     'Q_RG_H':(820,330),'Q_RG_L':(820,850),
     'R_RG_GH':(550,330),'R_RG_GSH':(550,530),
     'R_RG_GL':(550,850),'R_RG_GSL':(550,1050),
     'L_RG':(1250,610),'R_RG_PHASE':(1560,610),'C_RG_OUT':(1810,940),
     'Q_RG_ISOA':(2100,400),'Q_RG_ISOB':(2600,400),'R_RG_ISO_GS':(2340,800),
     'D_RG_OUT':(3020,340),'R_RG_OUTPUT':(3340,340),'F_RG_OUT':(3680,340)}}
   for n in (1,2):
    power_positions[f'输入功率链·0{n+1} 反向阻断第{n}级']={
     f'U_BAT_BLOCK{n}':(850,820),f'Q_BAT_BLOCK{n}':(1000,330),
     f'C_BAT_BLOCK_VCAP{n}':(430,710),f'C_BAT_BLOCK_IN{n}':(220,440),f'C_BAT_BLOCK_OUT{n}':(1460,440)}
   if title in power_positions:
    pos=power_positions[title]
    assert set(pos)=={p['ref'] for p in group},('输入实际功率链变更，须按新拓扑重排',title)
    return pos
   module_inputs={'主板15V模块':('PSU15_EXT','J_MOD15_IN'),
    '主板主12V模块':('PSU12_MAIN_EXT','J_MAIN12_IN'),'主板5V模块':('PSU5_EXT','J_MOD5_IN')}
   if title in module_inputs:
    psu,connector=module_inputs[title]
    pos={psu:(800,520),connector:(220,380),'C_'+psu+'_IN':(440,850),
     'C_'+psu+'_OUT':(1210,710),'R_'+psu+'_PRELOAD':(1490,950)}
    assert set(pos)=={p['ref'] for p in group},('模块输入/输出边界变更',title)
    return pos
   if title=='电容温度检测' and any(p['ref'].startswith('NTC_SC_') for p in group):
    pos={}
    for n,(x,y) in enumerate(((240,260),(770,260),(1300,260),(505,760),(1035,760)),1):
     pos[f'R_SC_TEMP{n}']=(x,y)
     pos[f'C_SC_TEMP{n}']=(x+165,y+150)
     pos[f'NTC_SC_{n}']=(x,y+260)
    assert set(pos)=={p['ref'] for p in group},('温度采样/板外探头变更，须重排',title)
    return pos
   if title=='限流回充·许可锁存与健康':
    # Permission/health enter from the left; the latch and successive AND
    # stages are adjacent. Decoupling remains next to its actual IC rather
    # than forcing three 14-pin parts into a generic peripheral column.
    pos={'R_RG_FAULT_PU':(260,170),'U_RG_CTRL_BUF':(260,370),
     'J_REGEN_ALLOW':(200,620),'R_RG_ALLOW_PD':(200,800),
     'R_RG_REQ_PD':(200,1020),'U_MAIN_LOGIC1':(800,430),
     'C_U_MAIN_LOGIC1':(1040,200),'U_RG_LATCH':(800,925),
     'C_U_RG_LATCH':(1050,1070),'U_MAIN_LOGIC2':(1450,650),
     'C_U_MAIN_LOGIC2':(1660,1000)}
    assert set(pos)=={p['ref'] for p in group},('回充许可链变更，须按新拓扑重排',title)
    return pos
   return foc_base_positions(group,preparations,title)
  scope['_positions']=structured_foc_positions
  original_positions=structured_foc_positions
  main_symbol=scope['_symbol']
  def power_contact_symbol(p,b,api_dict):
   ref=p['ref'];mapping=b['引脚映射']
   if p['mpn'] in ('BSC050N10NS5ATMA1','BSC070N10LS5ATMA1'):
    # Infineon BSC050N10NS5 Rev2.3 p1: G4, S1..3, D5..8.
    # All physical source/drain pin identities remain explicit and distinct.
    assert set(p['pins'])==set(map(str,range(1,9)))
    assert p.get('factory_pin_functions')=={'1':'S','2':'S','3':'S','4':'G','5':'D','6':'D','7':'D','8':'D'}
    assert len({p['pins'][n] for n in ('1','2','3')})==len({p['pins'][n] for n in ('5','6','7','8')})==1
    shapes=[];pins=[]
    def pin(old,x,y,angle,name):
     number=mapping[old];shapes.append(scope['_pin'](number,x,y,angle,name));pins.append((number,x,y,angle))
    def line(*points):shapes.append(scope['_line'](points))
    pin('4',-60,0,180,'G')
    for n,x in zip(('1','2','3'),(-10,0,10)):
     pin(n,x,60,270,'S');line((x,45),(x,35))
    for n,x in zip(('5','6','7','8'),(-15,-5,5,15)):
     pin(n,x,-60,90,'D');line((x,-45),(x,-35))
    line((-15,-35),(15,-35));line((-10,35),(10,35))
    line((-45,0),(-30,0));line((-30,-20),(-30,20))
    line((-20,-20),(-20,-5));line((-20,5),(-20,20))
    line((0,-35),(0,-20),(-20,-20));line((-20,20),(0,20),(0,35))
    line((12,20),(22,20),(17,5),(12,20));line((12,5),(22,5))
    line((17,5),(17,-20),(0,-20));line((17,20),(17,35),(0,35))
    return {'head':{'x':0,'y':0},'shape':shapes},pins,(-60,-60,40,60)
   if p['mpn']=='7443783533220':
    assert set(p['pins'])=={'1','2','3','4'} and p['pins']['2'].startswith('NC_') and p['pins']['3'].startswith('NC_')
    hide_winding_names=(c.get('physical_board')=='中央稳压模块' and ref in
     {'L_SC_P1_POWER','L_SC_P2_POWER','L_SC_PORT_HV','L_SC_PORT_LV'})
    if hide_winding_names:
     assert p.get('factory_pin_functions',{}).get('1')=='winding start' and p.get('factory_pin_functions',{}).get('4')=='winding end'
    shapes=[];pins=[]
    for n,x,y,d,label in [('1',-60,0,180,'winding start'),('4',60,0,0,'winding end'),('2',-20,70,270,'MECH'),('3',20,70,270,'MECH')]:
     number=mapping[n];display_name='' if hide_winding_names and n in ('1','4') else label
     shapes.append(scope['_pin'](number,x,y,d,display_name));pins.append((number,x,y,d))
    shapes.append(scope['_line'](((-45,0),(-30,0),(-25,-10),(-20,0),(-15,-10),(-10,0),(-5,-10),(0,0),(5,-10),(10,0),(15,-10),(20,0),(25,-10),(30,0),(45,0))))
    # Internal mechanical connection is drawing-only, not a PCB wire/extra node.
    shapes.append(scope['_line'](((-20,55),(-20,45),(20,45),(20,55))))
    return {'head':{'x':0,'y':0},'shape':shapes},pins,(-60,-10,60,70)
   if ref not in ('K1','K2','R_BAT','R_BRIDGE','R_SC_PHASE1','R_SC_PHASE2','R_SC_CAP_CURRENT','R_SC_BUS_TOTAL','R_SC_CAP_TOTAL'):return main_symbol(p,b,api_dict)
   wanted={'1','2','A1','A2'} if ref=='K2' else {'1','2','3','4'}
   assert set(p['pins'])==wanted,('功率触点或Kelvin合同变化',ref)
   shapes=[];pins=[]
   def pin(old,x,y,angle,name):
    number=mapping[old];shapes.append(scope['_pin'](number,x,y,angle,name));pins.append((number,x,y,angle))
   def line(*points):shapes.append(scope['_line'](points))
   if ref=='K1':
    for old,x,y,angle in [('1',-110,-45,180),('2',110,-45,0),('3',-110,45,180),('4',110,45,0)]:pin(old,x,y,angle,'触点')
    for y in (-45,45):
     line((-95,y),(-65,y));line((-65,y),(60,y-25));line((65,y),(95,y))
    bounds=(-110,-70,110,60)
   elif ref=='K2':
    pin('1',-110,-50,180,'触点');pin('2',110,-50,0,'触点')
    pin('A1',-110,70,180,'线圈');pin('A2',110,70,0,'线圈')
    line((-95,-50),(-65,-50));line((-65,-50),(60,-80));line((65,-50),(95,-50))
    line((-95,70),(-35,70));line((35,70),(95,70))
    line((-35,50),(35,50),(35,90),(-35,90),(-35,50));bounds=(-110,-80,110,90)
   else:
    pin('1',-110,0,180,'Force+');pin('2',110,0,0,'Force−')
    pin('3',-45,80,270,'Kelvin+');pin('4',45,80,270,'Kelvin−')
    line((-95,0),(-25,0));line((25,0),(95,0));line((-25,-10),(25,-10),(25,10),(-25,10),(-25,-10))
    line((-45,65),(-45,0));line((45,65),(45,0));bounds=(-110,-10,110,80)
   return {'head':{'x':0,'y':0},'shape':shapes},pins,bounds
  scope['_symbol']=power_contact_symbol
  if c.get('physical_board')=='驱动主板' and not c.get('e4_stable'):
   # The buck switching node and isolation-source node are actual power
   # conductors, not remote signals. Keep every connected physical terminal
   # on one wire component; named ports must never replace this chain.
   regen_power_nodes={'RG_HV','RG_SW1','RG_L_OUT','RG_OUT_PRE','RG_ISO_S',
    'RG_DIODE_A','RG_SHUNT_IN','RG_FUSED_OUT'}
   assert regen_power_nodes <= {net for p in c['parts'] for net in p['pins'].values()},'回充功率节点合同改变，须按实际源重排'
   original_main_power=scope['is_main_power']
   scope['is_main_power']=lambda net:net in regen_power_nodes or original_main_power(net)
  if c.get('physical_board')=='中央稳压模块' and not c.get('e4_stable'):
   storage_power_nodes={'SC_HV_OFF_AFTER','SC_CAP_SHUNT_IN','SC_HV_PRE_R','SC_LV_PRE_R',*(f'SC_CELL_{n}' for n in range(1,21))}
   assert storage_power_nodes <= {net for p in c['parts'] for net in p['pins'].values()},'储能功率路径合同改变，须重新组织'
   original_storage_power=scope['is_main_power']
   scope['is_main_power']=lambda net:net in storage_power_nodes or original_storage_power(net)
 if c.get('structured_regions'):
  original_cap_symbol=scope['_symbol']
  def capacitor_symbol(p,b,api_dict):
   symbol,pins,bounds=original_cap_symbol(p,b,api_dict)
   ref=p['ref'].rsplit('__',1)[-1]
   # CELL/BUS names identify placement, not capacitor polarity. Only remove
   # the engine's two final '+' strokes for explicitly ceramic families.
   if (ref.startswith('C') and len(p['pins'])==2 and not p.get('polarized')
       and (p['mpn'].startswith(('CGA','CGJ','GRM','GCM')) or p['mpn']=='C3225X7R1E226M250AB')
       and ('CELL' in ref or 'BUS' in ref)):
    assert len(symbol['shape'])==10 and all(s.startswith('PL~') for s in symbol['shape'][-2:]),ref
    symbol=dict(symbol,shape=symbol['shape'][:-2])
   return symbol,pins,bounds
  scope['_symbol']=capacitor_symbol
 if c.get('physical_board')=='辅助电源板':
  if any(p['ref']=='F_AUXBAT' for p in c['parts']):scope['WIDTH']=2600
  def auxiliary_power_positions(group,preparations,title):
   refs={p['ref'] for p in group}
   if title=='辅助电源分配' and 'U_AUX_EFUSE' in refs:
    # Two real input branches merge before the eFuse; the protected output is
    # at the right. UV/OV feedback, current limit and dV/dt stay at the IC.
    pos={'J_AUXBAT_IN':(170,280),'D_AUXBAT':(485,265),
     'J_AUXBUS_IN':(170,720),'D_AUXBUS':(485,705),
     'D_AUXTVS':(650,960),'C_AUX_EFUSE_IN':(870,1030),
     'U_AUX_EFUSE':(1110,485),'J_AUX_OR_OUT':(1640,470),
     'R_AUX_UV_T':(750,200),'R_AUX_UV_B':(750,370),
     'R_AUX_OV_T':(750,560),'R_AUX_OV_B':(750,730),
     'R_AUX_ILIM1':(1260,1040),'R_AUX_ILIM2':(1490,1040),
     'C_AUX_EFUSE_DVDT':(1510,805)}
    if 'F_AUXBAT' in refs:
     pos.update({'F_AUXBAT':(170,150),'F_AUXBUS':(170,960),
      'F_MOD1':(2120,280),'F_MAIN1':(2120,600),'F_MOD2':(2120,920)})
    assert refs==set(pos),('辅助电源实际拓扑变动，需要重新布图',sorted(refs^set(pos)))
    return pos
   return original_positions(group,preparations,title)
  scope['_positions']=auxiliary_power_positions
  original_power=scope['is_main_power']
  scope['is_main_power']=lambda net:net in {'AUX_OR_RAW','AUX_IN','AUX_BAT_FUSED','AUX_BUS_FUSED'} or original_power(net)
 basename=lambda ref:ref.rsplit('__',1)[-1]
 if c['board']!='FOC':
  scope['WIDTH']=2200
  # Keep this physical board's explicitly external terminals on the same
  # schematic. Their addIntoPcb/installation classification remains unchanged.
  scope['_board']=lambda p,b:'驱动主板'
  original_symbol=scope['_symbol'];original_positions=scope['_positions'];original_aux=scope['is_auxiliary_power'];original_main=scope['is_main_power']
  def symbol_with_namespace(p,b,api_dict):
   q=copy.deepcopy(p);q['ref']=basename(p['ref'])
   q['pins']={pin:basename(net) for pin,net in p['pins'].items()}
   if c['board']=='配电' and q['mpn']=='BCX53-16,115':
    assert q['names']=={'1':'E','2':'C','3':'B'},'PNP必须先按厂家1E/2C/3B修正源'
    shapes=[];pins=[];mapping=b['引脚映射']
    for old,x,y,angle,name in [('3',-60,0,180,'B'),('1',0,-60,90,'E'),('2',0,60,270,'C')]:
     n=mapping[old];shapes.append(scope['_pin'](n,x,y,angle,name));pins.append((n,x,y,angle))
    for points in [((-45,0),(-25,0)),((-25,-20),(-25,20)),
                   ((-25,-10),(0,-30),(0,-45)),((-25,10),(0,30),(0,45)),
                   ((-14,-22),(-23,-12),(-11,-13))]:shapes.append(scope['_line'](points))
    return {'head':{'x':0,'y':0},'shape':shapes},pins,(-60,-60,25,60)
   if c['board']=='配电' and q['mpn']=='BAS116,215':
    assert q['names']=={'1':'A','2':'NC','3':'K'} and q['pins']['2'].startswith('NC_')
    shapes=[];pins=[];mapping=b['引脚映射']
    for old,x,y,angle,name in [('3',-60,0,180,'K'),('1',60,0,0,'A'),('2',0,60,270,'NC')]:
     n=mapping[old];shapes.append(scope['_pin'](n,x,y,angle,name));pins.append((n,x,y,angle))
    for points in [((-45,0),(-15,0)),((15,0),(45,0)),((-15,-10),(-15,10)),
                   ((15,-10),(-15,0),(15,10),(15,-10))]:shapes.append(scope['_line'](points))
    return {'head':{'x':0,'y':0},'shape':shapes},pins,(-60,-20,60,60)
   if c['board']=='配电' and q['mpn'] in ('PSMN1R1-100CSE','NVMFS6B25NLT1G','NVMFS6B14NLT1G','NVMFS6H800NLT1G','NVMFS015N10MCLT1G'):
    mapping=b['引脚映射'];functions=b['依据']['pin_functions'];shapes=[];pins=[]
    physical=set(mapping.values());assert physical==set(functions)
    for func in ('S','D'):
     logical=[n for n,v in mapping.items() if functions[v]==func]
     assert len({q['pins'][n] for n in logical})==1,(q['ref'],func,'共铜/内部并联异网')
     numbers=sorted({mapping[n] for n in logical},key=int);y=70 if func=='S' else -70
     for i,n in enumerate(numbers):
      x=(i-(len(numbers)-1)/2)*10
      shapes.append(scope['_pin'](n,x,y,270 if func=='S' else 90,func));pins.append((n,x,y,270 if func=='S' else 90))
      shapes.append(scope['_line'](((x,y+(15 if func=='D' else -15)),(x,-35 if func=='D' else 35))))
     shapes.append(scope['_line']((((-(len(numbers)-1)/2)*10,-35 if func=='D' else 35),(((len(numbers)-1)/2)*10,-35 if func=='D' else 35))))
    gate=next(n for n,v in functions.items() if v=='G');shapes.append(scope['_pin'](gate,-60,0,180,'G'));pins.append((gate,-60,0,180))
    for points in [((-45,0),(-30,0)),((-30,-20),(-30,20)),((-20,-20),(-20,-5)),((-20,5),(-20,20)),
                   ((0,-35),(0,-20),(-20,-20)),((-20,20),(0,20),(0,35)),
                   ((12,20),(22,20),(17,5),(12,20)),((12,5),(22,5)),((17,5),(17,-20),(0,-20)),((17,20),(17,35),(0,35))]:
     shapes.append(scope['_line'](points))
    if q['mpn']=='PSMN1R1-100CSE':
     assert len(physical)==12 and q['top_mounting_surface']['PCB_solder_pad'] is False
     assert q['top_mounting_surface']['net']==q['pins']['7'],'顶部D合同未跟真实Drain网'
    return {'head':{'x':0,'y':0},'shape':shapes},pins,(-60,-70,40,70)
   if q['ref'].startswith('Q') and q['mpn']=='BSS131H6327XTSA1':
    assert q.get('names')=={'1':'G','2':'S','3':'D'},'BSS131逐脚函数需匹配作者原厂合同'
    mapping=b['引脚映射'];shapes=[];pins=[]
    for old,x,y,angle,name in [('1',-60,0,180,'G'),('3',0,-60,90,'D'),('2',0,60,270,'S')]:
     n=mapping[old];shapes.append(scope['_pin'](n,x,y,angle,name));pins.append((n,x,y,angle))
    for points in [((-45,0),(-30,0)),((-30,-20),(-30,20)),((-20,-20),(-20,-5)),((-20,5),(-20,20)),
     ((0,-45),(0,-20),(-20,-20)),((-20,20),(0,20),(0,45)),
     ((12,20),(22,20),(17,5),(12,20)),((12,5),(22,5)),((17,5),(17,-20),(0,-20)),((17,20),(17,35),(0,35))]:shapes.append(scope['_line'](points))
    return {'head':{'x':0,'y':0},'shape':shapes},pins,(-60,-60,40,60)
   if q['ref'].startswith('Q') and q['mpn'] in ('SiR882ADP-T1-GE3','SiS892ADN-T1-GE3'):
    # Real eight-pad MOS symbol: retain every physical pin, while exposing
    # the bridge's drain/source/gate topology instead of a generic box.
    assert set(q['pins'])==set(map(str,range(1,9)))
    assert len({q['pins'][n] for n in ('1','2','3')})==1
    assert len({q['pins'][n] for n in ('5','6','7','8')})==1
    shapes=[];pins=[];mapping=b['引脚映射']
    def add_pin(old,x,y,angle,name):
     n=mapping[old];shapes.append(scope['_pin'](n,x,y,angle,name));pins.append((n,x,y,angle))
    add_pin('4',-60,0,180,'G')
    for i,n in enumerate(('5','6','7','8')):add_pin(n,-15+i*10,-70,90,'D')
    for i,n in enumerate(('1','2','3')):add_pin(n,-10+i*10,70,270,'S')
    for points in [((-45,0),(-30,0)),((-30,-20),(-30,20)),((-20,-20),(-20,-5)),((-20,5),(-20,20)),
     ((-15,-55),(15,-55)),((0,-55),(0,-20),(-20,-20)),((-20,20),(0,20),(0,55)),((-10,55),(10,55)),
     ((12,20),(22,20),(17,5),(12,20)),((12,5),(22,5)),((17,5),(17,-20),(0,-20)),((17,20),(17,35),(0,35))]:
     shapes.append(scope['_line'](points))
    return {'head':{'x':0,'y':0},'shape':shapes},pins,(-60,-70,40,70)
   if c.get('structured_regions') and re.fullmatch(r'T_BAL\d+',q['ref']):
    assert q['mpn']=='750312504' and set(q['pins'])=={'1','2','4','5','6','7','9','10'}
    mapping=b['引脚映射'];shapes=[];pins=[]
    for old,x,y,angle in [('1',-80,-60,180),('2',-80,-30,180),('9',-80,30,180),('10',-80,60,180),
                         ('4',80,-60,0),('5',80,-30,0),('6',80,30,0),('7',80,60,0)]:
     n=mapping[old];shapes.append(scope['_pin'](n,x,y,angle,q['names'][old]));pins.append((n,x,y,angle))
    for sign in (-1,1):
     shapes.append(scope['_line'](((sign*65,-60),(sign*50,-60),(sign*50,-30),(sign*65,-30))))
     shapes.append(scope['_line'](((sign*65,30),(sign*50,30),(sign*50,60),(sign*65,60))))
     winding=[(sign*50,-45),(sign*25,-45)]
     for y in range(-40,41,10):winding.extend(((sign*40,y),(sign*25,y+5)))
     winding.append((sign*50,45));shapes.append(scope['_line'](winding))
    shapes.extend([scope['_line'](((-7,-50),(-7,50))),scope['_line'](((7,-50),(7,50))),
     scope['_line'](((-43,-43),(-37,-43),(-37,-37),(-43,-37),(-43,-43))),
     scope['_line'](((37,-43),(43,-43),(43,-37),(37,-37),(37,-43)))])
    return {'head':{'x':0,'y':0},'shape':shapes},pins,(-80,-60,80,60)
   return original_symbol(q,b,api_dict)
  def positions_with_namespace(group,preparations,title):
   scope['WIDTH']=2200;scope['HEIGHT']=1250
   def position_ref(p):
    ref=basename(p['ref'])
    if ref in ('J_CORE_P1','J_CORE_P2','J_SC_CORE_P1','J_SC_CORE_P2'):return 'J_GENERIC_'+ref
    if ref.startswith(('U','PSU')) and len(preparations[p['ref']][1])==4:return 'J_IC_'+ref
    return ref
   names={position_ref(p):p['ref'] for p in group};assert len(names)==len(group)
   local=[dict(p,ref=position_ref(p)) for p in group]
   pd_stage=re.search(r'(AUX|P5|P21)(?:(_S2))?保护链·(\d+) ',title) if c['board']=='配电' else None
   if pd_stage and pd_stage.group(3) in ('01','02','03','05','07','08','09'):
    tag,second,stage=pd_stage.groups();tag+=second or '';pos={}
    if stage=='01':
     pos={f'F_{tag}':(160,330),f'D_{tag}_REV':(490,330),f'R_{tag}_HS_OC':(1000,330),f'D_{tag}_TVS':(700,760)}
    elif stage=='02':
     pos={f'J_R_{tag}_HS_LIMIT1':(220,330),f'R_{tag}_HS_LIMIT1':(800,330),
          f'J_R_{tag}_HS_LIMIT2':(220,730),f'R_{tag}_HS_LIMIT2':(800,730)}
    elif stage=='03':
     pos={f'Q_{tag}_HS1':(470,330),f'Q_{tag}_HS2':(1170,330),f'D_{tag}_HS_POST_TVS':(830,710),
          f'C_{tag}_HS_BOOTSTRAP':(470,1040),f'C_{tag}_HS_DS':(1170,1040)}
     if f'C_{tag}_HS_OUT_BULK' in names:pos[f'C_{tag}_HS_OUT_BULK']=(1660,710)
    elif stage=='05':
     pos={f'D_{tag}_HS_GATE_CHARGE':(220,330),f'Q_{tag}_HS_GATE_OFF1':(800,330),f'Q_{tag}_HS_GATE_OFF2':(1410,330),
          f'R_{tag}_HS_GATE_OFF1':(800,790),f'R_{tag}_HS_GATE_OFF2':(1410,790),f'R_{tag}_HS_SLEW':(220,790)}
    elif stage in ('07','08'):
     node='VOUT' if stage=='07' else 'SENSE'
     pos={f'R_{tag}_HS_{node}_PIN':(210,350),f'R_{tag}_HS_{node}_CLAMP':(1260,350),f'D_{tag}_HS_{node}_PIN':(1260,800),
          **{f'C_{tag}_HS_{node}_PIN{n}':(510+(n-1)%2*320,350+(n-1)//2*450) for n in range(1,5)}}
    else:
     pos={f'D_{tag}_HS_NEG':(360,240),f'D_{tag}_HS_NEG2':(360,580),f'D_{tag}_HS_NEG3':(360,920),
          **{f'R_{tag}_HS_NEG_BAL{n}':(900,240+(n-1)*340) for n in range(1,4)},f'R_{tag}_HS_BLEED':(1440,580)}
    assert set(pos)==set(names),(tag,stage,'明确拓扑坐标缺失或多余',set(pos)^set(names))
    return {names[name]:point for name,point in pos.items()}
   if c.get('structured_regions') and title.startswith('主动均衡功率·均衡通道'):
    i=int(re.search(r'均衡通道(\d+)',title).group(1))
    pos={f'F_BAL{i}':(170,180),f'T_BAL{i}':(1210,590),
     f'Q_BAL_P{i}':(870,590),f'Q_BAL_S{i}':(1560,590),
     f'RG_BAL_P{i}':(610,590),f'RGS_BAL_P{i}':(660,810),f'RS_BAL_P{i}':(870,1010),
     f'RG_BAL_S{i}':(1810,590),f'RGS_BAL_S{i}':(1810,810),f'RS_BAL_S{i}':(1560,1010),
     f'R_SNUB_BAL_P{i}':(950,190),f'C_SNUB_BAL_P{i}':(950,370),
     f'R_SNUB_BAL_S{i}':(1540,190),f'C_SNUB_BAL_S{i}':(1750,370)}
    for cap in range(1,7):pos[f'C_BAL_CELL{i}_{cap}']=(230+(cap-1)%2*220,440+(cap-1)//2*250)
    assert set(pos)==set(names),('均衡通道电路变更，须重排',i,set(pos)^set(names))
    return {names[name]:point for name,point in pos.items()}
   if c['board']=='BMS板' and title in ('主动均衡控制·U_BAL_LOW','主动均衡控制·U_BAL_TOP'):
    controller=title.rsplit('·',1)[1];pos={controller:(1050,610)}
    rest=[p for p in local if p['ref']!=controller]
    assert len(rest)<=11,'主动均衡控制外围超过预留槽位'
    for i,p in enumerate(rest):
     col,row=divmod(i,6);pos[p['ref']]=(240 if col==0 else 1840,190+row*175)
    return {names[name]:point for name,point in pos.items()}
   if c['board']=='外充板' and all(r in names for r in ('Q_CHG_H1','Q_CHG_L1','Q_CHG_H2','Q_CHG_L2','L_CHARGER')):
    pos={'Q_CHG_H1':(600,330),'Q_CHG_L1':(600,850),'Q_CHG_H2':(1650,330),'Q_CHG_L2':(1650,850),
     'RG_Q_CHG_H1':(300,330),'RGS_Q_CHG_H1':(350,520),'RG_Q_CHG_L1':(300,850),'RGS_Q_CHG_L1':(350,1040),
     'RG_Q_CHG_H2':(1400,330),'RGS_Q_CHG_H2':(1410,520),'RG_Q_CHG_L2':(1400,850),'RGS_Q_CHG_L2':(1400,1040),
     'C_CHG_BST1':(800,250),'C_CHG_BST2':(1900,250),
     'R_CHG_L_SERIES_A':(800,610),'R_CHG_L_SERIES_B':(1010,610),'L_CHARGER':(1230,610)}
    assert set(names)==set(pos),('四开关主功率电路变化，须重排',set(names)^set(pos))
    return {names[name]:point for name,point in pos.items()}
   buck=next((tag for tag in ('RK','RADIO','P5','P21') if f'U_{tag}' in names and f'QH_{tag}' in names and f'QL_{tag}' in names and f'L_{tag}' in names),None) if c['board']=='配电' else None
   if buck:
    tag=buck;byref={p['ref']:p for p in local}
    assert byref[f'L_{tag}']['pins']=={'1':tag+'_SW','2':{'RK':'RK12','RADIO':'RADIO5','P5':'P5_RAW','P21':'P21_RAW'}[tag]},'降压输出网络改变，须重新核实际功率路径'
    pos={f'U_{tag}':(1350,1000),f'QH_{tag}':(1900,550),f'QL_{tag}':(1900,1000),f'L_{tag}':(2450,775)}
    control={'R_VIN':(650,580),'C_VIN':(1000,580),'R_EN_SER':(650,800),'R_UVB':(1000,800),
     'R_RT':(650,1040),'C_SS':(1000,1040),'R_PG':(650,1280),'C_VCC':(1650,750),
     'R_BST':(1650,300),'C_BST':(1900,300),'R_ILIM':(2200,1350),'C_ILIM':(2550,1350),
     'R_FBT':(2100,1600),'R_FBB':(2450,1600),'R_COMP':(1400,1600),'C_COMP':(1750,1600),
     'C_CP':(1400,1880),'R_FF':(2850,1600),'C_FF':(3200,1600)}
    for key,point in control.items():
     prefix,suffix=key.split('_',1);ref=f'{prefix}_{tag}_{suffix}'
     if ref in names:pos[ref]=point
    for bank,origin in [('IN',(300,300)),('OUT',(2450,1080))]:
     members=sorted(r for r in names if re.fullmatch(f'C_{tag}_{bank}\\d+',r) or (bank=='OUT' and r==f'C_{tag}_HF'))
     for i,ref in enumerate(members):pos[ref]=(origin[0]+i*300,origin[1])
    assert set(pos)==set(names),('同步降压完整控制/半桥/滤波电路变化，须重排',tag,set(pos)^set(names))
    # Input bank -> vertical half bridge -> inductor -> output bank. Feedback
    # and compensation are below the controller, not a BOM satellite column.
    scope['WIDTH']=4500;scope['HEIGHT']=2250
    return {names[name]:point for name,point in pos.items()}
   if c['board']=='配电' and 'U_PD' in names and 'J_RK_PD' in names:
    # Full source-control circuit: CC/bias at the IC, real port to its right,
    # shunt / back-to-back gate path between them, and discharge below.
    pos={'U_PD':(1600,650),'J_RK_PD':(4200,650),
     'C_PD_VTX':(700,300),'C_PD_CC1':(700,650),'C_PD_CC2':(700,1000),
     'R_PD_HIPWR':(700,1350),'R_PD_CTL_PU2':(1100,1350),
     'C_PD_VAUX':(2300,300),'C_PD_VDD':(2300,650),'R_PD_GD_PD':(2300,1000),
     'R_PD_DISCH_PU':(2300,1350),'R_PD_SENSE':(2300,1700),
     'R_PD_SHUNT':(3100,300),'Q_PD_PORT2':(3100,800),
     'R_PD_GATE':(2700,800),'D_PD_PORT_GS':(2700,1150),'R_PD_PORT_OFF':(3250,1150),
     'R_PD_DSCG_PU':(3650,1150),'C_PD_PORT':(4200,1250),
     'R_PD_DISCH1':(3100,1550),'R_PD_DISCH2':(3550,1550),'R_PD_PASSIVE_DISCH':(4200,1700),
     'C_PD_SENSE1':(2300,2050),'C_PD_SENSE2':(2750,2050),
     'C_PD_DVDD_100_1':(400,1900),'C_PD_DVDD_100_2':(800,1900),
     'C_PD_DVDD_10_1':(1200,1900),'C_PD_DVDD_10_2':(1600,1900)}
    assert set(pos)==set(names),('USB-PD完整电路改变，须按实际归属更新',set(pos)^set(names))
    scope['WIDTH']=4850;scope['HEIGHT']=2450
    return {names[name]:point for name,point in pos.items()}
   if c['board']=='配电' and 'U_PDET_CMP1' in names:
    # Four independent measured quantities run left -> divider/clamp ->
    # comparator; the wired permission output and dry-contact return at right.
    pos={'U_PDET_CMP1':(3300,550),'C_PDET_CMP1':(3300,1100),
     'R_PDET_ZERO_T':(650,1500),'R_PDET_ZERO_B':(1100,1500),
     'C_PDET_REF_IN':(1550,1500),'R_PDET_REF_LOW_T':(2000,1500),'R_PDET_REF_HIGH_T':(2500,1500),
     'R_PDET_PULL':(3950,250),'Q_PUMP_CERT':(4450,550),'R_PUMP_CERT_GPD':(4450,1000),
     'R_PUMP_CERT_LED':(5050,550),'J_BMS_PUMPS_OFF':(5650,550)}
    for i,channel in enumerate(('G5','G21','V5','V21')):
     x=450+i*700
     pos.update({f'R_PDET_{channel}_T':(x,350),f'R_PDET_{channel}_B':(x,800),f'D_PDET_{channel}':(x,1150)})
    assert set(pos)==set(names),('泵关断四通道采样归属改变',set(pos)^set(names))
    scope['WIDTH']=6250;scope['HEIGHT']=1950
    return {names[name]:point for name,point in pos.items()}
   if c['board']=='配电' and 'U_ADC_ISO' in names:
    # Three measured voltages each run through their own divider, filter and
    # two clamps into the isolation switch. Keep complete channels in rows.
    pos={'U_ADC_ISO':(2400,900),'C_ADC_ISO':(2400,350),'R_ADC_SEL_PD':(2400,1450)}
    for channel,y in (('V5',400),('V21',900),('VPACK',1400)):
     pos.update({f'R_{channel}T':(300,y),f'R_{channel}B':(700,y+100),
      f'C_{channel}':(1000,y+100),f'D_{channel}H':(1370,y),
      f'D_{channel}L':(1750,y+100),f'R_{channel}_BLEED':(3000,y)})
    assert set(pos)==set(names),('ADC隔离完整通道归属改变，须重新组织',set(pos)^set(names))
    scope['WIDTH']=3550;scope['HEIGHT']=2000
    return {names[name]:point for name,point in pos.items()}
   # Keep a controller and its complete peripheral paths together. The local
   # canvas grows to the actual circuit; do not force it into a twelve-part tile.
   pos,width,height=complete_circuit_positions(local,{name:preparations[ref] for name,ref in names.items()},lambda net:scope['_rail'](basename(net)))
   scope['WIDTH']=width;scope['HEIGHT']=height
   return {names[name]:point for name,point in pos.items()}
  scope['_symbol']=symbol_with_namespace;scope['_positions']=positions_with_namespace
  scope['is_auxiliary_power']=lambda net:original_aux(basename(net))
  power_nets=set()
  power_switch_models={'SiR882ADP-T1-GE3','SiS892ADN-T1-GE3','IPT015N10N5ATMA1',
   'IPB021N10NM5LF2ATMA1','BSC050N10NS5ATMA1','PSMN1R1-100CSE',
   'NVMFS6B25NLT1G','NVMFS6B14NLT1G','NVMFS6H800NLT1G','NVMFS015N10MCLT1G'}
  for p in c['parts']:
   ref=basename(p['ref']);functions=p.get('factory_pin_functions',p.get('names',p.get('pinmap_metadata',{}).get('pin_functions',{})))
   for pin,net in p['pins'].items():
    if re.search(r'(?:^|__|_)(?:A|D)?GND$',net):continue
    function=functions.get(pin,'')
    power_switch=ref.startswith('Q') and (not c.get('structured_regions') or p['mpn'] in power_switch_models)
    if (ref.startswith(('F','L')) and len(p['pins'])==2) or (power_switch and re.fullmatch(r'(?:D|S|Drain|Source)(?:\d+)?',function,re.I)):power_nets.add(net)
  scope['is_main_power']=lambda net:net in power_nets or original_main(basename(net))
 connect_source=inspect.getsource(scope['_connect_board'])
 assert connect_source.count("if net=='GND':")==1
 connect_source=connect_source.replace("if net=='GND':","if re.search(r'(?:^|__)GND$',net):")
 # 同一实体导线分量只放一个标准网标；不在已经连通的局部电路上堆叠重复端口。
 label_append='        labels.extend((point,net) for point in named_points)'
 assert connect_source.count(label_append)==1
 connect_source=connect_source.replace('    labels=[]\n    for net,points in endpoints.items():',
  '    labels=[];named_components=set()\n    for net,points in endpoints.items():')
 connect_source=connect_source.replace(label_append,
  '        for point in named_points:\n'
  '            signature=(net,tuple(sorted(_component_segments(router.segments,point,net))))\n'
  '            if signature in named_components:continue\n'
  '            named_components.add(signature);labels.append((point,net))')
 # A placed power flag must not cover the escape of a later disconnected
 # local branch. Reserving only signal-port escapes could trap GND stubs.
 connect_source=connect_source.replace('    moved_flags=0',
  '    flag_escapes={q for p,n in labels for q in (p,(p[0]-1,p[1]),(p[0]+1,p[1]),(p[0],p[1]-1),(p[0],p[1]+1))}\n    moved_flags=0')
 needle='            if wire_crosses(flagbox,net):continue'
 assert connect_source.count(needle)==1
 connect_source=connect_source.replace(needle,
  "            own_escape={point,(point[0]-1,point[1]),(point[0]+1,point[1]),(point[0],point[1]-1),(point[0],point[1]+1)}\n"
  "            if any(flagbox[0]<=q[0]*5<=flagbox[2] and flagbox[1]<=q[1]*5<=flagbox[3] for q in flag_escapes-own_escape):continue\n"+needle)
 if c.get('physical_board')!='辅助电源板':
  # Reserve a short, traversable escape corridor around each pending label.
  # A one-grid-cell reserve can still be enclosed by neighboring symbols.
  connect_source=connect_source.replace('flag_escapes={q for p,n in labels for q in (p,(p[0]-1,p[1]),(p[0]+1,p[1]),(p[0],p[1]-1),(p[0],p[1]+1))}',
   'flag_escapes={(p[0]+dx,p[1]+dy) for p,n in labels for dx,dy in ((0,0),*((i,0) for i in range(-4,5)),*((0,i) for i in range(-4,5)))}')
  connect_source=connect_source.replace("assert found,('标准网络端口没有空白位置',page,net,point)",
   "assert found,('标准网络端口没有空白位置',page,net,point,'origin_blocked',point in blocked,'neighbours',[(q,q in blocked) for q in ((point[0]-1,point[1]),(point[0]+1,point[1]),(point[0],point[1]-1),(point[0],point[1]+1))])")
 # Precompute the ordered search lattice once, keeping every geometric guard.
 # A merged board needs a wider label search than the former small sheets.
 for axis,key in ((0,'_flag_offsets'),(1,'_port_offsets')):
  scope[key]=sorted(((dx,dy) for dx in range(-128,129) for dy in range(-128,129)),
   key=lambda v,axis=axis:(abs(v[0])+abs(v[1]),abs(v[axis]),v))
  old=f"sorted(((dx,dy) for dx in range(-64,65) for dy in range(-64,65)),key=lambda v:(abs(v[0])+abs(v[1]),abs(v[{axis}]),v))"
  assert old in connect_source
  connect_source=connect_source.replace(old,key)
 # 端口可放在同一真实连通分量的其他短线端，而非困在旧临时标签附近。
 # 优先找投影文字最少被挡的分量端点；网络名/全部引脚/实体功率连接不变。
 port_offsets='        offsets=_port_offsets'
 assert connect_source.count(port_offsets)==1
 connect_source=connect_source.replace(port_offsets,
  '        seeds={point}|{q for a,b in tree for q in (a,b)}\n'
  '        def seed_score(seed):\n'
  '            sx,sy=seed[0]*5,seed[1]*5\n'
  '            rect=(sx+8,sy-9,sx+52+tw,sy+9) if default_side==1 else (sx-52-tw,sy-9,sx-8,sy+9)\n'
  '            return (sum(_overlap(rect,v) for v in texts+bodies+flags),abs(seed[0]-point[0])+abs(seed[1]-point[1]))\n'
  '        offsets=((seed[0]-point[0]+dx,seed[1]-point[1]+dy) for seed in sorted(seeds,key=seed_score) for dx,dy in _port_offsets)')
 if c.get('structured_regions'):
  flag_loop='        offsets=_flag_offsets\n        for dx,dy in offsets:'
  assert connect_source.count(flag_loop)==1
  connect_source=connect_source.replace(flag_loop,
   "        offsets=_flag_offsets\n"
   "        flag_started=time.monotonic()\n"
   "        if i%50==0:print(f'整板电源标记 {page} {i}/{len(labels)} {net}',flush=True)\n"
   "        for dx,dy in offsets:\n"
   "            assert time.monotonic()-flag_started<20,('电源符号避让搜索预算耗尽，须修局部几何',net,point)")
  # Preserve the geometric inputs for a bounded retry without rebuilding all
  # local circuits. This is a cache, not formal acceptance evidence.
  original_ports=connect_source[connect_source.index('    ports=[]'):connect_source.index('    stats,junctions=')]
  diagnostic_ports=original_ports.replace('tw=_textwidth(net,7);found=False','tw=_textwidth(net,7);found=False;rejected=collections.Counter()')
  diagnostic_ports=diagnostic_ports.replace('        for dx,dy in offsets:',
   "        port_started=time.monotonic()\n"
   "        if i%50==0:print(f'整板端口 {page} {i}/{len(labels)} {net}',flush=True)\n"
   "        for dx,dy in offsets:\n"
   "            assert time.monotonic()-port_started<20,('端口避让搜索预算耗尽，须修局部几何而非无限枚举',net,point,dict(rejected))")
  for reason,condition in [('anchor','anchor in blocked'),('bounds','rect[0]<15 or rect[2]>width-15 or rect[1]<100 or rect[3]>height-15'),('obstacle','any(_overlap(rect,v) for v in texts+bodies+flags)'),('escape','reserved & (escape_points-own_escape)'),('wire','wire_crosses(rect)'),('nc','any(rect[0]<=q[0]*5<=rect[2] and rect[1]<=q[1]*5<=rect[3] for q in nc.values())'),('different_net','any(d.get(anchor,net)!=net for d in (router.horizontal,router.vertical,router.vertices))'),('path_rect','any(rect[0]<=q[0]*5<=rect[2] and rect[1]<=q[1]*5<=rect[3] for a,b in zip(path,path[1:]) for q in cells(a,b))')]:
   diagnostic_ports=diagnostic_ports.replace(f'if {condition}:continue',f'if {condition}:rejected[{reason!r}]+=1;continue')
  diagnostic_ports=diagnostic_ports.replace('blocked.difference_update(extra);continue',"blocked.difference_update(extra);rejected['route']+=1;continue")
  diagnostic_ports=diagnostic_ports.replace("'origin_blocked',point in blocked", "'rejected',dict(rejected),'origin_blocked',point in blocked")
  connect_source=connect_source.replace(original_ports,diagnostic_ports)
 exec(connect_source,scope)
 parts=copy.deepcopy(c['parts']);groups={}
 for p in parts:
  p.setdefault('section',p['page']);p.setdefault('board','驱动主板')
  p.setdefault('assembly','候选装配禁止生产')
  if c['board']!='FOC':p['board']='驱动主板'
 for section in dict.fromkeys(p['section'] for p in parts):
  if c.get('e4_stable'):continue
  if c['board']=='FOC' and section not in ('11_regen','12_cap_safety','13_disarm_proof'):continue
  own=[p for p in parts if p['section']==section];by={p['ref']:p for p in own}
  if c['board']!='FOC':
   groups.update(complete_functional_groups(own,section,scope['_rail']))
   continue
  index={p['ref']:i for i,p in enumerate(own)};nets=collections.defaultdict(set)
  for p in own:
   for net in p['pins'].values():
    if not net.startswith('NC_'):nets[net].add(p['ref'])
  adjacency=collections.defaultdict(set)
  for net,refs in nets.items():
   if (c['board']=='FOC' and len(refs)>6) or re.search(r'(?:GND|V3V3|5V|3V3|AUX12|AUX15)$',net):continue
   for ref in refs:adjacency[ref].update(refs-{ref})
  anchors=[p['ref'] for p in own if basename(p['ref']).startswith(('U','PSU')) and len(p['pins'])>=4]
  best={};queue=[(0,ref,ref) for ref in anchors];heapq.heapify(queue)
  while queue:
   distance,anchor,ref=heapq.heappop(queue)
   if ref in best:continue
   best[ref]=(distance,anchor)
   for neighbour in adjacency[ref]:
    if neighbour not in best:heapq.heappush(queue,(distance+1,anchor,neighbour))
  title={'11_regen':'限流回充','12_cap_safety':'超容保护','13_disarm_proof':'关断证明'}.get(section,section)
  def refkey(ref):return re.sub(r'^[A-Z]+_?','',basename(ref))
  for p in own:
   ref=p['ref']
   if ref.startswith('C_U') and ref[2:] in by:anchor=ref[2:]
   elif ref in best:anchor=best[ref][1]
   elif anchors:
    def score(candidate):
     a,b=refkey(ref),refkey(candidate);prefix=0
     for x,y in zip(a,b):
      if x!=y:break
      prefix+=1
     return (prefix if prefix>=5 else 0,-abs(index[ref]-index[candidate]),candidate)
    anchor=max(anchors,key=score)
   else:anchor=min([ref,*adjacency[ref]])
   groups[ref]=title+'·'+anchor
  keys={p['ref']:(p['board'],groups[p['ref']]) for p in own}
  parent={key:key for key in keys.values()};members=collections.defaultdict(set)
  for ref,key in keys.items():members[key].add(ref)
  def root(key):
   while parent[key]!=key:parent[key]=parent[parent[key]];key=parent[key]
   return key
  edges=sorted({(abs(index[a]-index[b]),min(a,b),max(a,b)) for a in adjacency for b in adjacency[a] if a!=b})
  for _,a,b in edges:
   ka,kb=root(keys[a]),root(keys[b])
   if ka==kb or ka[0]!=kb[0] or len(members[ka])+len(members[kb])>20:continue
   if min(index[r] for r in members[ka])>min(index[r] for r in members[kb]):ka,kb=kb,ka
   parent[kb]=ka;members[ka].update(members.pop(kb))
  for p in own:
   refs=members[root(keys[p['ref']])]
   anchors_here=[ref for ref in refs if ref in anchors]
   anchor=max(anchors_here,key=lambda ref:(len(by[ref]['pins']),-index[ref])) if anchors_here else min(refs,key=index.get)
   groups[p['ref']]=title+'·'+anchor
 if c['board']=='配电' and c.get('structured_regions'):
  # This is the USB-PD source connector, not a comparator peripheral. Keep
  # its 28 real contacts opposite its source controller on the same sheet.
  refs={p['ref'] for p in parts}
  assert {'U_PD','J_RK_PD'}<=refs
  groups['J_RK_PD']=groups['U_PD']
  if any(p['mpn']=='PSMN1R1-100CSE' for p in parts):
   # Input, limiter/harness, back-to-back MOS and protection-control chains
   # are semantic circuits, not twelve-ref graph buckets. All stay on ONE SCH.
   for tag in ('AUX','P5','P21'):
    role='04 21V独立泵候选' if tag=='P21' else '01 配电与电源接口'
    stages={
     '01 输入熔断与前级钳位':{f'F_{tag}',f'D_{tag}_REV',f'D_{tag}_TVS',f'R_{tag}_HS_OC'},
     '02 板外并联限阻及独立接线':{f'{prefix}{tag}_HS_LIMIT{n}' for prefix in ('R_','J_R_') for n in (1,2)},
     '03 共源反串及D-S钳位':{f'Q_{tag}_HS1',f'Q_{tag}_HS2',f'D_{tag}_HS_POST_TVS',f'C_{tag}_HS_BOOTSTRAP',f'C_{tag}_HS_DS'},
     '04 LTC输入窗口与关断控制':{f'U_{tag}_HS',f'R_{tag}_HS_SHDN',f'C_{tag}_HS_IN',f'C_{tag}_HS_IN_LOCAL',f'C_{tag}_HS_UV',
      f'R_{tag}_OVT',f'R_{tag}_OVB',f'R_{tag}_PGPU',f'R_{tag}_PGPD',f'R_{tag}_HS_UVT',f'R_{tag}_HS_UVB',f'R_{tag}_UVT',f'R_{tag}_UVB'},
     '05 门极充电与PNP快沉':{f'D_{tag}_HS_GATE_CHARGE',*(f'{prefix}{tag}_HS_GATE_OFF{n}' for prefix in ('Q_','R_') for n in (1,2)),f'R_{tag}_HS_SLEW'},
     '06 门极偏置与缓升':{*(f'R_{tag}_HS_GS{n}' for n in range(1,7)),f'C_{tag}_HS_CG',f'C_{tag}_HS_CG2',f'C_{tag}_HS_MILLER'},
     '07 VOUT隔离RC与低能钳位':{f'R_{tag}_HS_VOUT_PIN',f'R_{tag}_HS_VOUT_CLAMP',f'D_{tag}_HS_VOUT_PIN',*(f'C_{tag}_HS_VOUT_PIN{n}' for n in range(1,5))},
     '08 SENSE隔离RC与低能钳位':{f'R_{tag}_HS_SENSE_PIN',f'R_{tag}_HS_SENSE_CLAMP',f'D_{tag}_HS_SENSE_PIN',*(f'C_{tag}_HS_SENSE_PIN{n}' for n in range(1,5))},
     '09 负压独立返回与均流':{f'D_{tag}_HS_NEG',f'D_{tag}_HS_NEG2',f'D_{tag}_HS_NEG3',*(f'R_{tag}_HS_NEG_BAL{n}' for n in range(1,4)),f'R_{tag}_HS_BLEED'}}
    assigned=set()
    assert stages['02 板外并联限阻及独立接线']<=refs,'缺真实板外限阻/PCB接线合同；不沿用旧13端子输入'
    for stage,members in stages.items():
     actual=members&refs;assert actual and not assigned&actual,(tag,stage,'分区为空或重复')
     assigned.update(actual)
     for ref in actual:groups[ref]=role+'·'+tag+'保护链·'+stage
     if f'U_{tag}_S2_HS' in refs:
      for stage,members in stages.items():
       if stage.startswith(('01','02')):continue
       second={r.replace('_'+tag+'_HS','_'+tag+'_S2_HS',1) if '_'+tag+'_HS' in r else r.replace('_'+tag+'_','_'+tag+'_S2_',1) for r in members}
       actual=second&refs;assert actual,(tag,stage,'第二保护级缺少功能区')
       for ref in actual:groups[ref]=role+'·'+tag+'_S2保护链·'+stage
      groups[f'R_{tag}_S2_HS_OC']=role+'·'+tag+'_S2保护链·00 第二级输入分流'
      bulk=f'C_{tag}_HS_OUT_BULK'
      if bulk in refs:groups[bulk]=role+'·'+tag+'保护链·03 共源反串及D-S钳位'
   for ref in ('J_PACK','F_LEFT','J_LEFT','F_RIGHT','J_RIGHT'):
    assert ref in refs;groups[ref]='01 配电与电源接口·整包输入与左右牵引支路'
 if c['board']=='BMS板':
  if c.get('structured_regions'):
   for cell in range(1,11):
    refs={f'F_BAL{cell}',f'T_BAL{cell}',*(f'C_BAL_CELL{cell}_{n}' for n in range(1,7)),
     *(f'{prefix}_BAL_{side}{cell}' for side in ('P','S') for prefix in ('Q','RG','RGS','RS','R_SNUB','C_SNUB'))}
    assert refs<={basename(p['ref']) for p in parts}
    for p in parts:
     if basename(p['ref']) in refs:groups[p['ref']]=f'主动均衡功率·均衡通道{cell:02d}—抽头、变压器与双向开关'
  # Each 49-pin balancing controller owns its local bias/OVP network. Do not
  # collapse both controllers into one twelve-component graph bucket.
  for ref,name in list(groups.items()):
   if name in ('主动均衡控制·U_BAL_LOW','主动均衡控制·U_BAL_TOP'):groups[ref]='主动均衡控制·双芯片通信接续'
  for side in ('LOW','TOP'):
   local_refs={f'U_BAL_{side}',f'C_BAL_{side}_REG',f'R_BAL_{side}_PON',f'R_BAL_{side}_SON',f'R_BAL_{side}_OVP',
    f'Q_BAL_{side}_OVP_CASCODE',f'D_BAL_BOOST_{side}',f'R_BAL_BOOST_{side}',f'C_BAL_BOOST_{side}'}
   existing=local_refs&{basename(p['ref']) for p in parts}
   assert f'U_BAL_{side}' in existing
   for p in parts:
    if basename(p['ref']) in existing:groups[p['ref']]=f'主动均衡控制·U_BAL_{side}'
 if c['board']=='外充板':
  bridge_refs={'Q_CHG_H1','Q_CHG_L1','Q_CHG_H2','Q_CHG_L2','L_CHARGER','R_CHG_L_SERIES_A','R_CHG_L_SERIES_B','C_CHG_BST1','C_CHG_BST2',
   *('RG_Q_CHG_'+s for s in ('H1','L1','H2','L2')),*('RGS_Q_CHG_'+s for s in ('H1','L1','H2','L2'))}
  assert bridge_refs<={basename(p['ref']) for p in parts}
  for p in parts:
   if basename(p['ref']) in bridge_refs:groups[p['ref']]='外充四开关功率级·输入桥—电感—输出桥'
 if c['board']=='FOC' and not c.get('e4_stable') and c.get('structured_regions') and any(p['ref']=='U_SC_LOGIC3' for p in parts):
  # Keep the safety latch, converter enable and port/READY decisions readable
  # as three linked local circuits on the SAME physical sheet. They are not
  # three schematic pages, nor arbitrary equal-size component buckets.
  safety_chains={
   '超容保护·锁存与健康资格':{'U_SC_LATCH','C_U_SC_LATCH','U_SC_LOGIC1','C_U_SC_LOGIC1','R_SC_ARM_REQUEST_PD'},
   '超容保护·双向变换许可':{'U_SC_LOGIC2','C_U_SC_LOGIC2','R_SC_RUN_EN1','R_SC_RUN_EN2','R_SC_RUN_UVLO','R_SC_CONVERT_REQUEST_PD'},
   '超容保护·端口与READY许可':{'U_SC_LOGIC3','C_U_SC_LOGIC3','R_SC_PORT_HV_CMD','R_SC_PORT_LV_CMD','R_SC_READY_SEND',
    'R_SC_PORT_LV_REQUEST_PD','R_SC_PORT_HV_REQUEST_PD','R_SC_READY_REQUEST_PD'}}
  refs={p['ref'] for p in parts}
  if 'U_SC_UVLO_BUFFER' in refs:
   safety_chains['超容保护·双向变换许可'].update({'U_SC_RUN_AND','C_U_SC_RUN_AND','U_SC_UVLO_BUFFER','C_U_SC_UVLO_BUFFER'})
   safety_chains['超容保护·端口与READY许可'].update({'U_SC_READY_B','C_U_SC_READY_B'})
  assert set.union(*safety_chains.values())<=refs,'储能许可链变更，须按新拓扑重新分组'
  for title,chain in safety_chains.items():
   for ref in chain:groups[ref]=title
  if 'C_U_SC_LOGIC4' in refs:
   assert 'U_SC_LOGIC4' in refs
   controller=next(p for p in parts if p['ref']=='U_SC_LOGIC4')
   groups['C_U_SC_LOGIC4']=groups.get('U_SC_LOGIC4',original_function(controller))
  for i in range(1,6):
   ref=f'U_SPF_WINDOW_PAIR{i}'
   if ref in refs:
    assert 'C_'+ref in refs
    groups[ref]=groups['C_'+ref]='关断证明·'+ref
  threshold_refs={'R_SPF_GOV_T','R_SPF_GOV_B','R_SPF_GUV_T','R_SPF_GUV_B'}
  assert threshold_refs<=refs
  for ref in threshold_refs:groups[ref]='关断证明·关栅阈值基准'
  for ref in ('U_SPF_PRE_HV','U_SPF_PRE_LV'):
   assert ref in refs and 'C_'+ref in refs
   groups[ref]=groups['C_'+ref]='关断证明·'+ref
  # The two four-channel reverse detectors are independent cell-bank
  # comparisons, not peripherals of the cold-start overcurrent comparator.
  # Keep their input escapes open and their bypass capacitors local, on the
  # same physical sheet; never alter the electrical pin or net contracts.
  reverse_reference={'R_SC_REVERSE_P','R_SC_REVERSE_N','R_SC_REVERSE_G'}
  assert reverse_reference<=refs
  for i in (1,2):
   ref=f'U_SC_REVERSE{i}'
   assert ref in refs and 'C_'+ref in refs
   groups[ref]=groups['C_'+ref]=f'14_cold_diagnostics·反接检测{i}'
  for ref in reverse_reference:groups[ref]='14_cold_diagnostics·反接检测1'
  # Ramp/compensation networks belong to their control loop, not the power
  # semiconductor row. Both phases remain on the same physical schematic.
  for phase in ('1','2'):
   compensation={f'R_SC_RAMP{phase}',f'C_SC_RAMP{phase}',f'R_SC_COMP{phase}',
    f'C_SC_COMP{phase}',f'C_SC_COMP_HF{phase}'}
   assert compensation<=refs,'储能相控制补偿合同改变，须重新组织'
   for ref in compensation:groups[ref]=f'电流控制与硬件禁能·相{phase}斜坡补偿'
  storage_power_groups={
   '高压端·熔断停流分流、隔离及预充':{'J_SC_BUS','F_SC_HV','R_SC_HV_OFF_SHUNT','Q_SC_HVA','Q_SC_HVB','R_SC_HV_GS','R_SC_HV_GATE_LOCK','R_SC_HV_PRE','U_SC_HV_PRE'},
   '低压端·熔断、隔离预充及总量分流':{'F_SC_LV','Q_SC_LVA','Q_SC_LVB','R_SC_CAP_CURRENT','R_SC_LV_GS','R_SC_LV_GATE_LOCK','R_SC_LV_PRE','U_SC_LV_PRE'},
   '20节超容串联功率':{*(f'C_SC_CELL{n}' for n in range(1,21))}}
  assert set.union(*storage_power_groups.values())<=refs,'储能主功率端口或电容串联合同改变'
  for title,chain in storage_power_groups.items():
   for ref in chain:groups[ref]=title
 if c['board']=='FOC' and not c.get('e4_stable') and c.get('structured_regions') and any(p['ref']=='U_MAIN_LOGIC1' for p in parts):
  chain={'R_RG_FAULT_PU','U_RG_CTRL_BUF','J_REGEN_ALLOW','R_RG_ALLOW_PD','R_RG_REQ_PD',
   'U_MAIN_LOGIC1','C_U_MAIN_LOGIC1','U_RG_LATCH','C_U_RG_LATCH','U_MAIN_LOGIC2','C_U_MAIN_LOGIC2'}
  assert chain<={p['ref'] for p in parts}
  for ref in chain:groups[ref]='限流回充·许可锁存与健康'
 if c['board']=='FOC' and c.get('physical_board')=='驱动主板' and not c.get('e4_stable'):
  input_chain={
   '输入功率链·01 端子、主熔断与手动断路':{'J_BAT_1','J_BAT_2','F1','K1'},
   '输入功率链·04 主接触器及并联预充':{'K2','F_PRE','R_PRE'},
   '输入功率链·05 主分流、母线电容与钳位':{'R_BAT','D_TVS','R_BLEED',*(f'C_BUS{i}' for i in range(1,9))},
   '输入功率链·06 桥输入分流':{'R_BRIDGE'}}
  for n in (1,2):input_chain[f'输入功率链·0{n+1} 反向阻断第{n}级']={
   f'U_BAT_BLOCK{n}',f'Q_BAT_BLOCK{n}',f'C_BAT_BLOCK_VCAP{n}',f'C_BAT_BLOCK_IN{n}',f'C_BAT_BLOCK_OUT{n}'}
  refs={p['ref'] for p in parts}
  assert set.union(*input_chain.values())<=refs,'主输入拓扑变更，须按新源重新组织'
  for title,chain in input_chain.items():
   for ref in chain:groups[ref]=title
  regen_power={'F_RG_IN','C_RG_IN','Q_RG_H','Q_RG_L','R_RG_GH','R_RG_GL','R_RG_GSH','R_RG_GSL',
   'L_RG','R_RG_PHASE','C_RG_OUT','Q_RG_ISOA','Q_RG_ISOB','R_RG_ISO_GS','D_RG_OUT','R_RG_OUTPUT','F_RG_OUT'}
  assert regen_power<=refs,'回充实际功率链变化，须按新源重排'
  for ref in regen_power:groups[ref]='限流回充·主功率与输出隔离'
  efuse={'U_EFUSE1','U_OVP5_CLAMP','D_EFUSE5_OV_ISO','R_EFUSE5_REF_BIAS','R_EFUSE5_OV_TOP',
   'R_EFUSE5_OV_BOT','R_EFUSE5_ILIM','C_EFUSE5_IN','C_EFUSE5_DVDT','C_EFUSE5_OUT'}
  assert efuse<=refs
  for ref in efuse:groups[ref]='主5V保护·过压、限流及软启动'
  for ref,title in [('J_MOD15_IN','主板15V模块'),('J_MAIN12_IN','主板主12V模块'),('J_MOD5_IN','主板5V模块')]:
   groups[ref]=title
  for ref in ('J_FAN','FAN1'):groups[ref]='主12V负载·风扇接口'
  for ref in ('F_BACKUP_BAT','J_BACKUP_BAT_IN','D_BACKUP_BAT','D_BACKUP_BUS'):groups[ref]='备用12V输入·双路反阻合流'
 scope['_function']=lambda p:groups.get(p['ref'],original_function(p) if c['board']=='FOC' else p['section'])
 if c['board']=='FOC' and c.get('physical_board')=='中央稳压模块' and not c.get('e4_stable'):
  def structured_storage_bands(board,blocks):
   lanes=collections.OrderedDict((k,[]) for k in (
    '主功率：端口隔离、预充与双向变换','偏置供电与电源监视','电流闭环、PWM与硬件禁能',
    '单节AFE、均衡与温度','20节独立越限检测','保护判决、锁存与预充资格',
    '实际桥臂及端口关栅证明','停流、EN与预充状态证明','证明域自检、基准与默认撤销',
    '冷启动独立诊断','控制接口、总量采样与通信'))
   for b in blocks:
    t=b['metadata']['title'];role=None
    if t in ('高压端·熔断停流分流、隔离及预充','低压端·熔断、隔离预充及总量分流','20节超容串联功率','端口隔离栅极驱动','双向功率相1','双向功率相2'):role=list(lanes)[0]
    elif t in ('端口驱动偏置窗口','端口浮动偏置','独立10V偏置','独立5V偏置','AFE偏置电源') or t in ('超容保护·U_SC_NEG','超容保护·U_SC_NEG_SENSE','超容保护·U_SC_REF25','超容保护·U_SC_5_MON'):role=list(lanes)[1]
    elif t.startswith(('电流控制与硬件禁能','限流回充')):role=list(lanes)[2]
    elif t.startswith(('单节AFE','单节检测与均衡','电容温度')):role=list(lanes)[3]
    elif t.startswith(('超容保护·U_SC_CELL_DIFF','超容保护·U_SC_CELL_PAIR')):role=list(lanes)[4]
    elif t.startswith('超容保护') or t in ('关断证明·U_SC_BMS_RUN_AND','关断证明·U_SC_PRE_HV_HARD'):role=list(lanes)[5]
    elif t.startswith(('关断证明·U_SPF_Q_','关断证明·U_SPF_PORT','关断证明·U_SPF_WINDOW_PAIR')):role=list(lanes)[6]
    elif t.startswith(('关断证明·U_SPF_I_','关断证明·U_SPF_EN','关断证明·U_SPF_PRE_','关断证明·U_SPF_UVLO')):role=list(lanes)[7]
    elif t.startswith('关断证明'):role=list(lanes)[8]
    elif t.startswith('14_cold_diagnostics'):role=list(lanes)[9]
    elif t.startswith(('储能控制接口','储能通信')):role=list(lanes)[10]
    assert role is not None,('储能新增电路须明确功能位置',t)
    b['metadata']['circuit_role']=role;lanes[role].append(b)
   bands=[]
   for role,own in lanes.items():
    columns=4 if role==list(lanes)[4] else 5
    for i in range(0,len(own),columns):
     band=own[i:i+columns]
     if band:band[0]['metadata']['title']=role+' / '+band[0]['metadata']['title'];bands.append(band)
   return bands
  scope['_board_bands']=structured_storage_bands
 if c['board']!='FOC':
  role_order={
   'BMS板':['整包功率','门驱动候选','采样与AFE','主动均衡功率','主动均衡控制','控制电源',
    '板载主控','默认关断候选','独立停机证明供电','插电硬联锁','外充控制接口','对外许可','隔离通信','跨板接口'],
   '外充板':['外充输入保护','外充四开关功率级','外充输出隔离与残能','外充独立电源与隔离','外充独立停流检测','跨板接口'],
   '配电':['01 配电与电源接口','01 RK独立降压','01 RK自主USB PD源','01 RADIO独立降压',
    '01 P5独立降压','03 双泵功率与检测','04 21V独立泵候选','输入保护与局部电源','02 弱电降压与控制','02 MCU CAN与硬件许可']}[c['board']]
  def electrical_role_bands(board,blocks):
   groups_by_role=collections.OrderedDict((role,[]) for role in role_order)
   for block in blocks:
    role=block['metadata']['title'].split('·',1)[0]
    assert role in groups_by_role,('新功能需明确电路位置，禁止落入剩余元件拼排',role)
    block['metadata']['circuit_role']=role
    groups_by_role[role].append(block)
   if c['board']=='外充板':groups_by_role['外充四开关功率级'].sort(key=lambda b:'输入桥—电感—输出桥' not in b['metadata']['title'])
   return [own[i:i+3] for own in groups_by_role.values() for i in range(0,len(own),3)]
  scope['_board_bands']=electrical_role_bands
 # No unexplained leftover grid: every functional block has a named circuit
 # role. Phase proof cells sit in the same lane as the phase they supervise.
 if c['board']=='FOC' and c.get('physical_board')=='驱动主板' and not c.get('e4_stable'):
  def structured_main_bands(board,blocks):
   lanes=collections.OrderedDict((k,[]) for k in (
    '输入、隔离与预充','U相功率与关断采样','V相功率与关断采样','W相功率与关断采样',
    '控制、门驱与硬件禁能','限流回充功率支路','回充及主泄放关栅证明','主泄放保护支路','独立备用泄放',
    '电流、电压与温度采样','本地辅助供电','外充关断资格与RUN监督','通信与霍尔'))
   for b in blocks:
    t=b['metadata']['title'];lane=None
    if t.startswith(('输入功率链·','母线与辅助电源接口','电池两级反向阻断','预充电压确认','接触器线圈驱动')):lane='输入、隔离与预充'
    for ph,nums,cur in [('U',(1,2),'A'),('V',(3,4),'B'),('W',(5,6),'C')]:
     if t==ph+'相功率桥' or t==cur+'相电流快速保护' or any(t=='关断证明·U_PF_PAIR'+str(n) for n in nums):lane=ph+'相功率与关断采样'
    if t.startswith(('三相栅极驱动','核心板与PWM接口','硬件联锁与驱动许可','复位及独立看门狗')):lane='控制、门驱与硬件禁能'
    elif t.startswith('限流回充'):lane='限流回充功率支路'
    elif t.startswith('关断证明·U_PF_Q_RG') or t in ('关断证明·U_PF_GATE_PAIR1','关断证明·U_PF_GATE_PAIR2'):lane='回充及主泄放关栅证明'
    elif t.startswith(('主12V独立监督','主泄放','主电阻接线')) or t=='关断证明·U_PF_Q13':lane='主泄放保护支路'
    elif t.startswith(('备用泄放','备用电阻接线')) or t=='关断证明·U_PF_Q_BACKUP':lane='独立备用泄放'
    elif t.startswith(('电池电流采样','母线电压采样','模拟输入与温度','过流窗口基准')):lane='电流、电压与温度采样'
    elif t.startswith(('主板15V模块','主板主12V模块','主板5V模块','主板备用12V模块','主板线圈12V模块','主5V保护·','主12V负载·','备用12V输入·')):lane='本地辅助供电'
    elif t.startswith('关断证明') and lane is None:lane='外充关断资格与RUN监督'
    elif t.startswith(('CAN通信接口','霍尔输入接口')):lane='通信与霍尔'
    assert lane is not None,('功能区没有明确电路角色，禁止按剩余数量拼排',t)
    b['metadata']['circuit_role']=lane;lanes[lane].append(b)
   bands=[]
   for lane,own in lanes.items():
    for start in range(0,len(own),4):
     band=own[start:start+4]
     if band:
      band[0]['metadata']['title']=lane+' / '+band[0]['metadata']['title']
      bands.append(band)
   return bands
  scope['_board_bands']=structured_main_bands
 if c.get('e4_stable'):
  adapter=module('集成E4功能区');e4_adapter_path=Path(adapter.__file__);e4_adapter_sha=sha(e4_adapter_path)
  adapter.install(c,scope,complete_circuit_positions)
 # Retain the existing physical-board merger. Its four-board assertion was
 # specific to the original FOC project; BMS/charger/power each supply one board.
 merge_source=inspect.getsource(scope['_merge_boards'])
 if c['board']!='FOC' or c.get('physical_board')=='中央稳压模块':
  merge_source=merge_source.replace('x+=bw+30;band_height=max(band_height,bh)','x+=bw+110;band_height=max(band_height,bh)')
  merge_source=merge_source.replace('y+=band_height+30','y+=band_height+110')
 merge_source=merge_source.replace("assert len(result)==4,'必须一板一图及独立系统接线图，共4页'",
  "assert len(result)==len({b['metadata']['board'] for b in blocks}), '实体板与图页数量不符'")
 exec(merge_source,scope)
 original_merge=scope['_merge_boards']
 def physical_pages(blocks,inventory,api_dict):
  if not c.get('structured_regions') or c.get('physical_board')=='辅助电源板':merged,stats=original_merge(blocks,inventory,api_dict)
  else:merged,stats=merge_structured_regions(c,blocks,inventory,api_dict,scope)
  if c['board']!='FOC':
   assert len(merged)==1, '一块实体板必须一张完整原理图'
   doc=merged[0];old=doc['head']['c_para']['name'];name=c['board']+'-01-整板原理图'
   doc['head']['c_para']['name']=name;doc['metadata']['board']=c['board']
   doc['metadata']['layout'].update(板=c['board'],页名=name)
   doc['shape']=[s.replace('驱动主板 · 整板原理图',name) if s.startswith('T~') else s for s in doc['shape']]
   for item in inventory:
    assert item['页名']==old
    item.update(板=c['board'],页名=name)
  return merged,stats
 scope['_merge_boards']=physical_pages
 library={p['mpn']:raw[p['mpn'].casefold()]['symbol'] for p in parts
          if p['mpn'].casefold() in raw and not raw[p['mpn'].casefold()]['multipart'] and set(raw[p['mpn'].casefold()]['pins'])==set(p['pins'])}
 if c['board']!='FOC' or c.get('e4_stable'):
  # This inherited renderer used fixed A3 tiles and split every 22 components
  # in source order. Those were construction blocks, never schematic pages.
  # Adapt its geometric bounds without editing the electrical author's engine.
  caption_source=inspect.getsource(scope['_caption_plan']).replace('>1185','>HEIGHT-65')
  exec(caption_source,scope)
  generate_source=inspect.getsource(scope['generate'])
  split_rule='chunks=[group] if len(group)<=22 else [group[i:i+18] for i in range(0,len(group),18)]'
  assert generate_source.count(split_rule)==1
  generate_source=generate_source.replace(split_rule,'chunks=[group]')
  old_positions='positions=_positions(group,prep,title); blocked=set();'
  assert generate_source.count(old_positions)==1
  generate_source=generate_source.replace(old_positions,'blocked=set();')
  generate_source=generate_source.replace("        doc={'head':", "        positions=_positions(group,prep,title)\n        doc={'head':",1)
  generate_source=generate_source.replace('block(40,20,1710,85); block(40,1190,1740,1240)',
   'block(40,20,WIDTH-60,85); block(40,HEIGHT-60,WIDTH-60,HEIGHT-10)')
  generate_source=generate_source.replace('cy+y2<1185','cy+y2<HEIGHT-65').replace('>1185','>HEIGHT-65')
  generate_source=generate_source.replace(',60,1220,size=10)',',60,HEIGHT-30,size=10)')
  exec(generate_source,scope);engine['generate']=scope['generate']
 elif c.get('physical_board')=='中央稳压模块' and not c.get('e4_stable'):
  # This complete twenty-cell chain is explicitly placed and geometrically
  # checked. A generic 22-part cap would split its 20 terminals into an
  # arbitrary 18/2 grid, destroying the visible series relationship.
  generate_source=inspect.getsource(scope['generate'])
  split_rule='chunks=[group] if len(group)<=22 else [group[i:i+18] for i in range(0,len(group),18)]'
  assert generate_source.count(split_rule)==1
  generate_source=generate_source.replace(split_rule,
   "chunks=[group] if len(group)<=22 or (title=='20节超容串联功率' and len(group)==20) else [group[i:i+18] for i in range(0,len(group),18)]")
  exec(generate_source,scope);engine['generate']=scope['generate']
 sheets,nets,nc,inventory,_,wiring=engine['generate'](parts,c['data'].get('SECTIONS',{}),bindings,library,vars(api))
 expected,expected_nc,aliases=physical_connection_contract(c['parts'],bindings)
 assert nets==expected and nc==expected_nc,'功能图面必须保持冻结逐脚连接及NC'
 assert sha(engine_path)==engine_sha,'公共图面生成期间依赖引擎改变'
 if c.get('e4_stable'):
  assert sha(e4_adapter_path)==e4_adapter_sha,'E4图面生成期间功能区适配器改变'
  wiring.update(E4功能区适配器=str(e4_adapter_path.relative_to(ROOT)),E4功能区适配器SHA256=e4_adapter_sha)
 wiring.update(一块板一张原理图=True,按真实功能分页=False,连接表未改=True,
  源逻辑端子到物理铜别名=aliases,源逻辑端子数=sum(len(p['pins']) for p in c['parts']),
  按板页数=dict(collections.Counter(s['metadata']['board'] for s in sheets)),
  工具SHA256=c['tool_sha'],依赖引擎SHA256=engine_sha)
 validate_single_physical_sheet(c,sheets,inventory)
 return sheets,nets,nc,inventory,wiring

def validate_single_physical_sheet(c,sheets,inventory):
 """页数、实体归属及元件完整性是硬约束，不代表图面可读性通过。"""
 physical=c.get('physical_board',c['board'])
 assert physical!='系统接线', '系统接线图不能代替实体板原理图'
 assert len(sheets)==1, ('一块板必须一原理图一页',physical,len(sheets))
 sheet=sheets[0];page=sheet['head']['c_para']['name']
 assert sheet['metadata']['board']==physical, ('原理图实体归属错误',physical)
 expected=[p['ref'] for p in c['parts']];actual=[p['位号'] for p in inventory]
 assert len(expected)==len(set(expected)), '输入存在重复位号'
 assert len(actual)==len(set(actual)) and set(actual)==set(expected), '单页元件遗漏、重复或混入其他板'
 assert all(p['页名']==page and p['板']==physical for p in inventory), '元件仍分散到别页或其他实体板'
 if c.get('native_scope'):
  selected={p['ref'] for p in c['parts']}
  assert all(p['board']==physical and p.get('installation')=='板上'
   and p.get('pcb_footprint_required') is True and p.get('onboard') is True for p in c['parts']), '仅板上原生范围混入板外器件'
  assert len(selected)==c['native_scope']['board_on_ref_count']
  assert scope_digest(selected)==c['native_scope']['board_on_refs_sha256']
 return {'实体板':physical,'原理图页':page,'页数':1,'完整位号数':len(actual),'视觉验收':'NOT_RUN'}

def select_central_board_on_scope(c):
 """Keep the full validated source/BOM, but expose only real onboard parts to EasyEDA."""
 physical='中央稳压模块';parts=c['parts']
 assert parts and all(p.get('board')==physical for p in parts), '中央单板过滤前必须是该实体板完整源清单'
 onboard=[p for p in parts if p.get('installation')=='板上' and p.get('pcb_footprint_required') is True]
 offboard=[p for p in parts if p.get('installation')=='板外' and p.get('pcb_footprint_required') is False]
 unclassified=[p['ref'] for p in parts if p not in onboard and p not in offboard]
 assert not unclassified and len(parts)==len(onboard)+len(offboard), ('中央源板内/板外身份不完整',unclassified)
 assert onboard and offboard and all(p.get('onboard') is True for p in onboard) and all(p.get('onboard') is False for p in offboard)
 refs={p['ref'] for p in onboard};excluded={p['ref'] for p in offboard}
 connections=sorted((p['ref'],n,net) for p in onboard for n,net in p['pins'].items() if not net.startswith('NC_'))
 nc=sorted((p['ref'],n) for p in onboard for n,net in p['pins'].items() if net.startswith('NC_'))
 offboard_pins=sum(len(p['pins']) for p in offboard)
 c['native_scope']={
  'scope':'CENTRAL_BOARD_ON_ONLY',
  'predicate':"board=='中央稳压模块' and installation=='板上' and pcb_footprint_required is True",
  'full_source_part_count':len(c['data']['PARTS']),
  'source_board_part_count':len(parts),
  'board_on_ref_count':len(onboard),
  'board_on_pin_count':sum(len(p['pins']) for p in onboard),
  'board_on_connected_pin_count':len(connections),
  'board_on_nc_count':len(nc),
  'board_on_net_count':len({net for _,_,net in connections}),
  'board_on_refs_sha256':scope_digest(refs),
  'board_on_connections_sha256':scope_digest(connections),
  'board_on_nc_sha256':scope_digest(nc),
  'excluded_offboard_ref_count':len(offboard),
  'excluded_offboard_pin_count':offboard_pins,
  'excluded_offboard_refs_sha256':scope_digest(excluded),
 }
 c['parts']=onboard
 return c['native_scope']

def structured_region_rows(physical,roles,blocks,default_columns=3):
 """关键功率/保护链按实际电路关系排，不用元件数量决定换行。"""
 title=lambda b:b['metadata']['title'].split(' / ',1)[-1]
 if physical=='配电' and len(roles)==1 and re.fullmatch(r'(?:AUX|P5|P21)输入保护',roles[0]):
  chains=collections.OrderedDict()
  for b in blocks:chains.setdefault(title(b).rsplit('·',1)[0],[]).append(b)
  rows=[]
  for key,own in chains.items():
   chain=sorted(own,key=lambda b:int(title(b).rsplit('·',1)[1].split(' ',1)[0]))
   expected=['00',*[f'{n:02d}' for n in range(3,10)]] if '_S2保护链' in key else [f'{n:02d}' for n in range(1,10)]
   assert [title(b).rsplit('·',1)[1][:2] for b in chain]==expected,'真实串联保护级功能块缺失或重复'
   rows.extend([chain[n:n+3] for n in range(0,len(chain),3)])
  # The first row is the physical energy path. Gate control sits directly
  # below its MOS pair; sense/clamp circuits follow in the third row.
  return rows
 if physical=='配电' and len(roles)==1 and roles[0] in ('01 配电与电源接口','04 21V独立泵候选'):
  by={title(b):b for b in blocks};rows=[];used=set()
  pack='01 配电与电源接口·整包输入与左右牵引支路'
  if pack in by:rows.append([by[pack]]);used.add(pack)
  for tag in ('AUX','P5','P21'):
   chain=sorted((t for t in by if t.startswith(roles[0]+'·'+tag+'保护链·')),key=lambda t:int(t.rsplit('·',1)[1].split(' ',1)[0]))
   if not chain:continue
   assert len(chain)==9 and [t.rsplit('·',1)[1][:2] for t in chain]==[f'{n:02d}' for n in range(1,10)],'实际保护链九功能块缺失，禁止按数量补格'
   rows.extend([[by[t] for t in chain[n:n+3]] for n in (0,3,6)]);used.update(chain)
  if used:
   rest=[b for b in blocks if title(b) not in used]
   return rows+signal_path_rows(rest)
 if physical=='中央稳压模块' and roles==['主功率：端口隔离、预充与双向变换']:
  by={title(b):b for b in blocks}
  ports=['高压端·熔断停流分流、隔离及预充','低压端·熔断、隔离预充及总量分流','20节超容串联功率']
  assert set(by)==set(ports)|{'端口隔离栅极驱动','双向功率相1','双向功率相2'},'储能端口及双相功率关系变化'
  return [[by[t] for t in ports],[by['双向功率相1'],by['双向功率相2']],[by['端口隔离栅极驱动']]]
 if physical=='中央稳压模块' and roles==['电流闭环、PWM与硬件禁能']:
  by={title(b):b for b in blocks}
  paths=[['电流控制与硬件禁能·1','电流控制与硬件禁能·相1斜坡补偿'],
   ['电流控制与硬件禁能·2','电流控制与硬件禁能·相2斜坡补偿','限流回充·R_SC_DT']]
  assert set(by)=={t for path in paths for t in path},'双相控制、斜坡及死区关系改变，须重排'
  return [[by[t] for t in path] for path in paths]
 if physical=='中央稳压模块' and roles==['单节AFE、均衡与温度']:
  by={title(b):b for b in blocks}
  paths=[['单节AFE与SPI','电容温度检测'],['单节检测与均衡1至4','单节检测与均衡5至8']]
  assert set(by)=={t for path in paths for t in path},'AFE、温度及两组逐节采样关系改变，须重排'
  return [[by[t] for t in path] for path in paths]
 if physical=='驱动主板' and roles==['输入、隔离与预充']:
  chain=sorted((b for b in blocks if title(b).startswith('输入功率链·')),key=title)
  assert [re.search(r'·(\d+)',title(b)).group(1) for b in chain]==['01','02','03','04','05','06'], '输入功率链阶段不完整'
  support={title(b):b for b in blocks if b not in chain}
  assert set(support)=={'预充电压确认','接触器线圈驱动'}, ('预充控制关系变更',set(support))
  return [chain,[support['预充电压确认'],support['接触器线圈驱动']]]
 if physical=='驱动主板' and len(roles)==1 and re.fullmatch(r'[UVW]相功率与关断采样',roles[0]):
  ph=roles[0][0];index='UVW'.index(ph);by={title(b):b for b in blocks}
  wanted=[ph+'相功率桥','ABC'[index]+'相电流快速保护',f'关断证明·U_PF_PAIR{index*2+1}',f'关断证明·U_PF_PAIR{index*2+2}']
  assert set(by)==set(wanted), ('相桥、采样或证明关系变更',ph,set(by))
  return [[by[wanted[0]]],[by[wanted[1]]],[by[wanted[2]],by[wanted[3]]]]
 if physical=='驱动主板' and roles==['本地辅助供电']:
  by={title(b):b for b in blocks}
  paths=[['主板15V模块','主板主12V模块','主12V负载·风扇接口'],
   ['主板5V模块','主5V保护·过压、限流及软启动'],
   ['备用12V输入·双路反阻合流','主板备用12V模块','主板线圈12V模块']]
  assert set(by)=={t for path in paths for t in path},('辅助电源路径变化',set(by))
  return [[by[t] for t in path] for path in paths]
 if physical=='驱动主板' and roles==['限流回充功率支路','回充及主泄放关栅证明']:
  by={title(b):b for b in blocks};power='限流回充·主功率与输出隔离'
  control=sorted(t for t in by if t.startswith('限流回充·U_RG_CTRL'))
  assert control and power in by,'回充主功率与闭环控制必须独立可辨'
  paths=[[power],['限流回充·U_RG_10V','限流回充·U_RG_ISO_DRV'],control,
   ['限流回充·U_RG_SENSE','限流回充·U_RG_LATCH'],
   ['限流回充·U_RG_DAC','限流回充·许可锁存与健康'],
   ['关断证明·U_PF_GATE_PAIR1','关断证明·U_PF_GATE_PAIR2']]
  assert len(by)==sum(map(len,paths)) and set(by)=={t for path in paths for t in path},('回充控制/许可/证明关系变更',set(by))
  return [[by[t] for t in path] for path in paths]
 if physical=='BMS板' and roles==['主动均衡功率']:
  # Two actual five-cell controller banks, not a two-column BOM grid.
  channels={int(re.search(r'均衡通道(\d+)',title(b)).group(1)):b for b in blocks if re.search(r'均衡通道(\d+)',title(b))}
  assert set(channels)==set(range(1,11)),'均衡实际通道归属改变，须重排'
  support=[b for b in blocks if b not in channels.values()]
  assert all(title(b)=='主动均衡功率·独立支路-J_BAL' for b in support) and len(support)<=1,'均衡抽头接口以外的支路须明确分区'
  return ([support] if support else [])+[[channels[n] for n in range(1,6)],[channels[n] for n in range(6,11)]]
 return signal_path_rows(blocks)

def merge_structured_regions(c,blocks,inventory,api,engine):
 """按明确电气域组织二维区域；保留局部电路、全部引脚和真实功率连线。"""
 plans={
  '驱动主板':[
   [['输入、隔离与预充']],
   [['U相功率与关断采样'],['V相功率与关断采样'],['W相功率与关断采样']],
   [['控制、门驱与硬件禁能'],['限流回充功率支路','回充及主泄放关栅证明'],['主泄放保护支路','独立备用泄放']],
   [['电流、电压与温度采样'],['本地辅助供电'],['外充关断资格与RUN监督','通信与霍尔']]],
  '中央稳压模块':[
   [['主功率：端口隔离、预充与双向变换'],['电流闭环、PWM与硬件禁能'],['控制接口、总量采样与通信']],
   [['单节AFE、均衡与温度'],['20节独立越限检测'],['保护判决、锁存与预充资格']],
   [['偏置供电与电源监视'],['实际桥臂及端口关栅证明','停流、EN与预充状态证明'],['证明域自检、基准与默认撤销','冷启动独立诊断']]],
  'BMS板':[
   [['整包功率'],['门驱动候选','默认关断候选']],
   [['采样与AFE'],['主动均衡功率'],['主动均衡控制']],
   [['控制电源','板载主控'],['独立停机证明供电','插电硬联锁'],['外充控制接口','对外许可']],
   [['隔离通信'],['跨板接口']]],
  '外充板':[
   [['外充输入保护'],['外充四开关功率级'],['外充输出隔离与残能']],
   [['外充独立电源与隔离'],['外充独立停流检测'],['跨板接口']]],
  '配电':[
   [['01 配电与电源接口']],
   [['01 RK独立降压','01 RK自主USB PD源'],['01 RADIO独立降压'],['01 P5独立降压']],
   [['03 双泵功率与检测'],['04 21V独立泵候选'],['02 MCU CAN与硬件许可',
     *(['02 弱电降压与控制'] if any(p['page']=='02 弱电降压与控制' for p in c['parts']) else []),
     *(['输入保护与局部电源'] if any(p['page']=='输入保护与局部电源' for p in c['parts']) else [])]]]}
 result=[];stats=[]
 for board in dict.fromkeys(b['metadata']['board'] for b in blocks):
  own=[b for b in blocks if b['metadata']['board']==board]
  ordered=[b for band in engine['_board_bands'](board,own) for b in band]
  directions=api.get('_port_pin_directions',{})
  for b in ordered:
   ports={'1':set(),'2':set()}
   for key,(point,net) in b['metadata']['geometry']['pins'].items():
    short=net.rsplit('__',1)[-1]
    if engine['is_auxiliary_power'](net) or re.fullmatch(r'(?:.*_)?(?:GND|AGND|DGND|VCC|VDD|VSS|[+-]?\d+V\d*)',short):continue
    kind=str(directions.get(key,''))
    if kind in ports:ports[kind].add(net)
   b['metadata'].update(signal_inputs=sorted(ports['1']),signal_outputs=sorted(ports['2']))
  if c['board']=='配电':
   for b in ordered:
    title=b['metadata']['title'].split(' / ',1)[-1];role=b['metadata']['circuit_role']
    chain=re.search(r'·(AUX|P5|P21)(?:_S2)?保护链·',title)
    if chain:role=chain.group(1)+'输入保护'
    elif title.endswith('·整包输入与左右牵引支路'):role='整包输入与左右牵引'
    elif title.endswith('·独立支路-J_RK12'):role='01 RK独立降压'
    elif title.endswith('·独立支路-J_RADIO5'):role='01 RADIO独立降压'
    elif role=='01 配电与电源接口':role='输入窗口、偏置及故障联锁'
    elif role=='04 21V独立泵候选':role='21V泵降压与负载'
    elif role=='02 MCU CAN与硬件许可' and re.search(r'·(?:U_PDET|U_PUMPS_OFF|.*(?:PUMP_CERT|PDET_RETURN))',title):role='双泵实体关断采样与证明'
    b['metadata']['circuit_role']=role
   plans['配电']=[
    [['整包输入与左右牵引']],
    [['AUX输入保护'],['P5输入保护'],['P21输入保护']],
    [['01 RK独立降压','01 RK自主USB PD源','01 RADIO独立降压'],['01 P5独立降压','03 双泵功率与检测'],['21V泵降压与负载']],
    [['输入窗口、偏置及故障联锁'],['02 MCU CAN与硬件许可'],['双泵实体关断采样与证明']],
    [[r for r in ('02 弱电降压与控制','输入保护与局部电源') if any(b['metadata']['circuit_role']==r for b in ordered)]]]
   plans['配电']=[row for row in plans['配电'] if any(row)]
  physical=c.get('physical_board',c['board']);plan=module('集成E4功能区').regions(physical) if c.get('e4_stable') else plans[physical]
  role_blocks=collections.OrderedDict()
  for b in ordered:role_blocks.setdefault(b['metadata']['circuit_role'],[]).append(b)
  planned={r for row in plan for zone in row for r in zone}
  assert set(role_blocks)<=planned,('未定义的真实功能区',set(role_blocks)-planned)
  plan=[[present for zone in row if (present:=[r for r in zone if r in role_blocks])] for row in plan]
  plan=[row for row in plan if row]
  assert set(role_blocks)=={r for row in plan for zone in row for r in zone}
  name=f'{physical}-01-整板原理图';page=len(result)+1;text=api['text']
  doc={'head':{'docType':'1','editorVersion':'6.5.43','x':0,'y':0,'c_para':{'name':name}},'shape':[
   text(physical+' · 整板原理图',45,40,size=20,ident=f'board_{page}_title'),
   text('上部主功率流；下部供电、控制、采样及联锁。局部电路实体连线，远端信号使用标准网络端口。',45,70,size=10,ident=f'board_{page}_note')]}
  segments=[];pins={};nc={};labels=[];shifts={};textboxes=[];component_textboxes=[];bodyboxes=[];placed=[];regions=[]
  width=0;y=135
  for row in plan:
   x=45;row_height=0
   for roles in row:
    zone=[b for role in roles for b in role_blocks[role]]
    circuit_rows=module('集成E4功能区').region_rows(physical,roles,zone) if c.get('e4_stable') else structured_region_rows(physical,roles,zone,5 if len(row)==1 else 3)
    assert [id(b) for band in circuit_rows for b in band] and sorted(id(b) for band in circuit_rows for b in band)==sorted(map(id,zone)),'拓扑排布不得漏/重电路块'
    # Independent circuits at the same dependency layer need not stretch the
    # entire sheet. Pack whole circuits by measured geometry, never split one
    # circuit or use a fixed number of columns as its electrical structure.
    measured={id(b):math.ceil(max(b['metadata']['content_bounds'][2]-b['metadata']['content_bounds'][0]+140,
     engine['_textwidth'](b['metadata']['title'],11)+50)/5)*5 for b in zone}
    limit=max(max(measured.values()),24000//len(row));packed=[]
    for band in circuit_rows:
     line=[];occupied_width=0
     for b in band:
      span=measured[id(b)]+110
      if line and occupied_width+span>limit:
       packed.append(line);line=[];occupied_width=0
      line.append(b);occupied_width+=span
     if line:packed.append(line)
    circuit_rows=packed
    local=[];zx=0;zy=90;line_height=0;zone_width=0
    for band_number,band in enumerate(circuit_rows):
     if band_number:zy+=line_height+110;zx=0;line_height=0
     for b in band:
      x1,y1,x2,y2=b['metadata']['content_bounds'];title=b['metadata']['title']
      if ' / ' in title:title=title.split(' / ',1)[1]
      if c['board']!='FOC' and '·' in title:title=title.split('·',1)[1]
      bw=math.ceil(max(x2-x1+140,engine['_textwidth'](title,11)+50)/5)*5
      bh=math.ceil((y2-y1+110)/5)*5
      local.append((b,zx,zy,bw,bh,title));zx+=bw+110;zone_width=max(zone_width,zx);line_height=max(line_height,bh)
    heading=module('集成E4功能区').region_heading(physical,roles) if c.get('e4_stable') else ' / '.join(roles)
    zone_width=max(zone_width,math.ceil((engine['_textwidth'](heading,14)+50)/5)*5)
    zone_height=zy+line_height+50
    region_number=len(regions)+1
    doc['shape'].append(f'R~{x}~{y}~~~{zone_width-40}~{zone_height}~#7793AC~2~1~none~board_{page}_region{region_number}_box~0~')
    doc['shape'].append(text(f'{region_number:02d}  '+heading,x+15,y+35,size=20,ident=f'board_{page}_region{region_number}'))
    regions.append({'电气域':roles,'位置':[x,y],'范围':[zone_width,zone_height]})
    for b,lx,ly,bw,bh,title in local:
     bx,by=x+lx,y+ly;x1,y1,_,_=b['metadata']['content_bounds'];dx=bx+35-x1;dy=by+55-y1
     prefix=f'm{page}_{len(placed)+1}_';doc['shape'].append(text(title,bx+15,by+25,size=11,ident=prefix+'title'))
     doc['shape'].extend(engine['_move_shape'](s,dx,dy,prefix,api) for s in b['shape'] if not s.startswith('T~'))
     gx,gy=int(dx/5),int(dy/5);assert gx*5==dx and gy*5==dy
     geometry=b['metadata']['geometry']
     segments.extend(((a[0]+gx,a[1]+gy),(z[0]+gx,z[1]+gy),net) for a,z,net in geometry['segments'])
     pins.update({key:((point[0]+gx,point[1]+gy),net) for key,(point,net) in geometry['pins'].items()})
     nc.update({key:(point[0]+gx,point[1]+gy) for key,point in geometry['nc'].items()})
     labels.extend(((point[0]+gx,point[1]+gy),net) for point,net in geometry['labels'])
     for key,target in [('textboxes',textboxes),('component_textboxes',component_textboxes),('bodyboxes',bodyboxes)]:
      target.extend((a+dx,z+dy,u+dx,v+dy) for a,z,u,v in b['metadata'][key])
     shifts[b['head']['c_para']['name']]=(dx,dy);placed.append({'功能':b['metadata']['title'],'位置':[bx,by],'范围':[bw,bh]})
    x+=zone_width+180;row_height=max(row_height,zone_height)
   width=max(width,x+30);y+=row_height+180
  height=y+35;doc['canvas']=f'CA~{width}~{height}~#FFFFFF~yes~#CCCCCC~10~{width}~{height}~line~10~pixel~5~0~0'
  write(c.get('build_root',CACHE/c['board'])/'结构连接缓存.json',{'源SHA256':c['hashes'],'doc':doc,'segments':segments,
   'pins':[[list(k),p,n] for k,(p,n) in pins.items()],'nc':[[list(k),p] for k,p in nc.items()],
   'labels':labels,'captions':component_textboxes,'bodies':bodyboxes,'width':width,'height':height,'page':page})
  segments,labels,textboxes,geometry_stats=engine['_connect_board'](doc,segments,pins,nc,labels,component_textboxes,bodyboxes,width,height,page,api)
  for boxes in (textboxes,bodyboxes):
   for i,a in enumerate(boxes):
    for b in boxes[i+1:]:assert not engine['_overlap'](a,b),('电气域合并相叠',physical,a,b)
  geometry_stats.update(板=physical,页名=name,功能区=len(placed),电气域=regions,器件=sum(b['metadata']['layout']['器件'] for b in own),
   画布尺寸=[width,height],导线段=len(segments),实体重叠=0,元件及网标文字相叠=0,文字框核验=len(textboxes),
   字体度量='simhei/Arial实际字宽，pt×100/72',同板跨功能共网核验=True,
   排布依据='明确功率链/实体通道；其余按输出到输入及反馈环，不按固定器件数或列数拆排',视觉验收='NOT_RUN')
  doc['metadata']={'board':board,'title':'整板原理图','layout':geometry_stats,'功能区':placed,'textboxes':textboxes,'bodyboxes':bodyboxes}
  for item in inventory:
   if item['板']!=board:continue
   dx,dy=shifts[item['页名']];item.update(位置=[item['位置'][0]+dx,item['位置'][1]+dy],页=page,页名=name)
  result.append(doc);stats.append(geometry_stats)
 assert len(result)==len({b['metadata']['board'] for b in blocks})
 return result,stats


def single_sheet_candidate(c):
 """Build only cached editable sheet input; do not write live board evidence/BOM."""
 api=module('生成可编辑原理图')
 if not packet(c).exists():
  bound=read(LIB/'封装绑定.json')['板级绑定'][c['board']]
  assert bound['板源文件SHA256']==c['hashes'] and bound['源SHA256']==c['digest']
  refs={p['ref'] for p in c['parts']};selected=[b for b in bound['位号绑定'] if b['位号'] in refs]
  assert {b['位号'] for b in selected}==refs
  packet(c).parent.mkdir(parents=True,exist_ok=True)
  write(packet(c),{'源SHA256':c['digest'],'板源文件SHA256':c['hashes'],'绑定':selected,
   '原理图范围':c.get('native_scope'),'候选用途':'仅板上器件原理图候选；非官方验收输入'})
 inp=read(packet(c))
 assert inp['源SHA256']==c['digest'] and inp.get('板源文件SHA256',c['hashes'])==c['hashes']
 refs={p['ref'] for p in c['parts']}
 if {b['位号'] for b in inp['绑定']}!=refs:
  # Older board-only candidates omitted external contactors/capacitors.
  # Re-select exact-source bindings, without changing addIntoPcb status.
  bound=read(LIB/'封装绑定.json')['板级绑定'][c['board']]
  assert bound['板源文件SHA256']==c['hashes'] and bound['源SHA256']==c['digest']
  selected=[b for b in bound['位号绑定'] if b['位号'] in refs]
  assert {b['位号'] for b in selected}==refs
  inp=dict(inp,绑定=selected,原理图范围=c.get('native_scope'),候选用途='仅板上器件原理图候选；板外器件不进入工程，非官方验收输入')
  write(packet(c),inp)
 if c.get('refresh_bindings'):
  current,diffs=bind(c)
  inp=dict(inp,绑定=list(current.values()),逐脚功能差异=diffs)
  write(packet(c),inp)
 bindings={b['位号']:b for b in inp['绑定']}
 if c.get('native_scope'):
  if inp.get('原理图范围')!=c['native_scope']:
   inp=dict(inp,原理图范围=c['native_scope'],候选用途='仅板上器件原理图候选；板外器件不进入工程，非官方验收输入')
   write(packet(c),inp)
  assert len(bindings)==c['native_scope']['board_on_ref_count']
  assert scope_digest(set(bindings))==c['native_scope']['board_on_refs_sha256']
  assert all(b['安装']=='板上' and b.get('封装') for b in bindings.values()), '板上器件必须绑定真实封装；不得由板外例外填补'
 sheets,nets,nc,inventory,wiring=functional_sheets(c,bindings,raw_objects(),api)
 expected_nets,expected_nc,aliases=physical_connection_contract(c['parts'],bindings)
 assert nets==expected_nets and nc==expected_nc,'真实引脚映射后图面针网/NC与完整源不一致'
 wiring['源端子与实际铜端子映射']={'源CAD端子数':sum(len(p['pins']) for p in c['parts']),
  '实际铜端子数':len(expected_nets)+len(expected_nc),'显式同网别名':aliases,
  '全量连接与NC集合一致':True,'范围':'仅显式同网别名折叠；不造厂家第六Drain铜盘'}
 output=candidate_path(c)
 write(output,{'板源文件SHA256':c['hashes'],'工具SHA256':c['tool_sha'],'原理图范围':c.get('native_scope'),
  'sheets':sheets,'nets':[[r,p,n] for (r,p),n in nets.items()],
  'nc':sorted(nc),'inventory':inventory,'wiring':wiring})
 print(dump({'候选':str(output),'SHA256':sha(output),'页数':len(sheets),
  '按板页数':wiring['按板页数'],'原理图范围':c.get('native_scope'),'源SHA256':c['hashes']}),flush=True)

def reassociate_note_only_candidate(board,old_revision,new_revision,physical_board):
 """仅备注修订时关联已核同页几何；不继承任何官方或电气PASS。"""
 old=source(board,revision=old_revision);new=source(board,revision=new_revision)
 assert board=='FOC' and physical_board in ('驱动主板','中央稳压模块','辅助电源板')
 select=lambda c:{p['ref']:p for p in c['parts'] if p['board']==physical_board}
 before,after=select(old),select(new);assert before.keys()==after.keys()
 note_changes=[]
 for ref,p in before.items():
  q=after[ref]
  assert {k:v for k,v in p.items() if k!='note'}=={k:v for k,v in q.items() if k!='note'},(ref,'非备注差额，须重新生成图面')
  if p.get('note')!=q.get('note'):note_changes.append(ref)
 origin=old['base']/physical_board/'单页图面候选.json';candidate=read(origin)
 assert candidate['板源文件SHA256']==old['hashes']
 expected={(r,n):v for r,p in after.items() for n,v in p['pins'].items() if not v.startswith('NC_')}
 expected_nc={(r,n) for r,p in after.items() for n,v in p['pins'].items() if v.startswith('NC_')}
 assert {(r,n):v for r,n,v in candidate['nets']}==expected
 assert {tuple(v) for v in candidate['nc']}==expected_nc
 assert {v['位号'] for v in candidate['inventory']}==set(after)
 assert len(candidate['sheets'])==1 and candidate['wiring']['按板页数']=={physical_board:1}
 target=new['base']/physical_board;target.mkdir(exist_ok=True)
 output=target/'单页图面候选.json';assert not output.exists(),'新版本候选已存在，不覆盖'
 candidate['板源文件SHA256']=new['hashes']
 candidate['备注差额来源关联']={'原候选':str(origin.relative_to(ROOT)),'原候选SHA256':sha(origin),
  '原板源文件SHA256':old['hashes'],'当前板源文件SHA256':new['hashes'],
  '变化备注位号':note_changes,'核对':'本板全部器件除note外所有字段、逐脚连接、NC、位号清单及单页相等',
  '关联工具SHA256':TOOL_SHA,'官方验收继承':False,'整板放行':False}
 write(output,candidate)
 bound=read(LIB/'封装绑定.json')['板级绑定'][board]
 assert bound['板源文件SHA256']==new['hashes'] and bound['源SHA256']==new['digest']
 bindings=[b for b in bound['位号绑定'] if b['位号'] in after]
 assert {b['位号'] for b in bindings}==set(after)
 write(target/'单页工具集成输入.json',{'源SHA256':new['digest'],'板源文件SHA256':new['hashes'],
  '绑定':bindings,'候选用途':'仅备注差额已逐字段核对的单页工具候选；非官方验收输入'})
 return {'板':physical_board,'器件':len(after),'变化备注位号':note_changes,'候选SHA256':sha(output)}

def frozen_netlist_probe(c):
 """Qualify the official string getter on preserved old input, without promotion."""
 report=c['live_base']/CONFIG[c['board']][4];j=read(report)
 record=j['native_validation_boards'][c['board']] if c['board'] in SPLIT_BOARDS else j['native_validation']
 assert record['板源文件SHA256']==c['hashes']
 origin=c['live_base']/record['原生工程'];origin_sha=sha(origin)
 assert origin_sha==record['原生工程SHA256']
 cache=CACHE/c['board'];d=module('原理图交付');d.CACHE=cache
 key='冻结源官方字符串网表路径'
 if key in j.get('integration_tool_checks',{}).get(c['board'],{}):
  print('已有单次路径检查记录，不重复调用',flush=True);return
 assert not [s for s in d.cli(EXE,'session','list')['value'] if s['status'] not in ('closed','destroyed')]
 clone=cache/'官方兼容读取.eprj2'
 assert not clone.exists(),'单次路径检查副本已经存在，须检查上次结果'
 d.sqlite_copy(origin,clone);session=None;inp=read(packet(c))
 result={'板源文件SHA256':c['hashes'],'源SHA256':c['digest'],
  '原件':str(origin.relative_to(ROOT)),'原件SHA256':origin_sha,
  '隔离副本':str(clone.relative_to(ROOT)),'当前源适用':False,
  '接口':'eda.sch_Netlist.getNetlist(Protel2)','工具SHA256':sha(__file__)}
 def invoke(code):return d.cli(EXE,'invoke','--session',session,'--ext-uuid','eda','--timeout','60000','--code',code)['value']
 try:
  session=d.cli(EXE,'open','--path',clone.as_posix(),'--headless','true')['value']['sessionId']
  d.wait_for_project(invoke)
  pages=invoke('return await eda.dmt_Schematic.getAllSchematicPagesInfo();')
  assert len(pages)==inp['页数'];page=pages[0]['uuid'];d.open_document(invoke,page)
  time.sleep(3)
  result['焦点']=invoke('return {page:await eda.dmt_Schematic.getCurrentSchematicPageInfo(),schematic:await eda.dmt_Schematic.getCurrentSchematicInfo()};')
  assert result['焦点']['page']['uuid']==page
  reply=invoke('try{const v=await eda.sch_Netlist.getNetlist("Protel2");return {type:typeof v,text:typeof v==="string"?v:null};}catch(e){return {type:"throw",error:String(e)};}')
  result['返回']={k:v for k,v in reply.items() if k!='text'}
  if reply.get('text'):
   path,file_sha=save_export_text(cache,'官方兼容网表.net',reply['text'])
   result.update(网表文件=str(path.relative_to(ROOT)),网表SHA256=file_sha,文本长度=len(reply['text']))
   result['全量核对']=verify_protel2(reply['text'],inp)
  else:result['全量核对']={'status':'FAIL_NO_OFFICIAL_TEXT'}
 except Exception as e:result['失败']=type(e).__name__+': '+str(e)[:4000]
 finally:
  if session:d.cli(EXE,'session','close','--session',session,'--destroy')
  result['原件未变']=sha(origin)==origin_sha;result['隔离副本SHA256']=sha(clone)
  j=read(report)
  j.setdefault('integration_tool_checks',{}).setdefault(c['board'],{})[key]=result
  write(report,j)
 print(dump(result),flush=True)

def generate(c):
 if not c.get('preview_only'):
  assert c.get('structured_regions'), '正式生成不得使用旧排列版'
  assert c['board']!='FOC' or c.get('physical_board') in ('驱动主板','中央稳压模块','辅助电源板'), '先选择实体板，再生成独立工程'
 api=module('生成可编辑原理图');board_cache=c.get('build_root',CACHE/c['board']);board_cache.mkdir(parents=True,exist_ok=True)
 if c.get('frozen'):
  if c.get('preview_only'):
   prior=read(packet(c))
  elif c.get('revision'):
   prior=read(LIB/'封装绑定.json')['板级绑定'][c['board']]
   assert prior['板源文件SHA256']==c['hashes'],'先按本次保全版本串行生成整域公共绑定'
   prior=dict(prior,绑定=prior['位号绑定'])
  else:prior=read(CACHE/c['board']/'集成输入.json')
  assert prior['源SHA256']==c['digest'] and prior.get('板源文件SHA256',c['hashes'])==c['hashes']
  refs={p['ref'] for p in c['parts']}
  bindings={b['位号']:b for b in prior['绑定'] if b['位号'] in refs};diffs=prior.get('逐脚功能差异',[])
  cache=new_export_dir(board_cache,'单页工具构建')
  if c['report'].is_file() and not c.get('preview_only'):preserve_previous_validation(c,cache)
  if c.get('refresh_bindings') or prior.get('封装库SHA256')!=sha(LIB/'可导入封装库.zip'):
   if c.get('physical_board'):
    # A physical-board preview consumes the already bound full-domain batch.
    # Never replace its 1610-ref public record with this 861-ref subset.
    full=read(LIB/'封装绑定.json')['板级绑定'][c['board']]
    assert full['板源文件SHA256']==c['hashes'] and full['源SHA256']==c['digest']
    bindings={b['位号']:b for b in full['位号绑定'] if b['位号'] in refs}
    assert set(bindings)==refs,'整域公共绑定没有覆盖本实体板'
    diffs=[v for v in full.get('逐脚功能差异',[]) if v['位号'] in refs]
   else:bindings,diffs=bind(c)
 else:
  cache=new_export_dir(board_cache,'功能原理图')
  preserve_previous_validation(c,cache)
  bindings,diffs=bind(c)
 api.CACHE=cache
 library_sha=sha(LIB/'可导入封装库.zip')
 raw=raw_objects();sheets=[];expected={};nc=set();plans={};real_refs=[]
 if c.get('preview_only'):
  candidate=read(candidate_path(c));assert candidate['板源文件SHA256']==c['hashes']
  c['candidate_generator_sha']=candidate['工具SHA256']
  sheets=candidate['sheets'];expected={(r,p):n for r,p,n in candidate['nets']};nc={tuple(v) for v in candidate['nc']}
  inventory=candidate['inventory'];wiring=candidate['wiring']
 else:sheets,expected,nc,inventory,wiring=functional_sheets(c,bindings,raw,api)
 validate_single_physical_sheet(c,sheets,inventory)
 page_by_ref={item['位号']:item['页名'] for item in inventory}
 for sheet in sheets:
  sheet['docType']='1';page=sheet['head']['c_para']['name']
  plans[page]=sheet['metadata_native_flags']
  for flag in plans[page]:
   if re.search(r'(?:^|__)GND$',flag['net']):flag['type']='Ground'
  for index,shape in enumerate(sheet['shape']):
   if not shape.startswith('LIB~'):continue
   chunks=shape.split('#@$');ref=next(q.split('~')[12] for q in chunks[1:] if q.startswith('T~P~'))
   p=next(p for p in c['parts'] if p['ref']==ref);b=bindings[ref]
   attrs={'pre':ref,'name':p['mpn'] or p['model'],'BOM_Manufacturer Part':p['mpn'],
    'package':b['封装'],'BOM_Value':p['value'],'BOM_Manufacturer':p['manufacturer'],
    'BOM_Assembly':p.get('assembly','候选装配禁止生产'),'BOM_Status':'候选，制造未放行',
    'BOM_Source_SHA256':c['digest'],'BOM_PCB_Placement':'yes' if p['onboard'] else 'no',
    'spicePre':ref[0]}
   if 'fitted' in p:attrs['BOM_Fitted']=str(p['fitted']).lower()
   if 'procurement_quantity' in p:attrs['BOM_Procurement_Quantity']=str(p['procurement_quantity'])
   if c.get('e4_stable'):
    attrs['BOM_Default_Quantity']=str(0 if p.get('fitted') is False else p['quantity'])
    if 'assembly_profiles' in p:attrs['BOM_Assembly_Profiles']=dump(p['assembly_profiles'])
    if 'runtime_assembly_option' in p:attrs['BOM_Runtime_Assembly_Option']=p['runtime_assembly_option']
   if 'assembly_domain' in p:attrs['BOM_Assembly_Domain']=p['assembly_domain']
   if 'cap_contract' in p:
    spec=c['data']['CAP_SPECS'][p['model']];attrs.update(BOM_Value=str(spec['nominal_uF'])+'uF',
     BOM_Manufacturer=spec['manufacturer'],BOM_Tolerance=str(spec['initial_tolerance']*100)+'%',
     BOM_Voltage=str(spec['rated_V'])+'V',BOM_Dielectric=spec['dielectric'],BOM_Case=spec['case_candidate'],
     BOM_Cap_Contract=json.dumps(p['cap_contract'],ensure_ascii=True,separators=(',',':')))
   header=chunks[0].split('~');header[3]=''.join(k+'`'+str(v)+'`' for k,v in attrs.items())
   # Placement is the electrical author's physical boundary. A footprint
   # still awaiting qualification is NOT a board-external component.
   assert isinstance(p['onboard'],bool)
   header[11]='yes' if p['onboard'] else 'none'
   chunks[0]='~'.join(header);sheet['shape'][index]='#@$'.join(chunks)
 sourcezip=cache/'转换源.zip';needed={b['库文件'] for b in bindings.values() if b.get('库文件')}
 native_scope=copy.deepcopy(c.get('native_scope'))
 if native_scope:
  selected_refs={p['ref'] for p in c['parts']}
  assert len(bindings)==native_scope['board_on_ref_count'] and scope_digest(selected_refs)==native_scope['board_on_refs_sha256']
  assert all(p.get('installation')=='板上' and p.get('pcb_footprint_required') is True for p in c['parts'])
  assert all(b.get('安装')=='板上' and b.get('封装') for b in bindings.values())
  native_scope['embedded_footprint_library_member_count']=len(needed)
  native_scope['embedded_footprint_library_members']=sorted(needed)
 with zipfile.ZipFile(sourcezip,'w',zipfile.ZIP_DEFLATED) as z,zipfile.ZipFile(LIB/'可导入封装库.zip') as fp:
  for n in sorted(needed):
   payload=fp.read(n)
   assert all(hashlib.sha256(payload).hexdigest()==b['封装SHA256'] for b in bindings.values() if b.get('库文件')==n),'封装成员版本不符'
   doc=json.loads(payload);doc['shape']=[s for s in doc['shape'] if not s.startswith('SVGNODE~')]
   # 同机械包UUID可被多个完整型号共用；转换输入按唯一库名命名，防止别名覆盖。
   doc['head']['uuid']=uuid.uuid5(uuid.NAMESPACE_URL,'board-footprint/'+n).hex
   for k in list(doc['head'].get('c_para',{})):
    if '3d' in k.lower():del doc['head']['c_para'][k]
   z.writestr(n,json.dumps(doc,ensure_ascii=False))
  z.writestr(c['name']+'.json',json.dumps({'docType':'5','title':c['name'],
   'schematics':[{'title':s['head']['c_para']['name'],'dataStr':s} for s in sheets]},ensure_ascii=False))
 if native_scope:
  with zipfile.ZipFile(sourcezip) as z:
   expected_members=set(needed)|{c['name']+'.json'}
   assert set(z.namelist())==expected_members, '原生转换包出现板上绑定之外的封装库成员'
 assert sha(LIB/'可导入封装库.zip')==library_sha,'共享库在读取期间改变'
 api.convert(sourcezip,c['name'],encoding='easyeda-pro-2');exchange=cache/(c['name']+'.epro2')
 caption_check=restore_component_captions(exchange,sheets)
 verify=module('核验交换原理图').verify_exchange
 checkparts=copy.deepcopy(c['parts'])
 for p in checkparts:
  p['model']=p['mpn'];p.pop('approved_binding',None);p.pop('mechanical_candidate',None)
  b=bindings[p['ref']]
  if b.get('库文件'):
   p['approved_binding']={'footprint':b['封装'],'member':b['库文件'],'sha256':b['封装SHA256'],
    'physical_pin_to_pad':b['引脚映射']}
 evidence=verify(exchange,expected,nc,parts=checkparts,hardware=HW,cap_specs=c['data'].get('CAP_SPECS'),strict_full_BOM=True)
 if c.get('preview_only'):
  preview=dict(prior,绑定=list(bindings.values()),逐脚功能差异=diffs,封装库SHA256=library_sha,原理图范围=native_scope,
   交换文件=str(exchange),交换SHA256=sha(exchange),构建目录=str(cache),标准端口计划=plans,
   图面组织核验=wiring,位号图页=page_by_ref,交换回读=evidence,可见元件标注=caption_check,
   页数=len(sheets),首页=sheets[0]['head']['c_para']['name'],预期网络=[[r,p,n] for (r,p),n in expected.items()],
   NC=[list(x) for x in sorted(nc)],候选文件SHA256=sha(candidate_path(c)))
  write(cache/'结构预览输入.json',preview)
  write(candidate_path(c).parent/'结构预览输入.json',preview)
  return preview
 # BOM取实际转换Device/组件属性，避免把源表回显当回读。
 with zipfile.ZipFile(exchange) as z:
  lines=z.read(next(n for n in z.namelist() if n.endswith('.epru'))).decode('utf8').splitlines()
 attrs=collections.defaultdict(dict);kind=None
 for line in lines:
  a,b=map(json.loads,line.rstrip('|').split('||'))
  if a['type']=='DOCHEAD':kind=b['docType'];docid=b['uuid']
  if kind=='SCH_PAGE' and a['type']=='ATTR':attrs[(docid,b['parentId'])][b['key']]=b['value']
 bom=[]
 for p in c['parts']:
  found=[a for a in attrs.values() if a.get('Designator')==p['ref']];assert len(found)==1
  a=found[0];assert a.get('Manufacturer Part','')==p['mpn'] and a['Assembly']==p.get('assembly','候选装配禁止生产')
  bom.append({'位号':p['ref'],'完整型号':a.get('Manufacturer Part',''),'数值':a.get('Value',''),
   '制造商':a.get('Manufacturer',''),'数量':p['quantity'],'装配':a['Assembly'],
   '实装':a.get('Fitted','未声明'),'采购数量':a.get('Procurement_Quantity','未声明'),'装配域':a.get('Assembly_Domain','未声明'),
   '安装位置':bindings[p['ref']]['安装'],'原理图页':page_by_ref[p['ref']],'封装':bindings[p['ref']]['封装'],
   '封装状态':bindings[p['ref']]['封装状态'],'制造放行':'否','源SHA256':c['digest']})
  if c['board'] in SPLIT_BOARDS:
   accessories=p.get('accessories','')
   bom[-1]['配套件']=accessories if isinstance(accessories,str) else dump(accessories)
   bom[-1]['配套件来源']='来自同SHA源合同 '+c['digest']+'；未声称机械/封装验收' if accessories else '同SHA源未列配套件'
 out=c['target'];out.mkdir(parents=True,exist_ok=True)
 bompath=c['bom_path'] if c['board'] in SPLIT_BOARDS else out/({'配电':'系统辅助板BOM.csv','FOC':'电机驱动BOM.csv'}[c['board']])
 bompath.parent.mkdir(parents=True,exist_ok=True)
 with bompath.open('w',encoding='utf-8-sig',newline='') as f:
  w=csv.DictWriter(f,fieldnames=list(bom[0]));w.writeheader();w.writerows(bom)
 if native_scope:
  with bompath.open(encoding='utf-8-sig',newline='') as f:bom_rows=list(csv.DictReader(f))
  bom_refs={r['位号'] for r in bom_rows}
  assert len(bom_rows)==native_scope['board_on_ref_count'] and scope_digest(bom_refs)==native_scope['board_on_refs_sha256'], '板上BOM位号集不等于冻结板上源'
 input={'源SHA256':c['digest'],'板源文件SHA256':c['hashes'],'交换文件':str(exchange),'交换SHA256':sha(exchange),
  '原理图范围':native_scope,
  '工具SHA256':c['tool_sha'],'封装库SHA256':library_sha,'保全旧源工具验证':bool(c.get('frozen')),
  '构建目录':str(cache),'首页':sheets[0]['head']['c_para']['name'],'位号图页':page_by_ref,
  '图面组织核验':wiring,'可见元件标注':caption_check,'页数':len(sheets),'预期网络':[[r,p,n] for (r,p),n in expected.items()],
  'NC':[list(x) for x in sorted(nc)],'标准端口计划':plans,'端口坐标倍率':1,'复用真实符号':real_refs,
  '原理图范围':native_scope,
  '交换回读':evidence,'绑定':list(bindings.values()),'逐脚功能差异':diffs,'BOM':str(bompath),'BOM_SHA256':sha(bompath)}
 write(packet(c),input)
 result={'源SHA256':c['digest'],'板源文件SHA256':c['hashes'],'工具':'集成板级原理图.py',
  '软件版本':'4.1.60.198f38ab','器件':len(c['parts']),'页数':len(sheets),'原理图范围':native_scope,
  '图面组织核验':wiring,'符号表达':'保留完整物理脚号的功能符号；局部实体连线和原生跨页端口',
  '交换逐脚回读':evidence,'真实符号复用数':len(real_refs),'已绑定封装位号':sum(bool(b['封装']) for b in bindings.values()),
  '未绑定板上器件':[{'位号':b['位号'],'型号':b['型号'],'安装':b['安装']} for b in bindings.values() if b['安装'] in ('板上','待设计') and not b['封装']],
  '逐脚功能差异待审':diffs,'BOM文件':artifact_relative_path(bompath,c['base']),'BOM_SHA256':sha(bompath),
  '官方导入':False,'官方编辑保存独立重开':False,'有效官方网表':False,'官方ERC已执行':False,'ERC通过':False,
  '整板放行':False,'制造放行':False}
 update(c,result);print(dump({'源SHA256':c['digest'],'器件':len(c['parts']),'页数':len(sheets),
  '连接':len(expected),'NC':len(nc),'真实符号':len(real_refs),'绑定':result['已绑定封装位号'],
  '未绑定板上':len(result['未绑定板上器件']),'BOM实际回读':evidence['full_BOM_readback']}),flush=True)

def preview_structured_candidate(c):
 """正式工程不变：对精确源候选做官方SVG和全量回读，不继承正式PASS。"""
 c=dict(c,preview_only=True);saved=candidate_path(c).parent/'结构预览输入.json'
 inp=read(saved) if saved.exists() else None
 if (not inp or inp.get('候选文件SHA256')!=sha(candidate_path(c))
     or inp.get('板源文件SHA256')!=c['hashes']
     or inp.get('封装库SHA256')!=sha(LIB/'可导入封装库.zip')):inp=generate(c)
 c['candidate_generator_sha']=read(candidate_path(c))['工具SHA256']
 d=module('原理图交付');session=None;out=Path(inp['构建目录'])
 assert not [s for s in d.cli(EXE,'session','list')['value'] if s.get('status') not in ('closed','destroyed')]
 c['preview_input']=inp;folder_evidence=direct_folder(c);entry=ROOT/folder_evidence['工程索引']
 check=verify_current_graph(c,inp,Path(inp['交换文件']))
 def invoke(code):return d.cli(EXE,'invoke','--session',session,'--ext-uuid','eda','--timeout','60000','--code',code)['value']
 try:
  session=d.cli(EXE,'open','--path',entry.as_posix(),'--headless','true')['value']['sessionId'];d.wait_for_project(invoke)
  pages=invoke('return await eda.dmt_Schematic.getAllSchematicPagesInfo();');assert len(pages)==1
  d.open_document(invoke,pages[0]['uuid'])
  repeated=invoke('const p='+json.dumps(inp['首页'])+';return (await eda.sch_PrimitiveAttribute.getAll()).filter(a=>{const v=a.getState_Value();return typeof v==="string"&&v.startsWith(p+",")}).map(a=>({id:a.getState_PrimitiveId(),key:a.getState_Key(),value:a.getState_Value(),visible:a.getState_ValueVisible()}));')
  print(dump({'同页重复引用属性':repeated[:3],'重复引用数量':len(repeated)}),flush=True)
  svg=invoke('const f=await eda.sch_ManufactureData.getSvgFile("结构候选官方图面");return f?await f.text():null;')
  assert svg and '<svg' in svg
  svg_path=out/'结构候选官方图面.svg';svg_bytes=svg.encode('utf8');prior_svg=None
  if svg_path.exists():
   if svg_path.read_bytes()==svg_bytes:
    path,h=svg_path,sha(svg_path)
   else:
    prior_svg={'path':str(svg_path.relative_to(ROOT)),'sha256':sha(svg_path),
     'preserved':True,'byte_match_to_current_export':False}
    out=new_export_dir(out.parent,'结构候选预览复核')
    path,h=save_export_text(out,'结构候选官方图面.svg',svg)
  else:path,h=save_export_text(out,'结构候选官方图面.svg',svg)
  r=validation_result(c)
  if r.get('结构图面候选'):r.setdefault('结构图面候选历史',[]).append(copy.deepcopy(r['结构图面候选']))
  r['结构图面候选']={'板源文件SHA256':c['hashes'],'工具SHA256':c['tool_sha'],
   '候选布局生成器SHA256':c['candidate_generator_sha'],
   '候选完整eprj3目录':folder_evidence,
   '页数':1,'官方SVG':str(path.relative_to(ROOT)),'SVG_SHA256':h,
   'SVG缓存复核':{'此前冲突SVG':prior_svg,'当前尝试目录':str(out.relative_to(ROOT))},
   '全量交换逐脚BOM':check,
   '正式工程未覆盖':True,'图面组织核验':inp['图面组织核验'],'视觉验收':'待实际渲染检查'}
  update(c,r);print(dump({'官方SVG':str(path),'页数':1,'正式工程未覆盖':True,'交换元件':check['actual_component_refs']}),flush=True)
 except Exception as error:
  diagnostic={'板源文件SHA256':c['hashes'],'候选完整eprj3目录':folder_evidence,'错误':str(error),'正式工程未覆盖':True}
  if session:
   try:diagnostic['官方日志']=invoke('return await eda.sys_Log.sort();')
   except Exception as log_error:diagnostic['日志读取错误']=str(log_error)
  r=validation_result(c);r['结构候选失败']=diagnostic;update(c,r)
  print(dump(diagnostic),flush=True);raise
 finally:
  if session:d.cli(EXE,'session','close','--session',session,'--destroy')


def official_export_implementation():
 """Read-only evidence: preflight fatal errors suppress the export callback."""
 path=Path('D:/lceda-pro/resources/app/assets/pro-sch/4.1.54.bfdf9a4d/js/sch.js')
 code=path.read_text(encoding='utf8')
 needles=('async function HV(i,t)', 'async function GL(i,t,e,r,n,s,a,o=!1)', 'async function xb(i,t,e={},r=[])')
 evidence=[]
 for needle in needles:
  offset=code.index(needle)
  evidence.append({'定位':needle,'字符偏移':offset,'实现片段':code[offset:offset+1200]})
 assert 'await xb(0,i,{isConvert2Pcb:n})===0?' in code
 return {'文件':str(path),'SHA256':sha(path),'定位':evidence,
  '静态结论':'HV仅在GL回调赋值；GL要求xb导出前检致命错误增量为0，否则无回调，HV返回undefined。未绕过规则或权限。',
  '证明边界':'实现路径证据，不冒充本工程每一条ERC错误的运行时因果隔离。'}

def native_duplicate_caption_targets(folder):
 d=module('原理图交付');attrs={};kind=None
 for _,(a,b) in d.records(next(Path(folder).rglob('*.esch2')).read_text(encoding='utf8')):
  if a['type']=='DOCHEAD':kind=b['docType']
  if kind=='SCH_PAGE' and a['type']=='ATTR':attrs.setdefault(b['parentId'],{})[b['key']]=(a,b)
 ports=collections.defaultdict(list)
 for v in attrs.values():
  if 'Device' in v and 'Name' in v and 'Designator' not in v and v['Name'][1].get('valueVisible') is True:ports[v['Name'][1]['value']].append(v['Name'])
 result=[]
 for v in attrs.values():
  if 'Device' in v or 'NET' not in v or v['NET'][1]['value'] not in ports:continue
  a,b=v['NET'];pa,pb=min(ports[b['value']],key=lambda p:(p[1].get('x',0)-b.get('x',0))**2+(p[1].get('y',0)-b.get('y',0))**2)
  result.append({'id':a['id'],'net':b['value'],'portNameAttribute':pa['id']})
 return result

def hide_duplicate_net_captions(invoke,targets):
 """4.1.60实际运行时读回并隐藏已有原生端口重复的导线NET文字。"""
 result={'onlyDisplay':True,'nativePortNames':0,'visibleBefore':0,'hidden':0,'attributes':[]}
 for start in range(0,len(targets),64):
  batch=invoke('const targets='+dump(targets[start:start+64])+';'+'''const ports=[...(await eda.sch_PrimitiveComponent.getAll("netport")),...(await eda.sch_PrimitiveComponent.getAll("netflag"))];
const names=new Set(ports.map(p=>p.getState_Net()).filter(Boolean));
const duplicate=[];for(const t of targets){const a=await eda.sch_PrimitiveAttribute.get(t.id);if(!a||!["NET","Name"].includes(a.getState_Key())||a.getState_Value()!==t.net||!names.has(t.net))throw new Error("冻结导线文字/原生端口不一致 "+JSON.stringify({target:t,key:a?.getState_Key(),value:a?.getState_Value(),namePresent:names.has(t.net)}));duplicate.push({a,t});}
const visibleBefore=duplicate.filter(o=>o.a.getState_ValueVisible()===true).length;
const changed=[];for(const {a,t} of duplicate){const id=a.getState_PrimitiveId(),value=a.getState_Value();
const edit={valueVisible:false,keyVisible:false};
// 4.1.60 may regenerate a few wire captions as visible on reopen. Give only
// currently visible duplicates the existing port Name's exact position/style,
// so regeneration does not lay a second displaced label across nearby text.
if(a.getState_ValueVisible()===true){const p=await eda.sch_PrimitiveAttribute.get(t.portNameAttribute);if(!p||p.getState_Value()!==value||p.getState_ValueVisible()!==true)throw new Error("配对原生端口Name不可读");Object.assign(edit,{x:p.getState_X(),y:p.getState_Y(),alignMode:p.getState_AlignMode(),fontSize:p.getState_FontSize()/100,fontName:p.getState_FontName()});}
if(a.getState_ValueVisible()===true)await eda.sch_PrimitiveAttribute.modify(a,edit);
const b=await eda.sch_PrimitiveAttribute.get(id);if(b.getState_ValueVisible()!==false||b.getState_Value()!==value)throw new Error("重复网标显示修正未生效");changed.push({id,net:value,portNameAttribute:t.portNameAttribute,coalescedPosition:edit.x===undefined?null:{x:edit.x,y:edit.y,alignMode:edit.alignMode,fontSize:edit.fontSize,fontName:edit.fontName}});}
return {onlyDisplay:true,nativePortNames:names.size,visibleBefore,hidden:changed.length,attributes:changed};''')
  result['nativePortNames']=batch['nativePortNames'];result['visibleBefore']+=batch['visibleBefore'];result['hidden']+=batch['hidden'];result['attributes'].extend(batch['attributes'])
 return result

def verify_duplicate_net_captions(invoke,targets):
 """独立重开后核对隐藏或与可读端口Name精确同位；不把立即回读当持久化。"""
 result={'status':'PASS','hidden':0,'regeneratedCoincident':0,'attributes':[]}
 for start in range(0,len(targets),64):
  batch=invoke('const expected='+dump(targets[start:start+64])+';'+'''const out=[];for(const e of expected){const a=await eda.sch_PrimitiveAttribute.get(e.id),p=await eda.sch_PrimitiveAttribute.get(e.portNameAttribute);if(!a||!p||a.getState_Value()!==e.net||p.getState_Value()!==e.net)throw new Error("独立重开网名发生变化 "+JSON.stringify({expected:e,wire:a?.getState_Value(),port:p?.getState_Value()}));const visible=a.getState_ValueVisible();const samePosition=a.getState_X()===p.getState_X()&&a.getState_Y()===p.getState_Y()&&a.getState_AlignMode()===p.getState_AlignMode()&&a.getState_FontSize()===p.getState_FontSize()&&a.getState_FontName()===p.getState_FontName();if(visible!==false&&(!samePosition||p.getState_ValueVisible()!==true))throw new Error("重开后仍存在位移或不可读的重复网标 "+e.id);out.push({id:e.id,net:e.net,portNameAttribute:e.portNameAttribute,visible,samePosition});}return out;''')
  result['hidden']+=sum(a['visible'] is False for a in batch);result['regeneratedCoincident']+=sum(a['visible'] is True for a in batch);result['attributes'].extend(batch)
 return result

def refine_structured_candidate(c):
 """只修单页候选显示；真实编辑保存、独立重开及全量官方回读。"""
 c=dict(c,preview_only=True);r=validation_result(c);record=r['结构图面候选']
 assert record['板源文件SHA256']==c['hashes'] and record['页数']==1
 entry=ROOT/record['候选完整eprj3目录']['工程索引']
 saved=candidate_path(c).parent/'结构预览输入.json'
 inp=read(saved if saved.exists() else packet(c))
 assert inp['板源文件SHA256']==c['hashes']
 d=module('原理图交付');session=None;out=new_export_dir(entry.parent.parent,'结构候选保存')
 assert not [s for s in d.cli(EXE,'session','list')['value'] if s.get('status') not in ('closed','destroyed')]
 recover_existing=bool(record.get('候选验收失败') and
  record.get('候选完整目录文件SHA256')=={p.relative_to(entry.parent).as_posix():sha(p) for p in entry.parent.rglob('*') if p.is_file()})
 # Native ATTR display fields are part of the public file format. Explicitly
 # hide same-sheet Relevance on ports before loading, avoiding thousands of
 # generated-attribute undo operations (which exhausted the 4.1.60 renderer).
 changes=0;title_cleanup=[]
 for schematic in entry.parent.rglob('*.esch2'):
  rows=[row for _,row in d.records(schematic.read_text(encoding='utf8'))];device_names={};kind=None;uuid_now=None;props={};page_rows=[]
  for a,b in rows:
   if a['type']=='DOCHEAD':kind=b['docType'];uuid_now=b['uuid']
   elif kind=='DEVICE' and a['type']=='META':device_names[uuid_now]=b['title']
   elif kind=='SCH_PAGE':
    page_rows.append((a,b))
    if a['type']=='ATTR':props.setdefault(b['parentId'],{})[b['key']]=(a,b)
  if c.get('e4_stable'):
   title_rows=[(a,b) for a,b in page_rows if a['type']=='TEXT' and '整板原理图' in b.get('value','')]
   assert title_rows and len({(b['x'],b['y'],b.get('rotation',0)) for a,b in title_rows})==1,'标题不在同一位置，不自动清理'
   canonical=title_rows[0][1]['value'].split(' · 单页结构核对')[0]+' · 单页结构核对 '+c['digest'][:12]
   if record.get('图面差额标记'):canonical+=' · '+record['图面差额标记']
   assert all(b['value'].split(' · 单页结构核对')[0]==canonical.split(' · 单页结构核对')[0] for a,b in title_rows)
   remove_ids={id(a) for a,b in title_rows[1:]}
   title_cleanup=[{'id':a['id'],'原文':b['value']} for a,b in title_rows]
   if title_rows[0][1]['value']!=canonical:title_rows[0][1]['value']=canonical;changes+=1
   if remove_ids:rows=[(a,b) for a,b in rows if id(a) not in remove_ids];changes+=len(remove_ids)
  ticket=max(a.get('ticket',0) for a,b in rows);added=[]
  displayed_nets={v['Name'][1]['value'] for v in props.values()
   if 'Name' in v and 'Device' in v and v['Name'][1].get('valueVisible') is True}
  # Standard conversion leaves a second visible NET caption on the wire
  # under the native net flag/port. Hide only that duplicate presentation,
  # retaining the NET value and the native symbol's readable Name.
  for attrs in props.values():
   if 'Device' not in attrs and 'NET' in attrs:
    _,attribute=attrs['NET']
    if attribute.get('value') in displayed_nets and attribute.get('valueVisible') is True:
     attribute.update(valueVisible=False,keyVisible=False);changes+=1
  for cid,attrs in props.items():
   if c.get('e4_stable') and 'Designator' in attrs:
    ref=attrs['Designator'][1]['value'];part=next((p for p in c['parts'] if p['ref']==ref),None)
    if part and part.get('runtime_assembly_option') and part.get('fitted') is False:
     assert '图面参数' in attrs,ref
     caption=attrs['图面参数'][1];want=str(part['value'])+' · 默认DNP'
     if caption['value']!=want:caption['value']=want;changes+=1
   if not device_names.get(attrs.get('Device',({},{}))[1].get('value',''),'').startswith('Netport-'):continue
   if 'Relevance' in attrs:
    a,b=attrs['Relevance']
    if b.get('valueVisible') is not False:b.update(valueVisible=False,keyVisible=False);changes+=1
   else:
    a,b=copy.deepcopy(attrs['Name']);ticket+=1
    a.update(id=hashlib.sha256((cid+'|single-sheet-relevance').encode()).hexdigest()[:16],ticket=ticket)
    b.update(key='Relevance',value='',valueVisible=False,keyVisible=False);added.append((a,b));changes+=1
  if added or changes:
   preserved=out/schematic.name;write_exclusive(preserved,schematic.read_bytes())
   payload='\n'.join(d.record_json(a)+'||'+d.record_json(b)+'|' for a,b in rows+added)+'\n'
   schematic.write_text(payload,encoding='utf8',newline='\n')
 print(dump({'单页端口引用显示格式修正':changes}),flush=True)
 def invoke(code):return d.cli(EXE,'invoke','--session',session,'--ext-uuid','eda','--timeout','60000','--code',code)['value']
 try:
  session=d.cli(EXE,'open','--path',entry.as_posix(),'--headless','true')['value']['sessionId'];d.wait_for_project(invoke,attempts=90)
  pages=invoke('return await eda.dmt_Schematic.getAllSchematicPagesInfo();');assert len(pages)==1
  page=pages[0]['uuid'];d.open_document(invoke,page)
  changed=changes
  runtime_captions=hide_duplicate_net_captions(invoke,native_duplicate_caption_targets(entry.parent))
  if runtime_captions['hidden']:assert invoke('return await eda.sch_Document.save();') is True
  record['实际公开属性重复NET显示修正']=runtime_captions
  texts=invoke('return (await eda.sch_PrimitiveText.getAll()).map(t=>({id:t.getState_PrimitiveId(),content:t.getState_Content()}));')
  title=next(t for t in texts if '整板原理图' in t['content']);new_title=title['content'].split(' · 单页结构核对')[0]+' · 单页结构核对 '+c['digest'][:12]
  if record.get('图面差额标记'):new_title+=' · '+record['图面差额标记']
  marked=[t for t in texts if t['content']==new_title]
  if c.get('e4_stable'):
   assert len(marked)==1 and len([t for t in texts if '整板原理图' in t['content']])==1,'原生当前标题须唯一'
   assert invoke('return await eda.sch_Document.save();') is True
   edit={'方式':'公开原生显示字段规范化后实际SCH_Document.save；独立关闭重开核验','标题':new_title,'标题旧记录保全':title_cleanup,'图面显示变化数':changes,'没有宣称create/delete已持久化':True}
   d.cli(EXE,'session','close','--session',session,'--destroy');session=None
   reopen_root=new_export_dir(entry.parent.parent,'候选独立重开');reopen_folder=reopen_root/'完整工程'
   original_manifest={p.relative_to(entry.parent).as_posix():sha(p) for p in entry.parent.rglob('*') if p.is_file()}
   shutil.copytree(entry.parent,reopen_folder)
   assert {p.relative_to(reopen_folder).as_posix():sha(p) for p in reopen_folder.rglob('*') if p.is_file()}==original_manifest
   record['实际独立路径重开']={'入口':str((reopen_folder/entry.name).relative_to(ROOT)),'打开前完整目录SHA256':original_manifest,'与已保存原目录逐字节一致':True}
   session=d.cli(EXE,'open','--path',(reopen_folder/entry.name).as_posix(),'--headless','true')['value']['sessionId'];d.wait_for_project(invoke,attempts=90);d.open_document(invoke,page)
  elif recover_existing and marked:
   assert len(marked)==1 and changes==0,'失败候选已改变或持久化标记重复，不能恢复保存证据'
   edit={'恢复方式':'从同一目录独立重开确认先前公开编辑保存的唯一标记；本次不再次改图',
    '目录SHA与前次失败后完全一致':True,'标记':new_title,'前次失败':record['候选验收失败']}
  else:
   edit=d.edit_native_text(invoke,page,title['id'],title['content'],new_title)
   d.cli(EXE,'session','close','--session',session,'--destroy');session=None
   session=d.cli(EXE,'open','--path',entry.as_posix(),'--headless','true')['value']['sessionId'];d.wait_for_project(invoke,attempts=90);d.open_document(invoke,page)
  persisted=new_title in invoke('return (await eda.sch_PrimitiveText.getAll()).map(t=>t.getState_Content());')
  native_record=record['候选完整eprj3目录']
  native_record.setdefault('文件生成时官方状态',{key:native_record.get(key) for key in ('官方保存','关闭独立重开','有效官方网表','ERC通过')})
  native_record.update(官方保存=True,关闭独立重开=bool(persisted))
  record['实际重复NET独立重开核对']=verify_duplicate_net_captions(invoke,runtime_captions['attributes'])
  exported=invoke('const f=await eda.sys_FileManager.getProjectFile("结构候选官方回读",undefined,"epro2");const a=new Uint8Array(await f.arrayBuffer());let s="";for(let i=0;i<a.length;i+=32768)s+=String.fromCharCode(...a.subarray(i,i+32768));return {size:f.size,data:btoa(s)};')
  payload=base64.b64decode(exported['data'],validate=True);assert len(payload)==exported['size']
  path=out/'独立重开官方回读.epro2';write_exclusive(path,payload);check=verify_current_graph(c,inp,path)
  svg=invoke('const f=await eda.sch_ManufactureData.getSvgFile("单页结构修整");return f?await f.text():null;');assert svg and '<svg' in svg
  svgpath,h=save_export_text(out,'结构修整后官方图面.svg',svg)
  old=copy.deepcopy(record);r.setdefault('结构图面候选历史',[]).append(old)
  record.update(官方编辑保存独立重开=persisted,实际编辑=edit,单页隐藏冗余引用数=changed,
   修整工具SHA256=c['tool_sha'],
   官方重开全量逐脚BOM=check,官方重开交换文件=str(path.relative_to(ROOT)),官方重开交换SHA256=sha(path),
   官方SVG=str(svgpath.relative_to(ROOT)),SVG_SHA256=h,视觉验收='待修整后实际渲染检查',整板电气放行=False)
  if recover_existing:record.update(候选验收失败=None,先前完整失败记录已留历史=True)
  print(dump({'板':c.get('physical_board',c['board']),'隐藏引用':changed,'保存重开':persisted,'官方回读器件':check['actual_component_refs'],'官方SVG':str(svgpath)}),flush=True)
  erc=invoke(d.ERC_CODE)
  record.update(官方ERC已执行=True,官方ERC结果=erc,ERC通过=not any(item.get('count',1) for item in erc['summary']),
   有效官方网表=False,封装库SHA256=inp['封装库SHA256'],
   未绑定板上器件=[b['位号'] for b in inp['绑定'] if b['安装'] in ('板上','待设计') and not b['封装']])
  native_record.update(有效官方网表=record['有效官方网表'],ERC通过=record['ERC通过'])
  print(dump({'官方ERC':erc}),flush=True)
  if record['未绑定板上器件']:
   record['官方网表未执行']={'状态':'NOT_RUN_KNOWN_ONBOARD_FOOTPRINT_GAPS',
    '本版缺封装板上位号':record['未绑定板上器件'],
    '原因':'本批仅几何及保存重开；真实板上封装未齐，不重复已知失败导出，不改板上归属以绕过前检。'}
   print(dump(record['官方网表未执行']),flush=True)
   return
  reply=invoke('try{const f=await eda.sch_ManufactureData.getNetlistFile("结构候选官方网表",ESYS_NetlistType.ALTIUM_DESIGNER);return f?{text:await f.text()}:{returnType:typeof f};}catch(e){return {error:String(e)};}')
  if reply.get('text'):
   netpath,netsha=save_export_text(out,'结构候选官方网表.net',reply['text'])
   graph=verify_protel2(reply['text'],inp)
   record.update(官方网表文件=str(netpath.relative_to(ROOT)),官方网表SHA256=netsha,
    官方网表全量核对=graph,有效官方网表=graph['status']=='PASS')
   native_record['有效官方网表']=record['有效官方网表']
  else:record['官方网表失败']=reply
  print(dump({'有效官方网表':record['有效官方网表'],'官方网表失败':record.get('官方网表失败')}),flush=True)
  if not reply.get('text'):
   pcb_reply=invoke('try{const f=await eda.sch_ManufactureData.getNetlistFile("结构候选PCB官方网表",ESYS_NetlistType.JLCEDA_PRO);return f?{text:await f.text()}:{returnType:typeof f};}catch(e){return {error:String(e)};}')
   if pcb_reply.get('text'):
    path,h=save_export_text(out,'结构候选PCB官方网表.enet',pcb_reply['text'])
    graph=verify_jlceda(pcb_reply['text'],inp)
    record['官方PCB网表读取']={'文件':str(path.relative_to(ROOT)),'SHA256':h,'文本长度':len(pcb_reply['text']),'状态':graph['status'],'全量核对':graph}
    record['有效官方网表']=graph['status']=='PASS'
    native_record['有效官方网表']=record['有效官方网表']
   else:record['官方PCB网表读取']={'状态':'FAIL_NO_TEXT','返回':pcb_reply}
   print(dump(record['官方PCB网表读取']),flush=True)
 except Exception as error:
  record.update(候选验收失败=type(error).__name__+': '+str(error),整板电气放行=False)
  raise
 finally:
  if session:d.cli(EXE,'session','close','--session',session,'--destroy')
  final_manifest={p.relative_to(entry.parent).as_posix():sha(p) for p in entry.parent.rglob('*') if p.is_file()}
  native_record=record['候选完整eprj3目录']
  native_record.setdefault('文件生成时完整目录文件SHA256',native_record.get('完整目录文件SHA256',{}))
  native_record['官方保存关闭后完整目录文件SHA256']=final_manifest
  native_record['完整目录文件SHA256']=final_manifest
  record['候选完整目录文件SHA256']=final_manifest
  reopened=record.get('实际独立路径重开')
  if reopened and reopened.get('入口'):
   reopened_entry=ROOT/reopened['入口'];reopened_folder=reopened_entry.parent
   reopened['官方重开关闭后完整目录SHA256']={p.relative_to(reopened_folder).as_posix():sha(p) for p in reopened_folder.rglob('*') if p.is_file()}
  update(c,r)

def record_structured_visual_review(c,notes,status,raster_path=None,render_input_path=None):
 """记录已人工阅读的官方SVG栅格图；静态无重叠不等于视觉合格。"""
 assert status in ('PARTIAL_RENDERED_REVIEW','FAIL_RENDERED_READABILITY','PASS_SCOPED_READABLE_TRACEABLE') and notes
 if status=='PASS_SCOPED_READABLE_TRACEABLE':assert c.get('e4_stable')
 r=validation_result(c);record=r['结构图面候选']
 svg=ROOT/record['官方SVG'];png=Path(raster_path) if raster_path else svg.with_suffix('.png')
 assert sha(svg)==record['SVG_SHA256'] and png.is_file()
 render_source='本版官方SVG原字节栅格化，非重绘或桌面截图'
 derivative=None
 if render_input_path:
  q=Path(render_input_path);assert q.parent.resolve()==svg.parent.resolve()
  text,n=re.subn(r'<rect\b[^>]*fill="url\(#gridPattern\)"[^>]*/>','',svg.read_text(encoding='utf8'))
  assert n==1 and q.read_text(encoding='utf8')==text,'只允许另存移除背景网格的QA输入'
  derivative={'文件':str(q.relative_to(ROOT)),'SHA256':sha(q),'唯一变化':'移除背景gridPattern矩形；器件/文字/导线均保持官方SVG字节'}
  render_source='本版官方SVG另存仅去背景网格后栅格化；原始SVG保留，不重绘器件/文字/导线'
 record.update(视觉验收=status,图面实际阅读核对={
  '实际图面':str(png.relative_to(ROOT)),'实际图面SHA256':sha(png),
  '来源':render_source,'QA渲染输入':derivative,
  '阅读结论及缺口':notes,'静态文字无重叠不作为视觉通过':True,
  '完整图面最终通过':status=='PASS_SCOPED_READABLE_TRACEABLE',
  '通过范围':'实际功能区及主功率链可读可追踪；不代替电气、布板或制造验收',
  '生成器后续修正不自动覆盖此图面证据':True},整板电气放行=False)
 update(c,r)

def compare_official_svg_display(old_path,new_path):
 """Compare actual SVG graphics, retaining both originals and runtime ID changes.

 The client regenerates some symbol-pin text IDs on reopen. Ignore only IDs
 that neither document references; every visible attribute/text stays checked.
 """
 old=Path(old_path).read_text(encoding='utf8');new=Path(new_path).read_text(encoding='utf8')
 aa=list(ET.fromstring(old).iter());bb=list(ET.fromstring(new).iter())
 assert len(aa)==len(bb),'SVG node count changed'
 diffs=[];ids=[]
 for a,b in zip(aa,bb):
  assert (a.tag,a.text,a.tail,len(a))==(b.tag,b.text,b.tail,len(b)),'SVG structure/text changed'
  changes={k:[a.attrib.get(k),b.attrib.get(k)] for k in set(a.attrib)|set(b.attrib) if a.attrib.get(k)!=b.attrib.get(k)}
  if 'id' in changes:
   for value,document in zip(changes.pop('id'),(old,new)):
    assert value and not re.search(r'(?:url\(\s*#|href=["\']#)'+re.escape(value)+r'(?:\s*\)|["\'])',document),'Changed ID is referenced'
    assert not re.search(r'#'+re.escape(value)+r'\s*\{',document),'Changed ID has a CSS selector'
   ids.append([a.attrib.get('id'),b.attrib.get('id')])
  if changes:diffs.append({'id':a.attrib.get('id'),'tag':a.tag,'changes':changes})
 return {'状态':'PASS_DISPLAY_IDENTICAL' if not diffs else 'DISPLAY_DIFFERENCES',
  '旧官方SVG_SHA256':sha(old_path),'新官方SVG_SHA256':sha(new_path),
  '节点数':len(aa),'仅未被引用的运行ID重生数':len(ids),'显示差额':diffs,
  '两份官方原字节未改写':True,'忽略范围':'仅无引用、无CSS选择器的id属性；所有图形/文字/坐标/样式均比较'}

def record_formal_visual_review(c,notes,status):
 """只记录实际正式入口导出的图面，不继承候选图面阅读。"""
 assert status in ('PARTIAL_RENDERED_REVIEW','FAIL_RENDERED_READABILITY') and notes
 r=validation_result(c);formal=r['正式单板原生目录']
 assert formal['对应源文件SHA256']==c['hashes'] and formal['实际入口独立重开']
 entry=ROOT/formal['入口'];folder=entry.parent
 manifest={p.relative_to(folder).as_posix():sha(p) for p in folder.rglob('*') if p.is_file()}
 assert manifest==formal['正式入口重开后目录SHA256'],'正式目录改变，不沿用图面'
 svg=ROOT/formal['官方SVG'];png=svg.with_suffix('.png')
 assert sha(svg)==formal['SVG_SHA256'] and png.is_file()
 formal.update(图面视觉验收=status,实际正式图面阅读={
  '正式入口':formal['入口'],'正式目录SHA256':manifest,
  '官方SVG':formal['官方SVG'],'SVG_SHA256':formal['SVG_SHA256'],
  '实际图面':str(png.relative_to(ROOT)),'实际图面SHA256':sha(png),
  '来源':'本版正式入口官方SVG原字节栅格化，非候选图面、重绘或桌面截图',
  '阅读结论及缺口':notes,'完整图面最终通过':False,
  '仅阅读总览不等于全部文字及逐区连线验收':True},整板放行=False)
 update(c,r)

def verify_structured_electrical(c):
 """在已保存且精确匹配的结构工程上读取ERC明细与官方网表，不再改图。"""
 c=dict(c,preview_only=True);r=validation_result(c);record=r['结构图面候选']
 assert record['板源文件SHA256']==c['hashes'] and record['页数']==1
 entry=ROOT/record['候选完整eprj3目录']['工程索引']
 assert {p.relative_to(entry.parent).as_posix():sha(p) for p in entry.parent.rglob('*') if p.is_file()}==record['候选完整目录文件SHA256']
 inp=read(candidate_path(c).parent/'结构预览输入.json')
 assert inp['板源文件SHA256']==c['hashes'] and inp['封装库SHA256']==sha(LIB/'可导入封装库.zip')
 out=new_export_dir(entry.parent.parent,'结构电气差额回读')
 d=module('原理图交付');session=None
 assert not [s for s in d.cli(EXE,'session','list')['value'] if s.get('status') not in ('closed','destroyed')]
 r.setdefault('结构图面候选历史',[]).append(copy.deepcopy(record))
 def invoke(code):return d.cli(EXE,'invoke','--session',session,'--ext-uuid','eda','--timeout','60000','--code',code)['value']
 try:
  session=d.cli(EXE,'open','--path',entry.as_posix(),'--headless','true')['value']['sessionId'];d.wait_for_project(invoke)
  pages=invoke('return await eda.dmt_Schematic.getAllSchematicPagesInfo();');assert len(pages)==1
  d.open_document(invoke,pages[0]['uuid'])
  if not record.get('官方重开交换文件'):
   marker=' · 单页结构核对 '+c['digest'][:12]
   titles=invoke('return (await eda.sch_PrimitiveText.getAll()).map(t=>t.getState_Content());')
   assert sum(marker in title for title in titles)==1,'先前公开编辑未实际落盘，不能恢复为保存通过'
   exported=invoke('const f=await eda.sys_FileManager.getProjectFile("恢复独立重开回读",undefined,"epro2");const a=new Uint8Array(await f.arrayBuffer());let s="";for(let i=0;i<a.length;i+=32768)s+=String.fromCharCode(...a.subarray(i,i+32768));return {size:f.size,data:btoa(s)};')
   payload=base64.b64decode(exported['data'],validate=True);assert len(payload)==exported['size']
   path=out/'恢复独立重开官方回读.epro2';write_exclusive(path,payload)
   check=verify_current_graph(c,inp,path)
   record.update(官方编辑保存独立重开=True,官方重开全量逐脚BOM=check,
    官方重开交换文件=str(path.relative_to(ROOT)),官方重开交换SHA256=sha(path),
    保存恢复说明='首次公开create/delete/save后第二次挂载未就绪，当前从同一目录独立重开确认唯一持久化编辑及全量引脚/BOM/NPTH；未再次改图')
   print(dump({'保存独立重开恢复':True,'元件':check['actual_component_refs']}),flush=True)
  erc=invoke(d.ERC_CODE);record.update(官方ERC结果=erc,官方ERC已执行=True,ERC通过=not any(item.get('count',1) for item in erc['summary']),有效官方网表=False)
  print(dump(erc),flush=True)
  reply=invoke('try{const f=await eda.sch_ManufactureData.getNetlistFile("结构候选官方网表",ESYS_NetlistType.ALTIUM_DESIGNER);return f?{text:await f.text()}:{returnType:typeof f};}catch(e){return {error:String(e)};}')
  if reply.get('text'):
   netpath,netsha=save_export_text(out,'结构候选官方网表.net',reply['text']);graph=verify_protel2(reply['text'],inp)
   record.update(官方网表文件=str(netpath.relative_to(ROOT)),官方网表SHA256=netsha,官方网表全量核对=graph,有效官方网表=graph['status']=='PASS')
  else:record['官方网表失败']=reply
  if not reply.get('text'):
   pcb_reply=invoke('try{const f=await eda.sch_ManufactureData.getNetlistFile("结构候选PCB官方网表",ESYS_NetlistType.JLCEDA_PRO);return f?{text:await f.text()}:{returnType:typeof f};}catch(e){return {error:String(e)};}')
   if pcb_reply.get('text'):
    path,h=save_export_text(out,'结构候选PCB官方网表.enet',pcb_reply['text'])
    graph=verify_jlceda(pcb_reply['text'],inp)
    record['官方PCB网表读取']={'文件':str(path.relative_to(ROOT)),'SHA256':h,'文本长度':len(pcb_reply['text']),'状态':graph['status'],'全量核对':graph}
    record['有效官方网表']=graph['status']=='PASS'
   else:record['官方PCB网表读取']={'状态':'FAIL_NO_TEXT','返回':pcb_reply}
   print(dump(record['官方PCB网表读取']),flush=True)
  print(dump({'有效官方网表':record['有效官方网表'],'官方网表失败':record.get('官方网表失败')}),flush=True)
 finally:
  if session:d.cli(EXE,'session','close','--session',session,'--destroy')
  record['候选完整目录文件SHA256']={p.relative_to(entry.parent).as_posix():sha(p) for p in entry.parent.rglob('*') if p.is_file()}
  update(c,r)

def restore_component_captions(exchange,sheets):
 """Restore planned visible captions lost by the standard-to-Pro converter.

 Only instance display attributes change; complete BOM/Name/Value remain intact.
 """
 planned={}
 for sheet in sheets:
  for shape in sheet['shape']:
   if not shape.startswith('LIB~'):continue
   texts={q.split('~')[1]:q.split('~') for q in shape.split('#@$')[1:] if q.startswith(('T~P~','T~N~'))}
   assert set(texts)=={'P','N'}
   planned[texts['P'][12]]=texts
 d=module('原理图交付')
 with zipfile.ZipFile(exchange) as z:entries={n:z.read(n) for n in z.namelist()}
 covered=set()
 for name,payload in list(entries.items()):
  if not name.endswith('.epru'):continue
  rows=[(a,b) for _,(a,b) in d.records(payload.decode('utf8'))];kind=None;attrs={};page=0
  for a,b in rows:
   if a['type']=='DOCHEAD':kind=b['docType'];page+=1
   if kind=='SCH_PAGE' and a['type']=='ATTR':attrs.setdefault((page,b['parentId']),{})[b['key']]=(a,b)
  additions=[];ticket=max(a.get('ticket',0) for a,b in rows)
  # Insert the parameter attribute next to its owner, not at the end of another document.
  for props in attrs.values():
   if 'Designator' not in props:continue
   ref=props['Designator'][1]['value'];assert ref in planned and ref not in covered
   covered.add(ref)
   for typ,key in [('P','Designator'),('N','图面参数')]:
    t=planned[ref][typ]
    if key in props:a,b=props[key]
    else:
     a,b=copy.deepcopy(props['Designator']);ticket+=1
     a.update(id=a['id']+'_caption',ticket=ticket);b.update(key=key,value=t[12])
     additions.append(((props['Designator'][0]['id'],ref),(a,b)))
    b.update(x=float(t[2]),y=float(t[3]),rotation=0,keyVisible=False,valueVisible=True,
     fontSize=float(t[7].replace('pt',''))*100/72,fontFamily='Arial',
     align='RIGHT_BOTTOM' if t[14]=='end' else 'LEFT_BOTTOM')
  extra=dict(additions);output=[]
  for a,b in rows:
   output.append(d.record_json(a)+'||'+d.record_json(b)+'|')
   if a['type']=='ATTR' and b.get('key')=='Designator' and (a.get('id'),b.get('value')) in extra:
    aa,bb=extra[(a['id'],b['value'])];output.append(d.record_json(aa)+'||'+d.record_json(bb)+'|')
  entries[name]=('\n'.join(output)+'\n').encode('utf8')
 assert covered==set(planned),(covered^set(planned))
 with zipfile.ZipFile(exchange,'w',zipfile.ZIP_DEFLATED) as z:
  for n,b in entries.items():z.writestr(n,b)
 return {'位号可见':len(covered),'参数可见':len(covered),'BOM及电气连接修改':False}


def sqlite_official(c):
 """串行使用官方SQLite原生格式；异常和未通过的门如实写入已有核验。"""
 d=module('原理图交付');inp=read(packet(c));d.CACHE=new_export_dir(Path(inp.get('构建目录',CACHE/c['board'])),'官方原生校验');result=validation_result(c)
 result['官方编辑保存独立重开']=False
 assert inp['源SHA256']==c['digest'] and result['板源文件SHA256']==c['hashes'], '集成输入不是当前冻结源'
 assert sha(inp['交换文件'])==inp['交换SHA256'], '交换输入发生变化'
 assert not [s for s in d.cli(EXE,'session','list')['value'] if s.get('status') not in ('closed','destroyed')], '官方会话必须串行'
 native_plans,anchor_changes=d.resolve_standard_port_plans(inp['交换文件'],inp['标准端口计划'])
 inp.update(原生端口计划=native_plans,原生同网导线端点锚点调整=anchor_changes);write(packet(c),inp)
 # 不从目录枚举挑选历史工程；只复用本次输入明确记录并校验的构建。
 candidate=inp.get('原生构建文件');works=[]
 if candidate and Path(candidate).exists() and sha(candidate)==inp.get('原生构建SHA256'):
  works=[Path(candidate)]
 session=None;sessions=[];phase='SQLite_open'
 def invoke(code):return d.cli(EXE,'invoke','--session',session,'--ext-uuid','eda','--timeout','60000','--code',code)['value']
 def exported(path):
  r=invoke('const f=await eda.sys_FileManager.getProjectFile("原生回读",undefined,"epro2");const a=new Uint8Array(await f.arrayBuffer());let s="";for(let i=0;i<a.length;i+=32768)s+=String.fromCharCode(...a.subarray(i,i+32768));return {size:f.size,data:btoa(s)};')
  b=base64.b64decode(r['data'],validate=True);assert len(b)==r['size'];path.write_bytes(b)
 def verify(path):
  ps=copy.deepcopy(c['parts']);bindings={b['位号']:b for b in inp['绑定']}
  for p in ps:
   p['model']=p['mpn'];p.pop('approved_binding',None);p.pop('mechanical_candidate',None);b=bindings[p['ref']]
   if b.get('库文件'):p['approved_binding']={'footprint':b['封装'],'member':b['库文件'],'sha256':b['封装SHA256'],'physical_pin_to_pad':b['引脚映射']}
  return module('核验交换原理图').verify_exchange(path,{(r,p):n for r,p,n in inp['预期网络']},
   {tuple(x) for x in inp['NC']},parts=ps,hardware=HW,cap_specs=c['data'].get('CAP_SPECS'),strict_full_BOM=True)
 try:
  if not works:
   prepared=d.CACHE/'SQLite输入.epro2';shutil.copy2(inp['交换文件'],prepared);d.insert_standard_ports(prepared,native_plans)
   w,_=d.native_import(EXE,prepared,expected_refs=[p['ref'] for p in c['parts']],
    parking_title=inp.get('首页',c['parts'][0]['page']),project_name=c['name'],cache_dir=d.CACHE,template_path=CACHE/'空工程模板.eprj2',default_page_title=inp.get('首页',c['parts'][0]['page']))
   works=[w]
   inp.update(原生构建文件=str(w),原生构建SHA256=sha(w));write(packet(c),inp)
  work=Path(tempfile.mkdtemp(prefix='SQLite编辑-',dir=d.CACHE))/(c['name']+'.eprj2');d.sqlite_copy(works[-1],work)
  session=d.cli(EXE,'open','--path',work.as_posix(),'--headless','true')['value']['sessionId'];sessions.append(session);d.wait_for_project(invoke)
  pages=invoke('return await eda.dmt_Schematic.getAllSchematicPagesInfo();');assert len(pages)==inp['页数']
  result['官方导入']=True
  first=next(p['uuid'] for p in pages if p['name']==inp.get('首页',c['parts'][0]['page']));phase='SQLite_port_and_placement'
  allrefs=[];moved=0
  for i,page in enumerate(pages):
   external=[p['ref'] for p in c['parts'] if inp.get('位号图页',{}).get(p['ref'],p['page'])==page['name'] and not p['onboard']]
   plan=native_plans[page['name']]
   planpath=d.CACHE/'当前图页端口计划.json';write(planpath,plan)
   code='''const expected=JSON.parse(await (await eda.sys_FileSystem.readFileFromFileSystem('''+json.dumps(planpath.as_posix())+''')).text());const ports=[...(await eda.sch_PrimitiveComponent.getAll("netport")),...(await eda.sch_PrimitiveComponent.getAll("netflag"))];
if(ports.length!==expected.length)throw new Error("端口计数不符");let moved=0;
const match=(x,y,net)=>expected.some(p=>p.net===net&&Math.abs(p.x-x)<0.00001&&Math.abs(p.y+y)<0.00001);
const misplaced=[];for(const p of ports){const x=p.getState_X(),y=p.getState_Y(),net=p.getState_Net();
if(match(x,y,net))continue;if(!match(x/10,y/10,net))throw new Error("端口不能对应本版计划:"+net);misplaced.push(p);}
// 新版通用modify不支持网络端口；删除误置重复端口，保留原实际导线及完整NET标签。
if(misplaced.length){if(await eda.sch_PrimitiveComponent.delete(misplaced)!==true)throw new Error("误置端口删除失败");moved=misplaced.length;}
const external=new Set('''+json.dumps(external)+''');const parts=await eda.sch_PrimitiveComponent.getAll("part");
for(const p of parts)if(external.has(p.getState_Designator()))await eda.sch_PrimitiveComponent.modify(p,{addIntoPcb:false,otherProperty:p.getState_OtherProperty()});
if(await eda.sch_Document.save()!==true)throw new Error("页保存失败");
return {refs:parts.map(p=>p.getState_Designator()),moved};'''
   r=d.invoke_on_page(invoke,page['uuid'],first,code);allrefs.extend(r['refs']);moved+=r['moved']
   if (i+1)%8==0:print('SQLite本版页保存',i+1,'/',len(pages),flush=True)
  assert set(allrefs)=={p['ref'] for p in c['parts']} and len(allrefs)==len(c['parts'])
  d.open_document(invoke,first);texts=invoke('return (await eda.sch_PrimitiveText.getAll()).map(t=>({id:t.getState_PrimitiveId(),content:t.getState_Content()}));')
  title=inp.get('首页','同版原理图');alternates={title,re.sub(r'-\d+-整板原理图$',' · 整板原理图',title)}
  candidates=[t for t in texts if any(s in t['content'] for s in alternates)]
  assert len(candidates)==1,('保存探针标题必须唯一',title,candidates)
  t=candidates[0];newtext=t['content']+'；SQLite同版保存 '+c['digest'][:12]
  edit=d.edit_native_text(invoke,first,t['id'],t['content'],newtext)
  d.time.sleep(8)
  exported(d.CACHE/'SQLite保存回读.epro2');before=verify(d.CACHE/'SQLite保存回读.epro2')
  d.cli(EXE,'session','close','--session',session,'--destroy');sessions.remove(session);session=None
  phase='SQLite_independent_reopen';reopen=Path(tempfile.mkdtemp(prefix='SQLite独立重开-',dir=d.CACHE))/work.name;d.sqlite_copy(work,reopen)
  session=d.cli(EXE,'open','--path',reopen.as_posix(),'--headless','true')['value']['sessionId'];sessions.append(session);d.wait_for_project(invoke);d.open_document(invoke,first)
  texts=invoke('return (await eda.sch_PrimitiveText.getAll()).map(t=>t.getState_Content());');assert newtext in texts
  exported(d.CACHE/'SQLite独立重开回读.epro2');after=verify(d.CACHE/'SQLite独立重开回读.epro2')
  assert after['actual_component_refs']==len(c['parts']) and after['connected_pins']==before['connected_pins']
  result.update(官方导入=True,官方编辑保存独立重开=True,原生格式='官方SQLite eprj2',
   官方持久化编辑=edit,原生误置重复端口删除数=moved,原生端口同网端点调整=anchor_changes,原生网络表达='局部实体导线；端口锚点按同网短线端点调整的实际计划核对',官方保存后交换逐脚回读=before,官方独立重开交换逐脚回读=after)
  print('SQLite官方编辑保存独立重开及逐脚/BOM回读通过',c['board'],flush=True)
  if len(pages)==1:
   preview=invoke('const f=await eda.sch_ManufactureData.getSvgFile("单板原生图面");return f?{text:await f.text(),mime:f.type}:null;')
   if preview and '<svg' in preview.get('text',''):
    preview_path,preview_sha=save_export_text(d.CACHE,'单板原生图面.svg',preview['text'])
    result['单板图面核验']={'官方SVG':str(preview_path.relative_to(ROOT)),'SVG_SHA256':preview_sha,
     '源SHA256':c['digest'],'图页':pages[0]['name'],'页数':1,'视觉验收':'待实际渲染检查；单页及逐脚通过不代表结构可读'}
  phase='SQLite_ERC_netlist';erc=invoke(d.ERC_CODE);result.update(官方ERC已执行=True,官方ERC结果=erc,ERC通过=not any(r['count'] for r in erc['summary']))
  raw=invoke('const f=await eda.sch_ManufactureData.getNetlistFile("客户端网表","JLCEDA");return f?{data:await f.text()}:null;')
  if raw and raw.get('data'):
   path,file_sha=save_export_text(d.CACHE,'官方网表.json',raw['data'])
   result.update(有效官方网表=False,官方网表文件=str(path.relative_to(ROOT)),官方网表SHA256=file_sha,当前网表阻塞='JLCEDA返回文本，尚未完成全量独立拓扑核对；不能仅凭非空文件放行。')
  else:
   result['有效官方网表']=False
   result['官方导出实现核对']=official_export_implementation()
   result['当前网表阻塞']='JLCEDA未返回File；客户端导出前检遇致命错误会跳过输出回调，本版ERC有无致命错误见完整结果。先修实际缺陷，未绕过规则，未用源自导网表替代。'
  update(c,result)
  for owned in reversed(sessions):d.cli(EXE,'session','close','--session',owned,'--destroy')
  sessions=[];session=None
  target=c['target']/(c['name']+'.eprj2');d.sqlite_copy(reopen,target)
  # SQLite is a verified intermediate, not a reason to remove folder projects.
  # Human-facing eprj3 delivery is produced and independently checked below.
  result.update(原生工程=str(target.relative_to(c['base'])),原生工程SHA256=sha(target),原生工程状态='SQLite同版逐脚/BOM及官方编辑保存独立重开通过；ERC/制造网表仍按缺口记录')
  # 现代交换工程为必要导出，全部来自独立重开的官方实际文件。
  exchange=c['exchange_target'] if c.get('exchange_target') else c['base']/({'配电':'导出/系统辅助板候选.epro2','FOC':'导出/电机驱动原理图.epro2'}[c['board']]);exchange.parent.mkdir(parents=True,exist_ok=True)
  shutil.copy2(d.CACHE/'SQLite独立重开回读.epro2',exchange);result['官方同版交换导出']=artifact_relative_path(exchange,c['base']);result['官方同版交换SHA256']=sha(exchange)
  update(c,result);print('原生交付',target,'ERC',erc['summary'],flush=True)
 except Exception as e:
  result.setdefault('官方失败',[]).append({'阶段':phase,'错误':type(e).__name__+': '+str(e)[:6000],
   '调用栈':traceback.format_exc()[-5000:],
   '客户端版本':'4.1.60.198f38ab','工具SHA256':c['tool_sha'],'输入源SHA256':c['digest']});update(c,result);print('SQLite失败',phase,type(e).__name__,str(e)[:2400],flush=True)
 finally:
  for owned in reversed(sessions):
   try:d.cli(EXE,'session','close','--session',owned,'--destroy')
   except Exception as e:print('关闭SQLite会话失败',str(e)[:400])
 return result

def normalize_folder_default(index_path, first_title):
 """Repair only the stale imported default UUID in official folder metadata."""
 d=module('原理图交付');index=read(index_path);before=sha(index_path)
 pages=[v['uuid'] for v in index['profile']['sheets'].values() if v['title']==first_title]
 assert len(pages)==1,('本版默认图页须唯一',first_title)
 first=pages[0];old=index.get('default_sheet');index['default_sheet']=first
 assert isinstance(index['config'],str),'官方CONFIG格式变化，停止猜测'
 rows=[];kind=None;defaults=[]
 for _,(a,b) in d.records(index['config']):
  if a['type']=='DOCHEAD':kind=b['docType']
  elif a['type']=='META' and kind=='CONFIG':defaults.append(b.get('defaultSheet'));b['defaultSheet']=first
  rows.append(d.record_json(a)+'||'+d.record_json(b)+'|')
 assert len(defaults)==1,'官方CONFIG须有唯一默认页记录'
 index['config']='\n'.join(rows)+'\n';write(index_path,index)
 return {'索引SHA256_前':before,'索引SHA256_后':sha(index_path),'索引默认页_前':old,
  'CONFIG默认页_前':defaults[0],'统一默认页_后':first,
  '修改范围':'仅官方另存索引默认页与CONFIG默认页对应真实当前UUID、记录分隔符；不修改电气图页/库/规则'}

def folder_official(c):
 """Official folder save-as, closed-session reopen and full graph/ERC readback."""
 d=module('原理图交付');inp=read(packet(c));result=validation_result(c)
 assert result.get('官方编辑保存独立重开'), '先取得同版SQLite实际编辑保存回读'
 origin=c['base']/result['原生工程'];origin_sha=sha(origin)
 assert origin_sha==result['原生工程SHA256']
 assert not [s for s in d.cli(EXE,'session','list')['value'] if s.get('status') not in ('closed','destroyed')]
 out=new_export_dir(CACHE/c['board'],'eprj3');folder=out/c['name'];session=None
 evidence={'板源文件SHA256':c['hashes'],'源SHA256':c['digest'],'工具SHA256':c['tool_sha'],
  '输入中间件SHA256':origin_sha,'当前电气源适用':not c.get('frozen',False),
  '官方另存':False,'关闭独立重开':False,'有效官方网表':False,'ERC通过':False}
 def invoke(code):return d.cli(EXE,'invoke','--session',session,'--ext-uuid','eda','--timeout','60000','--code',code)['value']
 try:
  clone=out/'另存输入.eprj2';d.sqlite_copy(origin,clone)
  session=d.cli(EXE,'open','--path',clone.as_posix(),'--headless','true')['value']['sessionId'];d.wait_for_project(invoke)
  pages=invoke('return await eda.dmt_Schematic.getAllSchematicPagesInfo();')
  first=next(p['uuid'] for p in pages if p['name']==inp['首页']);d.open_document(invoke,first)
  assert invoke('return await eda.sch_Document.save();') is True
  saved=invoke('const v=globalThis.gVars;return (await v.messageBus.rpcCall("/pro-mgr/projectAsCloud",{uuid:v.currentProject.projectId,info:{name:'+json.dumps(folder.name)+',path:'+json.dumps(folder.parent.as_posix())+',isFolder:true,owner:{uuid:v.loginedUserInfo.uuid},introduction:"",description:"",cbb_project:false},options:{needDlg:false,autoOpen:false,needTip:false},progressOptions:{needProgress:false}})).message;')
  assert saved and saved.get('success'),('官方文件夹另存失败',saved)
  d.cli(EXE,'session','close','--session',session,'--destroy');session=None
  index=folder/(c['name']+'.eprj3')
  evidence.update(官方另存=True,另存返回=saved,默认页同步=normalize_folder_default(index,inp['首页']),
   工程索引=str(index.relative_to(ROOT)),磁盘结构=d.project_documents(index))
  session=d.cli(EXE,'open','--path',index.as_posix(),'--headless','true')['value']['sessionId'];d.wait_for_project(invoke)
  pages=invoke('return await eda.dmt_Schematic.getAllSchematicPagesInfo();')
  assert len(pages)==inp['页数'] and {p['name'] for p in pages}==set(inp['标准端口计划'])
  first=next(p['uuid'] for p in pages if p['name']==inp['首页']);d.open_document(invoke,first)
  texts=invoke('return (await eda.sch_PrimitiveText.getAll()).map(t=>t.getState_Content());')
  assert any('SQLite同版保存 '+c['digest'][:12] in t for t in texts),'官方另存未保留已验证编辑'
  raw=invoke('const f=await eda.sys_FileManager.getProjectFile("文件夹重开回读",undefined,"epro2");const a=new Uint8Array(await f.arrayBuffer());let s="";for(let i=0;i<a.length;i+=32768)s+=String.fromCharCode(...a.subarray(i,i+32768));return {size:f.size,data:btoa(s)};')
  payload=base64.b64decode(raw['data'],validate=True);assert len(payload)==raw['size']
  export=out/'文件夹独立重开回读.epro2';write_exclusive(export,payload)
  evidence.update(关闭独立重开=True,逐脚及BOM回读=verify_current_graph(c,inp,export),
   实际官方交换文件=str(export.relative_to(ROOT)),实际官方交换SHA256=sha(export))
  erc=invoke(d.ERC_CODE);evidence.update(官方ERC结果=erc,ERC通过=not any(r['count'] for r in erc['summary']))
  reply=invoke('try{const f=await eda.sch_ManufactureData.getNetlistFile("官方网表","Protel2");return f?{text:await f.text()}:{returnType:typeof f};}catch(e){return {error:String(e)};}')
  if isinstance(reply.get('text'),str) and reply['text'].strip():
   netpath,netsha=save_export_text(out,'官方网表.net',reply['text'])
   evidence.update(官方网表文件=str(netpath.relative_to(ROOT)),官方网表SHA256=netsha)
   check=verify_protel2(reply['text'],inp)
   evidence.update(官方网表文件=str(netpath.relative_to(ROOT)),官方网表SHA256=netsha,官方网表全量核对=check,有效官方网表=check['status']=='PASS')
  else:evidence['官方网表失败']=reply
 except Exception as e:
  evidence['失败']=type(e).__name__+': '+str(e)[:4000]
  evidence['调用栈']=traceback.format_exc()[-5000:]
 finally:
  if session:
   try:d.cli(EXE,'session','close','--session',session,'--destroy')
   except Exception as e:evidence['关闭失败']=str(e)[:1000]
  evidence['输入中间件未变']=sha(origin)==origin_sha
  if folder.is_dir():
   evidence['完整目录文件SHA256']={p.relative_to(folder).as_posix():sha(p) for p in sorted(folder.rglob('*')) if p.is_file()}
  prior=result.get('官方文件夹工程')
  if prior:result.setdefault('官方文件夹工程历史',[]).append(prior)
  result['官方文件夹工程']=evidence;update(c,result)
 print(dump({k:evidence.get(k) for k in ('工程索引','官方另存','关闭独立重开','有效官方网表','ERC通过','失败')}),flush=True)
 return evidence

def diagnose_folder_save(c):
 """在完整隔离副本创建文本，以公开保存及日志API取得明确失败原因。"""
 result=validation_result(c);formal=result['正式单板原生目录'];d=module('原理图交付')
 index=ROOT/formal['入口']
 assert not [s for s in d.cli(EXE,'session','list')['value'] if s.get('status') not in ('closed','destroyed')]
 out=new_export_dir(CACHE/c['board'],'保存校验');clone=out/'完整工程';shutil.copytree(index.parent,clone)
 session=None;e={'实际入口':formal['入口'],'隔离副本':str((clone/index.name).relative_to(ROOT)),
  '源文件SHA256':c['hashes'],'工具SHA256':sha(__file__),'公开API创建文本':False,'公开API保存返回':None}
 def invoke(code):return d.cli(EXE,'invoke','--session',session,'--ext-uuid','eda','--timeout','60000','--code',code)['value']
 try:
  session=d.cli(EXE,'open','--path',(clone/index.name).as_posix(),'--headless','true')['value']['sessionId'];d.wait_for_project(invoke)
  pages=invoke('return await eda.dmt_Schematic.getAllSchematicPagesInfo();');assert len(pages)==1;d.open_document(invoke,pages[0]['uuid'])
  marker='eprj3公开保存验证 '+c['digest'][:12]
  response=invoke('const t=await eda.sch_PrimitiveText.create(0,0,'+json.dumps(marker)+');const saved=await eda.sch_Document.save();return {created:!!t,id:t?.getState_PrimitiveId(),saved,logs:await eda.sys_Log.sort()};')
  e.update(公开API创建文本=response['created'],文本ID=response.get('id'),公开API保存返回=response['saved'],官方日志=response['logs'])
  print(dump({'公开API创建文本':e['公开API创建文本'],'公开API保存返回':e['公开API保存返回'],
   '日志条目':len(e['官方日志']),'错误摘要':[{'type':v['type'],'message':v['message'][:220]} for v in e['官方日志'] if v['type'] in ('error','fatalError')]}),flush=True)
 except Exception as error:e.update(错误=str(error)[:4000],调用栈=traceback.format_exc()[-3000:]);print(str(error)[:2000],flush=True)
 finally:
  if session:d.cli(EXE,'session','close','--session',session,'--destroy')
  e['副本完整文件SHA256']={p.relative_to(clone).as_posix():sha(p) for p in clone.rglob('*') if p.is_file()}
  result.setdefault('保存根因核查',[]).append(e);update(c,result)


def repair_folder_references(c):
 """修正DEVICE内编码JSON的SymbolName/FootprintName引用，不改电路或删图元。"""
 result=validation_result(c);formal=result['正式单板原生目录'];d=module('原理图交付');index=ROOT/formal['入口']
 assert not [s for s in d.cli(EXE,'session','list')['value'] if s.get('status') not in ('closed','destroyed')]
 original_manifest={p.relative_to(index.parent).as_posix():sha(p) for p in index.parent.rglob('*') if p.is_file()}
 assert original_manifest==formal.get('完整目录文件SHA256',result['官方文件夹工程']['完整目录文件SHA256'])
 history=new_export_dir(CACHE/c['board'],'引用修正前');shutil.copytree(index.parent,history/'完整工程')
 result.setdefault('原生格式修正历史',[]).append({'原生工程':str((history/'完整工程'/index.name).relative_to(ROOT)),
  '完整文件SHA256':original_manifest,'正式单板原生目录':copy.deepcopy(formal),'官方文件夹工程':copy.deepcopy(result['官方文件夹工程'])})
 changes=[]
 for path in index.parent.rglob('*.esch2'):
  rows=[r for _,r in d.records(path.read_text(encoding='utf8'))];kind='';uid=''
  for a,b in rows:
   if a['type']=='DOCHEAD':kind=b['docType'];uid=b['uuid']
   if kind!='DEVICE' or a['type']!='META':continue
   attrs=b.get('attributes',{})
   for key in ('Symbol','Footprint'):
    encoded=attrs.get(key+'Name');target=attrs.get(key)
    if not isinstance(encoded,str) or not encoded.startswith('{') or not target:continue
    v=json.loads(encoded)
    if v.get('uuid')!=target:
     changes.append({'device':uid,'title':b.get('title'),'field':key+'Name','before':v.get('uuid'),'after':target})
     v['uuid']=target;attrs[key+'Name']=json.dumps(v,ensure_ascii=False,separators=(',',':'))
  if changes:path.write_text('\n'.join(d.record_json(a)+'||'+d.record_json(b)+'|' for a,b in rows)+'\n',encoding='utf8',newline='\n')
 assert changes,'没有发现引用缺陷，停止无变化修复'
 e=result['官方文件夹工程'];e.update(官方保存=False,关闭独立重开=False)
 e['库引用修正']={'变化':changes,'工具SHA256':sha(__file__),'依据':'公开SYS_Log显示五种特殊器件DEVICE.SymbolName引用缺失；目标取同一DEVICE已有有效Symbol UUID'}
 e['完整目录文件SHA256']={p.relative_to(index.parent).as_posix():sha(p) for p in index.parent.rglob('*') if p.is_file()}
 formal.update(完整目录文件SHA256=e['完整目录文件SHA256'],正式入口重开后目录SHA256=e['完整目录文件SHA256'],实际入口独立重开=False,
  范围='修正特殊器件库引用后待官方编辑保存及同版重开，不继承修正前PASS')
 result.update(官方编辑保存独立重开=False,官方独立重开交换逐脚回读=None)
 update(c,result);print(dump({'板':c.get('physical_board',c['board']),'修正引用':changes}),flush=True)


def intro_lock_template():
 """官方eprj3-intro.md锁载体：按实际存在的副本解析，不硬编码已被移动的旧路径。

 4.1.60服务端日志以该官方说明文件作为文件夹锁载体。交付重组后
 原生工程/<板>/eprj3-intro.md 已被移入 <板>/E4-2026100602-<digest12>/ 内，
 旧硬编码路径直接FileNotFoundError。这里优先旧路径（若仍在），否则在原生工程树内
 查找，并要求所有候选副本逐字节相同；全部缺失时明确失败，不伪造内容、不绕过锁。
 """
 direct=HW/'FOC驱动与储能/原生工程/辅助电源板/eprj3-intro.md'
 if direct.is_file():return direct
 found=sorted(p for p in (HW/'FOC驱动与储能/原生工程').rglob('eprj3-intro.md') if p.is_file())
 assert found,('缺少官方eprj3-intro.md锁载体，无法生成文件夹工程',
  str(HW/'FOC驱动与储能/原生工程'))
 blobs={p.read_bytes() for p in found}
 assert len(blobs)==1,('多份eprj3-intro.md内容不一致，须人工确认锁载体',
  [str(p.relative_to(HW)) for p in found])
 return found[0]

def direct_folder(c):
 """按官方Workflow B生成单板完整目录；不经过SQLite/逐根导线重写。"""
 d=module('原理图交付');inp=c.get('preview_input') or read(packet(c));result=validation_result(c)
 original=Path(inp['交换文件']);assert sha(original)==inp['交换SHA256']
 assert inp['页数']==1
 verify_current_graph(c,inp,original)
 out=new_export_dir(Path(inp['构建目录']),'直接文件夹')
 prepared=out/'标准端口输入.epro2';shutil.copy2(original,prepared)
 plans,changes=d.resolve_standard_port_plans(prepared,inp['标准端口计划']);d.insert_standard_ports(prepared,plans)
 with zipfile.ZipFile(prepared) as z:
  text=z.read(next(n for n in z.namelist() if n.endswith('.epru'))).decode('utf8')
 docs=[]
 for _,row in d.records(text):
  if row[0]['type']=='DOCHEAD':docs.append([])
  docs[-1].append(row)
 kind=lambda doc:doc[0][1]['docType']
 meta=lambda doc:next(b for a,b in doc if a['type']=='META')
 # 基于实际库内容重新寻址；不得命中旧版同UUID的库缓存。
 aliases={}
 def mapped(v):
  if isinstance(v,str):
   if v in aliases:return aliases[v]
   if v.startswith(('{','[')):
    try:
     parsed=json.loads(v)
     if isinstance(parsed,(dict,list)):return json.dumps(mapped(parsed),ensure_ascii=False,separators=(',',':'))
    except json.JSONDecodeError:pass
   return v
  if isinstance(v,list):return [mapped(x) for x in v]
  if isinstance(v,dict):return {aliases.get(k,k):mapped(x) for k,x in v.items()}
  return v
 for kinds in (('FOOTPRINT','FONT'),('SYMBOL',),('DEVICE',)):
  for doc in docs:
   if kind(doc) in kinds:
    content=[(a['type'],a.get('id',''),mapped({k:v for k,v in b.items() if k!='uuid'} if a['type']=='DOCHEAD' else b)) for a,b in doc]
    aliases[doc[0][1]['uuid']]=hashlib.sha256(json.dumps(content,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()[:16]
 for doc in docs:
  if kind(doc) in ('BOARD','SCH','SCH_PAGE'):
   aliases[doc[0][1]['uuid']]=hashlib.sha256((sha(prepared)+'|folder|'+kind(doc)).encode()).hexdigest()[:16]
 docs=[[(mapped(a),mapped(b)) for a,b in doc] for doc in docs]
 board,sch,page=[next(doc for doc in docs if kind(doc)==k) for k in ('BOARD','SCH','SCH_PAGE')]
 assert sum(kind(doc)=='SCH_PAGE' for doc in docs)==1 and meta(page)['title']==inp['首页']
 bu,su,pu=[doc[0][1]['uuid'] for doc in (board,sch,page)]
 assert meta(sch)['board']==bu and meta(page)['schematic']==su
 # META/ticket必须全页唯一，按组件在其属性之前的原始记录顺序重新编号。
 for doc in docs:
  ids=[a['id'] for a,b in doc if 'id' in a];assert len(ids)==len(set(ids)),('重复图元id',kind(doc))
  for i,(a,b) in enumerate(doc):
   if a['type']!='DOCHEAD':a['ticket']=i
 libraries=[doc for k in ('SYMBOL','FOOTPRINT','DEVICE','BLOB','FONT') for doc in docs if kind(doc)==k]
 available={doc[0][1]['uuid'] for doc in libraries}
 for doc in libraries+[page]:
  for a,b in doc:
   if kind(doc)=='SCH_PAGE' and a['type']=='ATTR' and b.get('key') in ('Symbol','Device','Footprint') and b.get('value'):
    assert b['value'] in available,('库引用缺失',b)
   if a['type']=='META':
    for key,val in b.get('attributes',{}).items():
     if key in ('Symbol','Footprint') and val:assert val in available
    attrs=b.get('attributes',{})
    for key in ('Symbol','Footprint'):
     encoded=attrs.get(key+'Name')
     if isinstance(encoded,str) and encoded.startswith('{'):
      embedded=json.loads(encoded).get('uuid')
      assert not embedded or embedded in available,('内嵌库引用缺失',key,embedded)
      assert not embedded or embedded==attrs.get(key),('内嵌库引用不一致',key,embedded,attrs.get(key))
 profile={k:{} for k in ('boards','schematics','sheets','pcbs','panels','blockSymbols','simSchematics','simulations')}
 profile['boards'][bu]={'uuid':bu,**meta(board),'name':meta(board)['title']}
 profile['schematics'][su]={'uuid':su,'name':meta(sch)['title'],'board':bu,'source':''}
 profile['sheets'][pu]={'uuid':pu,'title':meta(page)['title'],'schematic_uuid':su,'zIndex':1,'source':''}
 config=copy.deepcopy(meta(next(doc for doc in docs if kind(doc)=='CONFIG')));config.update(defaultSheet=pu,settings={})
 index={'name':c['name'],'content':'','archive':False,'cbb_project':0,'ticket':1,'g_ticket':1,
  'boards':[],'pcb_count':0,'format':'folder','profile':profile,'default_sheet':pu,'config':config}
 physical=c.get('physical_board',c['board'])
 folder=(c['live_base']/physical/'原生候选'/'单页完整工程' if c['board'] in SPLIT_BOARDS else c['live_base']/'原生工程'/physical)
 if c.get('preview_only'):folder=out/'完整结构候选'
 assert folder.resolve().is_relative_to((out if c.get('preview_only') else c['live_base']).resolve()) and not folder.exists(),'交付目标已有内容，禁止覆盖'
 name=meta(sch)['title'];title=meta(page)['title'];assert all(not any(ch in s for ch in '<>:"/\\|?*') for s in (name,title,c['name']))
 def encode(blocks):return ('\n'.join(d.record_json(a)+'||'+d.record_json(b)+'|' for doc in blocks for a,b in doc)+'\n').encode('utf8')
 outputs={Path(c['name']+'.eprj3'):(dump(index)+'\n').encode('utf8'),
  Path('sch')/name/(name+'.ecfg'):encode([sch]),Path('sch')/name/(title+'.esch2'):encode(libraries+[page])}
 # 4.1.60以这个官方说明文件作为文件夹锁载体；补齐官方目录构成，不绕过文件锁。
 lock_template=intro_lock_template()
 outputs[Path('eprj3-intro.md')]=lock_template.read_bytes()
 for relative,data in outputs.items():
  path=folder/relative;path.parent.mkdir(parents=True,exist_ok=True);write_exclusive(path,data)
 entry=folder/(c['name']+'.eprj3');structure=d.project_documents(entry)
 evidence={'工程索引':str(entry.relative_to(ROOT)),'生成方式':'官方Workflow B完整文件夹生成；不是官方另存，也不是改扩展名',
  '文件生成':True,'官方另存':False,'官方保存':False,'关闭独立重开':False,'有效官方网表':False,'ERC通过':False,
  '板源文件SHA256':c['hashes'],'源SHA256':c['digest'],'工具SHA256':sha(__file__),
  '输入交换文件':str(original.relative_to(ROOT)),'输入交换SHA256':sha(original),'磁盘结构':structure,
  '端口端点调整':changes,'完整目录文件SHA256':{str(p.relative_to(folder).as_posix()):sha(p) for p in folder.rglob('*') if p.is_file()}}
 if c.get('preview_only'):return evidence
 if result.get('官方文件夹工程'):result.setdefault('官方文件夹工程历史',[]).append(result['官方文件夹工程'])
 result['官方文件夹工程']=evidence
 result['正式单板原生目录']={'入口':str(entry.relative_to(ROOT)),'对应源文件SHA256':c['hashes'],
  '生成方式':evidence['生成方式'],'实际入口独立重开':False,'范围':'已生成完整单板单页；尚未官方保存/回读验收，不放行布局'}
 update(c,result);print(dump({'完整单板目录':str(entry),'文件数':len(outputs),'元件数':len(c['parts']),'官方验收':'待执行'}),flush=True)


def verify_direct_folder(c):
 """直接生成后只做一次官方保存及关闭重开；证据与文件生成分别记录。"""
 result=validation_result(c);d=module('原理图交付')
 if c.get('native_scope'):
  inp=read(c['build_root']/'结构预览输入.json')
  verify_cached_central_candidate(c,result,inp,d)
  return
 inp=read(packet(c))
 e=result['官方文件夹工程'];formal=result['正式单板原生目录']
 index=ROOT/formal['入口'];assert e.get('文件生成')
 assert not [s for s in d.cli(EXE,'session','list')['value'] if s.get('status') not in ('closed','destroyed')]
 lockfile=index.parent/'eprj3-intro.md'
 if not lockfile.exists():
  template=intro_lock_template()
  write_exclusive(lockfile,template.read_bytes())
  e['原生锁载体修正']={'文件':lockfile.name,'官方模板SHA256':sha(template),
   '依据':'4.1.60服务端日志lockFile ENOENT；补齐官方生成目录的eprj3-intro.md，不删除或绕过锁'}
 out=new_export_dir(Path(inp['构建目录']),'直接文件夹官方');session=None;phase='打开生成目录'
 def invoke(code):return d.cli(EXE,'invoke','--session',session,'--ext-uuid','eda','--timeout','60000','--code',code)['value']
 def export(name):
  raw=invoke('const f=await eda.sys_FileManager.getProjectFile("直接文件夹回读",undefined,"epro2");const a=new Uint8Array(await f.arrayBuffer());let s="";for(let i=0;i<a.length;i+=32768)s+=String.fromCharCode(...a.subarray(i,i+32768));return {size:f.size,data:btoa(s)};')
  data=base64.b64decode(raw['data'],validate=True);assert len(data)==raw['size'];path=out/name;write_exclusive(path,data)
  return path,verify_current_graph(c,inp,path)
 try:
  session=d.cli(EXE,'open','--path',index.as_posix(),'--headless','true')['value']['sessionId'];d.wait_for_project(invoke)
  pages=invoke('return await eda.dmt_Schematic.getAllSchematicPagesInfo();')
  assert len(pages)==1 and pages[0]['name']==inp['首页'],pages
  first=pages[0]['uuid'];d.open_document(invoke,first)
  phase='生成目录逐脚回读';path,before=export('保存前回读.epro2');e['生成目录官方逐脚及BOM回读']=before
  texts=invoke('return (await eda.sch_PrimitiveText.getAll()).map(t=>({id:t.getState_PrimitiveId(),content:t.getState_Content()}));')
  assert texts
  t=next((t for t in texts if '原理图' in t['content']),texts[0]);newtext=t['content']+' · eprj3同版保存 '+c['digest'][:12]
  phase='官方编辑保存';edit=None
  try:
   edit=d.edit_native_text(invoke,first,t['id'],t['content'],newtext);e.update(官方保存=True,官方持久化编辑=edit)
  except Exception as error:
   e.setdefault('保存缺口',[]).append(str(error)[:3000]);e['官方保存']=False
  d.cli(EXE,'session','close','--session',session,'--destroy');session=None
  phase='独立重开实际入口'
  session=d.cli(EXE,'open','--path',index.as_posix(),'--headless','true')['value']['sessionId'];d.wait_for_project(invoke);d.open_document(invoke,first)
  if edit:assert newtext in invoke('return (await eda.sch_PrimitiveText.getAll()).map(t=>t.getState_Content());')
  path,after=export('独立重开回读.epro2')
  e.update(关闭独立重开=True,逐脚及BOM回读=after,实际官方交换文件=str(path.relative_to(ROOT)),实际官方交换SHA256=sha(path))
  formal.update(实际入口独立重开=True,实际入口逐脚BOM回读=after,回读文件=str(path.relative_to(ROOT)),回读SHA256=sha(path))
  result.update(官方编辑保存独立重开=bool(edit),官方独立重开交换逐脚回读=after,原生格式='完整eprj3文件夹工程')
  print('直接文件夹关闭重开和逐脚/BOM通过',c.get('physical_board',c['board']),'编辑保存',bool(edit),flush=True)
  phase='ERC与网表';erc=invoke(d.ERC_CODE);passed=not any(r['count'] for r in erc['summary'])
  e.update(官方ERC结果=erc,ERC通过=passed);result.update(官方ERC已执行=True,官方ERC结果=erc,ERC通过=passed)
  reply=invoke('try{const f=await eda.sch_ManufactureData.getNetlistFile("官方网表","Protel2");return f?{text:await f.text()}:{returnType:typeof f};}catch(e){return {error:String(e)};}')
  if reply.get('text'):
   path,h=save_export_text(out,'官方网表.net',reply['text']);check=verify_protel2(reply['text'],inp)
   e.update(官方网表文件=str(path.relative_to(ROOT)),官方网表SHA256=h,官方网表全量核对=check,有效官方网表=check['status']=='PASS')
  else:e['官方网表失败']=reply
  phase='官方图面导出';svg=invoke('const f=await eda.sch_ManufactureData.getSvgFile("单板原生图面");return f?{text:await f.text()}:null;')
  if svg and '<svg' in svg.get('text',''):
   path,h=save_export_text(out,'单板原生图面.svg',svg['text'])
   result['单板图面核验']={'官方SVG':str(path.relative_to(ROOT)),'SVG_SHA256':h,'源SHA256':c['digest'],'页数':1,'视觉验收':'待实际渲染检查'}
 except Exception as error:
  e.setdefault('直接生成验收失败',[]).append({'阶段':phase,'错误':type(error).__name__+': '+str(error)[:4000],'栈':traceback.format_exc()[-4000:]})
  print('直接文件夹验收失败',phase,str(error)[:1500],flush=True)
 finally:
  if session:
   try:d.cli(EXE,'session','close','--session',session,'--destroy')
   except Exception as error:e['关闭失败']=str(error)[:1000]
  e['完整目录文件SHA256']={p.relative_to(index.parent).as_posix():sha(p) for p in index.parent.rglob('*') if p.is_file()}
  formal.update(正式入口重开后目录SHA256=e['完整目录文件SHA256'],有效官方网表=bool(e.get('有效官方网表')),ERC通过=bool(e.get('ERC通过')))
  update(c,result)
 print(dump({k:e.get(k) for k in ('工程索引','文件生成','官方保存','关闭独立重开','有效官方网表','ERC通过')}),flush=True)


def verify_cached_central_candidate(c,result,inp,d):
 """Save, close and independently reopen only the cached central board-on candidate."""
 base_scope=c['native_scope'];scope=inp.get('原理图范围',{});candidate=result.get('结构图面候选')
 assert candidate and candidate.get('板源文件SHA256')==c['hashes']
 assert inp.get('板源文件SHA256')==c['hashes']
 assert {k:v for k,v in scope.items() if k not in ('embedded_footprint_library_member_count','embedded_footprint_library_members')}==base_scope
 assert len(inp['绑定'])==scope['board_on_ref_count']==960
 refs={b['位号'] for b in inp['绑定']}
 assert len(refs)==960 and scope_digest(refs)==scope['board_on_refs_sha256']
 members=sorted({b['库文件'] for b in inp['绑定'] if b.get('库文件')})
 assert members==scope['embedded_footprint_library_members']
 assert all(b.get('封装') and b.get('库文件') and b.get('封装SHA256') for b in inp['绑定'])
 manifest=read(c['stable_manifest_path']);bom=Path(c['live_base'])/manifest['作者BOM']
 assert sha(bom)==manifest['作者BOM_SHA256']
 with bom.open(encoding='utf-8-sig',newline='') as f:full_bom_rows=list(csv.DictReader(f))
 bom_rows=[row for row in full_bom_rows if row['位号'] in refs]
 assert len(bom_rows)==960 and {r['位号'] for r in bom_rows}==refs
 parts={p['ref']:p for p in c['parts']}
 for row in bom_rows:
  p=parts[row['位号']]
  assert row['完整型号']==p['mpn'] and row['标称参数']==str(p['value'])
  assert row['所属板或取电边界']==p['board'] and row['装配']==p['assembly']
 expected_bom_sha=hashlib.sha256(json.dumps(bom_rows,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf8')).hexdigest()

 folder_evidence=candidate['候选完整eprj3目录'];index=ROOT/folder_evidence['工程索引']
 folder=index.parent;assert index.is_file() and folder.resolve().is_relative_to(c['build_root'].resolve())
 docs_before=d.project_documents(index);index_before=read(index)
 pages_before=index_before['profile']['sheets'];assert len(pages_before)==1
 page_uuid,page_row=next(iter(pages_before.items()))
 assert page_uuid==page_row['uuid'] and index_before.get('pcb_count',0)==0
 assert not index_before['profile'].get('pcbs') and not list(folder.rglob('*.epcb2'))
 page_file=folder/next(x['文件'] for x in docs_before['文档'] if x['文档类型']=='SCH_PAGE')
 def page_refs(path):
  page_refs=set();doc_type=None
  for _,(a,b) in d.records(path.read_text(encoding='utf8')):
   if a.get('type')=='DOCHEAD':doc_type=b.get('docType')
   if doc_type=='SCH_PAGE' and a.get('type')=='COMPONENT':
    unique_id=b.get('attrs',{}).get('Unique ID','')
    if unique_id:
     assert unique_id.startswith('gge_'),('实例COMPONENT位号ID格式异常',unique_id)
     page_refs.add(unique_id[4:])
  return page_refs
 assert page_refs(page_file)==refs
 def profile_identity(index_data):
  profile=index_data['profile']
  def records(name,fields):
   rows={}
   for uuid,row in profile.get(name,{}).items():
    rows[uuid]={key:row.get(key) for key in fields}
   return rows
  boards={uuid:{'uuid':row.get('uuid'),'title':row.get('title'),
   'name':row.get('name') or row.get('title'),'zIndex':row.get('zIndex')}
   for uuid,row in profile.get('boards',{}).items()}
  return {'name':index_data.get('name'),'default_sheet':index_data.get('default_sheet'),
   'pcb_count':index_data.get('pcb_count'),
   'profile':{'boards':boards,
    'schematics':records('schematics',('uuid','name','board','source')),
    'sheets':records('sheets',('uuid','title','schematic_uuid','zIndex','source')),
    'pcbs':records('pcbs',('uuid','name','title','board','source')),
    'panels':records('panels',('uuid','name','title','source')),
    'blockSymbols':records('blockSymbols',('uuid','name','title','source')),
    'simSchematics':records('simSchematics',('uuid','name','title','source')),
    'simulations':records('simulations',('uuid','name','title','source'))}}
 identity_before=profile_identity(index_before)
 def tree_hashes(root):
  return {p.relative_to(root).as_posix():sha(p) for p in sorted(root.rglob('*')) if p.is_file()}
 before_hashes=tree_hashes(folder)
 formal_dir=HW/'FOC驱动与储能'/'原生工程'/'中央稳压模块'
 formal_before=tree_hashes(formal_dir) if formal_dir.is_dir() else None
 proof={'板源文件SHA256':c['hashes'],'原理图范围':scope,'源板上位号精确匹配':True,
  'board_on_refs_sha256':scope_digest(refs),'board_on_refs_count':len(refs),
  '作者全量BOM路径':str(bom.relative_to(ROOT)),'作者全量BOM_SHA256':sha(bom),
  '板上BOM期望位号数':len(bom_rows),'板上BOM期望属性SHA256':expected_bom_sha,
  '候选索引':str(index.relative_to(ROOT)),
  '保存前工程索引SHA256':sha(index),'保存前工程目录SHA256':before_hashes,
  '保存前项目语义身份':identity_before,'保存前官方文档UUID核验':docs_before,
  '原始候选记录目录SHA与当前一致':folder_evidence.get('完整目录文件SHA256')==before_hashes,
  'PCB文档数':len(index_before['profile'].get('pcbs',{})),'PCB文件数':len(list(folder.rglob('*.epcb2'))),
  '正式原生目录保存前SHA256':formal_before,'正式目录未触碰':True,
  '官方保存':False,'保存后等待秒数':9,'独立重开':False,'官方ERC已执行':False,
  '有效官方网表':False,'官方图面':''}
 out=new_export_dir(Path(inp['构建目录']),'中央板内官方闭合核验');session=None;failure=None;phase='检查官方客户端会话'
 before_sessions=[];after_first_close=[];after_final_close=[];save_result=None;baseline_active_ids=set();baseline_session_ids=set();protel_pass=False;jlceda_pass=False
 def invoke(code):
  return d.cli(EXE,'invoke','--session',session,'--ext-uuid','eda','--timeout','60000','--code',code)['value']
 def active_sessions(rows):
  return [s for s in rows if s.get('status') not in ('closed','destroyed')]
 def active_ids(rows):
  return {s.get('sessionId') for s in active_sessions(rows)}
 def normalized_project_name(value):
  if value is None:return None
  return str(value).replace('\\','/').rstrip('/').rsplit('/',1)[-1]
 def wait_active_ids(expected,attempts=20):
  rows=None
  for _ in range(attempts):
   rows=d.cli(EXE,'session','list')['value']
   if active_ids(rows)==expected:return rows
   time.sleep(.25)
  raise AssertionError(('session集合未稳定',expected,rows))
 try:
  before_sessions=d.cli(EXE,'session','list')['value']
  assert isinstance(before_sessions,list),('官方session list格式异常',before_sessions)
  active=active_sessions(before_sessions)
  proof['官方既有活跃会话']=active
  baseline_active_ids=active_ids(before_sessions)
  baseline_session_ids={s.get('sessionId') for s in before_sessions}
  phase='首次打开候选工程'
  opened_session=d.cli(EXE,'open','--path',index.as_posix(),'--headless','true')['value']['sessionId']
  assert opened_session not in baseline_session_ids,'官方open试图复用既有会话；该会话未赋予本任务关闭权限'
  session=opened_session
  after_open=wait_active_ids(baseline_active_ids|{session})
  info=d.wait_for_project(invoke)
  proof['首次打开项目回读']={'name':info.get('name'),'normalized_name':normalized_project_name(info.get('name',info.get('title'))),
   'uuid':info.get('uuid'),'path':info.get('path')}
  project_name=info.get('name',info.get('title'))
  if project_name is not None:assert normalized_project_name(project_name)==index_before['name'],('已打开项目名不匹配',project_name,index_before['name'])
  pinfo=invoke('return await eda.dmt_Schematic.getAllSchematicPagesInfo();')
  assert len(pinfo)==1 and pinfo[0].get('uuid')==page_uuid and pinfo[0].get('name')==page_row['title'],pinfo
  d.open_document(invoke,page_uuid)
  phase='官方保存候选工程'
  focus=invoke('const s=await eda.dmt_Schematic.getCurrentSchematicInfo();const p=await eda.dmt_Schematic.getCurrentSchematicPageInfo();return {schematicUuid:s?.uuid,pageUuid:p?.uuid,parentSchematicUuid:p?.parentSchematicUuid};')
  assert focus=={'schematicUuid':next(iter(index_before['profile']['schematics'])),'pageUuid':page_uuid,
   'parentSchematicUuid':next(iter(index_before['profile']['schematics']))},focus
  save_result=invoke('const p=await eda.dmt_Schematic.getCurrentSchematicPageInfo();const saved=await eda.sch_Document.save();return {saved,pageUuid:p?.uuid};')
  proof['官方保存']=save_result.get('saved') is True
  proof['官方保存原始返回']=save_result
  time.sleep(9)
  proof['保存后等待秒数']=9
  d.cli(EXE,'session','close','--session',session,'--destroy');session=None
  phase='检查保存后会话关闭'
  after_first_close=wait_active_ids(baseline_active_ids)
  proof['保存后关闭会话列表']=after_first_close
  phase='独立重新打开候选工程'
  reopened_session=d.cli(EXE,'open','--path',index.as_posix(),'--headless','true')['value']['sessionId']
  assert reopened_session not in baseline_session_ids,'独立重开复用了既有会话；本任务不得关闭它'
  session=reopened_session
  wait_active_ids(baseline_active_ids|{session})
  reopened=d.wait_for_project(invoke)
  proof['独立重开项目回读']={'name':reopened.get('name'),'normalized_name':normalized_project_name(reopened.get('name',reopened.get('title'))),
   'uuid':reopened.get('uuid'),'path':reopened.get('path')}
  project_name=reopened.get('name',reopened.get('title'))
  if project_name is not None:assert normalized_project_name(project_name)==index_before['name'],('重开项目名不匹配',project_name,index_before['name'])
  page_list=invoke('return await eda.dmt_Schematic.getAllSchematicPagesInfo();')
  assert len(page_list)==1 and page_list[0].get('uuid')==page_uuid and page_list[0].get('name')==page_row['title'],page_list
  d.open_document(invoke,page_uuid)
  phase='官方关闭重开逐脚BOM回读'
  focus_after=invoke('const s=await eda.dmt_Schematic.getCurrentSchematicInfo();const p=await eda.dmt_Schematic.getCurrentSchematicPageInfo();return {schematicUuid:s?.uuid,pageUuid:p?.uuid,parentSchematicUuid:p?.parentSchematicUuid};')
  assert focus_after==focus,focus_after
  export_reply=invoke('const f=await eda.sys_FileManager.getProjectFile("板内关闭重开回读",undefined,"epro2");const a=new Uint8Array(await f.arrayBuffer());let s="";for(let i=0;i<a.length;i+=32768)s+=String.fromCharCode(...a.subarray(i,i+32768));return {size:f.size,data:btoa(s)};')
  exported=base64.b64decode(export_reply['data'],validate=True);assert len(exported)==export_reply['size']
  exchange=out/'板内关闭重开回读.epro2';write_exclusive(exchange,exported)
  graph=verify_current_graph(c,inp,exchange)
  expected_graph=(graph.get('connection_readback')=='PASS_CONVERTED_PIN_AND_WIRE_GEOMETRY'
   and graph.get('actual_component_refs')==960 and graph.get('connected_pins')==2916
   and graph.get('NC_pins')==99 and graph.get('full_BOM_readback',{}).get('status')=='PASS_ACTUAL_EXCHANGE_ALL_COMPONENT_ATTRIBUTES'
   and graph.get('full_BOM_readback',{}).get('count')==960)
  proof.update(官方保存关闭重开交换文件=str(exchange.relative_to(ROOT)),
   官方保存关闭重开交换SHA256=sha(exchange),官方保存关闭重开逐脚BOM=graph,
   板内逐脚BOM_精确核对=expected_graph)
  phase='官方原始ERC'
  erc=invoke('try{const passed=await eda.sch_Drc.check(true,false,true);return {returnType:typeof passed,raw:passed,strict:true,showError:false,includeVerbose:true};}catch(e){return {thrown:String(e),strict:true,showError:false,includeVerbose:true};}')
  proof['官方ERC已执行']=True;proof['官方ERC结果']=erc
  erc_pass=erc.get('returnType')=='boolean' and erc.get('raw') is True
  proof['ERC通过']=erc_pass
  raw=erc.get('raw');severity_counts=raw if isinstance(raw,list) and all(
   isinstance(item,dict) and set(item).issubset({'type','count'}) for item in raw) else None
  if erc_pass:
   erc_class={'status':'PASS','rule_details_available':False,'不豁免':True}
  elif erc.get('returnType')=='boolean' and raw is False:
   erc_class={'status':'UNCLASSIFIED_RAW_FALSE','rule_details_available':False,
    '原因':'官方API返回布尔false；当前4.1.60响应未提供可逐条分类字段','不豁免':True}
  elif severity_counts is not None:
   erc_class={'status':'UNCLASSIFIED_SEVERITY_COUNTS_ONLY','rule_details_available':False,
    '官方严重度计数':severity_counts,
    '原因':'官方strict ERC返回严重度计数数组，不含规则、位号或网络明细；不能从该响应推断raw pass/false或逐条分类',
    '不豁免':True}
  else:
   erc_class={'status':'UNCLASSIFIED_API_RESPONSE','rule_details_available':bool(erc.get('details') or erc.get('items')),
    '原因':'官方ERC响应未提供可确认的布尔通过值或逐条分类结果','不豁免':True}
  proof['ERC分类']=erc_class
  phase='官方Protel2网表'
  net=official_netlist_text(invoke,'板内关闭重开官方网表','ALTIUM_DESIGNER')
  proof['官方网表官方API返回']={k:v for k,v in net.items() if k!='text'}
  if net.get('text'):
   net_path=out/'板内关闭重开Protel2.net';write_exclusive(net_path,net['text'].encode('utf8'))
   net_check=verify_protel2(net['text'],inp)
   protel_pass=net_check.get('status')=='PASS' and net_check.get('actual_component_refs')==960 and net_check.get('connected_pins')==2916 and net_check.get('expected_NC_pins')==99
   proof.update(官方网表文件=str(net_path.relative_to(ROOT)),官方网表SHA256=sha(net_path),
    官方网表逐脚核验=net_check,Protel2板内范围核验=protel_pass)
  jlceda=official_netlist_text(invoke,'板内关闭重开JLCEDA官方网表','JLCEDA_PRO')
  proof['JLCEDA官方网表官方API返回']={k:v for k,v in jlceda.items() if k!='text'}
  if jlceda.get('text'):
   jlceda_path=out/'板内关闭重开JLCEDA_PRO.enet';write_exclusive(jlceda_path,jlceda['text'].encode('utf8'))
   try:
    jlceda_check=verify_jlceda(jlceda['text'],inp)
    jlceda_pass=(jlceda_check.get('status')=='PASS' and jlceda_check.get('actual_component_refs')==960
     and jlceda_check.get('connected_pins')==2916 and jlceda_check.get('NC_pins')==99
     and jlceda_check.get('NC完全相同') is True and jlceda_check.get('板上位号')==960
     and jlceda_check.get('板外合同位号')==0)
    proof.update(JLCEDA官方网表=str(jlceda_path.relative_to(ROOT)),JLCEDA官方网表SHA256=sha(jlceda_path),
     JLCEDA_PRO板内逐脚NC核验=jlceda_check,JLCEDA_PRO板内范围核验=jlceda_pass)
   except Exception as error:proof['JLCEDA_PRO验证错误']=type(error).__name__+': '+str(error)[:2000]
  proof['有效官方网表']=bool(protel_pass and proof.get('板内逐脚BOM_精确核对'))
  phase='官方SVG图面导出'
  svg_reply=invoke('try{const f=await eda.sch_ManufactureData.getSvgFile("中央板内关闭重开原生图面");return f?{text:await f.text(),mime:f.type}:null;}catch(e){return {error:String(e)};}')
  svg=svg_reply.get('text') if isinstance(svg_reply,dict) else None
  if isinstance(svg,str) and '<svg' in svg[:1000]:
   svg_bytes=svg.encode('utf8');svg_digest=hashlib.sha256(svg_bytes).hexdigest()
   old_svg=ROOT/candidate['官方SVG'] if candidate.get('官方SVG') else None
   if old_svg and old_svg.is_file() and sha(old_svg)==svg_digest:
    svg_path=old_svg;svg_reused=True
   else:
    svg_path=out/'板内关闭重开官方图面.svg';write_exclusive(svg_path,svg_bytes);svg_reused=False
   lowered=svg.lower()
   proof.update(官方图面路径=str(svg_path.relative_to(ROOT)),官方图面SHA256=sha(svg_path),
    官方图面与既有候选预览逐字节一致=svg_reused,
    官方SVG残留winding_start_end文本数=lowered.count('winding start')+lowered.count('winding end'),
    官方SVG类型=svg_reply.get('mime'))
   proof['官方图面']='PASS_EXPORTED' if proof['官方SVG残留winding_start_end文本数']==0 else 'FAIL_REDUNDANT_WINDING_TEXT_PRESENT'
  else:proof['官方图面']='FAIL_EXPORT';proof['官方图面导出返回']=svg_reply
  proof['独立重开']=True
 except Exception as error:
  failure={'阶段':locals().get('phase','cached_candidate_save_close_reopen'),
   '类型':type(error).__name__,'错误':str(error)[:3000]}
  proof['失败']=failure
 finally:
  if session:
   try:
    d.cli(EXE,'session','close','--session',session,'--destroy');session=None
   except Exception as error:proof['本任务会话关闭错误']=str(error)[:1000]
  try:
   after_final_close=d.cli(EXE,'session','list')['value']
   proof['最终会话列表']=after_final_close
   proof['既有会话ID仍保留']=active_ids(after_final_close)==baseline_active_ids
   proof['无本任务遗留活会话']=session is None and active_ids(after_final_close)==baseline_active_ids
  except Exception as error:proof['最终会话列表读取错误']=str(error)[:1000]
  index_after=read(index);docs_after=d.project_documents(index)
  after_hashes=tree_hashes(folder)
  identity_after=profile_identity(index_after)
  proof.update(独立重开后项目语义身份=identity_after,
   项目profile文档UUID语义未变=identity_after==identity_before,
   项目profile语义比较口径='比较项目名、默认页、PCB数及profile文档UUID/名称/归属/标题/排序/源引用；boards.name按title别名归一化，忽略version/updateTime',
   保存前项目profile原始记录=copy.deepcopy(index_before['profile']),
   保存后项目profile原始记录=copy.deepcopy(index_after['profile']),
   独立重开后官方文档UUID核验=docs_after,
   保存关闭重开后目录SHA256=after_hashes,
   保存关闭重开后工程索引SHA256=sha(index),
   保存关闭重开后工程目录摘要SHA256=hashlib.sha256(json.dumps(after_hashes,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest(),
   保存关闭重开前后目录变化={k:[before_hashes.get(k),after_hashes.get(k)] for k in sorted(set(before_hashes)|set(after_hashes)) if before_hashes.get(k)!=after_hashes.get(k)},
   正式原生目录保存后SHA256=tree_hashes(formal_dir) if formal_dir.is_dir() else None)
  proof['正式目录未触碰']=proof['正式原生目录保存前SHA256']==proof['正式原生目录保存后SHA256']
  proof['候选只含板上器件']=page_refs(page_file)==refs
  candidate['候选原生闭合核验']=proof
  candidate.update(官方编辑保存独立重开=bool(proof.get('官方保存') and proof.get('独立重开')
    and proof.get('项目profile文档UUID语义未变')),
   官方独立重开交换逐脚回读=proof.get('板内逐脚BOM_精确核对',False),
   全量交换逐脚BOM=proof.get('板内关闭重开逐脚BOM'),
   有效官方网表=proof.get('有效官方网表',False),
   官方ERC已执行=proof.get('官方ERC已执行',False),
   官方ERC结果=proof.get('官方ERC结果',candidate.get('官方ERC结果')),
   ERC通过=proof.get('ERC通过',False),
   ERC分类=proof.get('ERC分类') or {'status':'NOT_RUN','失败':proof.get('失败')},正式工程未覆盖=True)
  candidate['保存关闭独立重开']=candidate['官方编辑保存独立重开']
  if proof.get('官方图面')=='PASS_EXPORTED':
   candidate['官方SVG']=proof['官方图面路径'];candidate['SVG_SHA256']=proof['官方图面SHA256']
   candidate['视觉验收']='待独立实际阅读；官方同版SVG已保存'
  result['官方编辑保存独立重开']=candidate['官方编辑保存独立重开']
  result['官方独立重开交换逐脚回读']=candidate['官方独立重开交换逐脚回读']
  result['有效官方网表']=candidate['有效官方网表']
  result['官方ERC已执行']=candidate['官方ERC已执行'];result['官方ERC结果']=candidate.get('官方ERC结果')
  result['ERC通过']=candidate['ERC通过'];result['ERC分类']=candidate.get('ERC分类')
  update(c,result)
 print(dump({'candidate':str(index.relative_to(ROOT)),'saved':proof.get('官方保存'),
  'reopened':proof.get('独立重开'),'board_on_graph':proof.get('板内逐脚BOM_精确核对'),
  'protel2':proof.get('有效官方网表'),'erc':proof.get('官方ERC结果'),
  'svg':proof.get('官方图面'),'formal_untouched':proof.get('正式目录未触碰'),
  'failure':proof.get('失败')}),flush=True)


def finalize_delivery(c):
 """既有证据收口：完整目录SHA、源适用性及已人工查看的官方渲染范围。"""
 result=validation_result(c);e=result.get('官方文件夹工程',{});formal=result.get('正式单板原生目录',{})
 if formal:
  index=ROOT/formal['入口'];folder=index.parent
  manifest={p.relative_to(folder).as_posix():sha(p) for p in sorted(folder.rglob('*')) if p.is_file()}
  expected=formal.get('正式入口重开后目录SHA256',e.get('完整目录文件SHA256'))
  assert manifest==expected,'原生目录已变；不沿用旧验证'
  formal.update(入口SHA256=sha(index),完整目录文件SHA256=manifest,
   工程目录清单SHA256=hashlib.sha256(json.dumps(manifest,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest(),
   工程摘要算法='SHA256(JSON(相对路径->文件SHA256,ensure_ascii=False,sort_keys=True,compact).UTF8)',
   单板单页磁盘结构=module('原理图交付').project_documents(index))
  if e.get('文件生成'):
   if e.get('官方保存') and result.get('官方编辑保存独立重开'):
    formal['范围']='完整单板单页已生成；实际编辑保存、关闭独立重开及逐脚/BOM通过；网表、ERC及视觉验收分别记录，未据此放行PCB布局'
    e['保存诊断结论']='修正DEVICE.SymbolName内嵌UUID与Symbol不同步的生成器缺陷后，官方编辑保存及关闭独立重开通过；原失败及修正前字节保留在历史记录。'
   else:
    formal['范围']='完整单板单页已生成；实际入口独立重开及逐脚/BOM通过；官方编辑保存尚未通过，未放行正常编辑或PCB布局'
    e['保存诊断结论']='保存尚未通过；各次官方日志、API返回及同版持久化验证分别记录。不归因于必须人类加载扩展，不绕过保存。'
  if c['board']=='FOC' and c['revision']=='RevM-ea0190d573e5':
   latest=source('FOC',frozen=True,revision='RevN-ea9850dfdb77')
   old=runpy.run_path(str(c['base']/'设计数据.py'))['PARTS'];new=runpy.run_path(str(latest['base']/'设计数据.py'))['PARTS']
   old=sorted((p for p in old if p['board']==c['physical_board']),key=lambda p:p['ref'])
   new=sorted((p for p in new if p['board']==c['physical_board']),key=lambda p:p['ref'])
   assert old==new,'本板PARTS改变，不能沿用旧版本'
   record={'版本':'RevM -> RevN-ea9850dfdb77','板':c['physical_board'],'本板全部归属位号':len(new),'本工程在板位号':len(c['parts']),
    '全部PARTS字段逐项完全相同':True,'canonical_SHA256':hashlib.sha256(json.dumps(new,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest(),
    '排序规则':'PARTS按ref排序，JSON sort_keys=True ensure_ascii=False compact UTF8','RevN源文件SHA256':latest['hashes'],'不扩展到其他板或整域电气放行':True}
   result['逐板版本适用']=record;formal['逐板版本适用']=record
 notes={'驱动主板':'已查看官方整页渲染：三相桥按重复通道组织，其余按功能区连接；仍有长跨区线、外伸网络文字和拥挤区，不通过整页视觉验收。',
  '中央稳压模块':'已查看官方整页渲染：主功率链、控制器、超容单元和保护分区可辨；仍有长跨区线、外伸文字及留白不均，不通过整页视觉验收。',
  'BMS板':'已查看官方上部1900px裁切：输入保护、驱动、AFE分区及实体连接可辨；全图2300x10434仍过长，下部尚未逐区目视验收，不通过整页视觉验收。'}
 scope=c.get('physical_board',c['board']);visual=result.get('单板图面核验',{})
 if scope in notes and visual.get('官方SVG') and visual.get('视觉验收')!='待实际渲染检查':
  svg=ROOT/visual['官方SVG'];png=svg.with_suffix('.png');assert sha(svg)==visual['SVG_SHA256'] and png.is_file()
  visual.update(原生PNG=str(png.relative_to(ROOT)),PNG_SHA256=sha(png),视觉验收='PARTIAL_NOT_PASSED',实际查看=notes[scope],
   渲染来源='官方SVG经Sharp栅格化，非重新绘制电路；图面部分改善不代表工程整体完成')
  crop=svg.with_name(svg.stem+'-上部核查.png')
  if scope=='BMS板' and crop.exists():visual.update(实际查看裁切=str(crop.relative_to(ROOT)),裁切SHA256=sha(crop))
 update(c,result)
 print(dump({'板':scope,'入口':formal.get('入口'),'工程目录清单SHA256':formal.get('工程目录清单SHA256'),
  '入口SHA256':formal.get('入口SHA256'),'逐字段版本适用':result.get('逐板版本适用'),
  '保存关闭重开':result.get('官方编辑保存独立重开'),'入口独立重开':formal.get('实际入口独立重开'),
  'ERC':(result.get('官方ERC结果') or {}).get('summary'),'有效官方网表':e.get('有效官方网表'),'视觉':visual.get('视觉验收')}))


def promote_folder(c):
 """交付完整已重开工程；格式交付不以ERC失败为由隐藏，也不冒充电气放行。"""
 result=validation_result(c);e=result['官方文件夹工程']
 assert all(e.get(k) for k in ('官方另存','关闭独立重开','输入中间件未变'))
 assert e.get('逐脚及BOM回读'), '缺少同版全量回读，不能提升'
 folder=(ROOT/e['工程索引']).parent;manifest=e['完整目录文件SHA256']
 assert {p.relative_to(folder).as_posix():sha(p) for p in folder.rglob('*') if p.is_file()}==manifest
 physical=c.get('physical_board') or ('配电板' if c['board']=='配电' else c['board'])
 assert physical in ('驱动主板','辅助电源板','中央稳压模块','BMS板','外充板','配电板')
 target=(c['live_base']/physical/'原生候选'/'单页完整工程' if c['board'] in SPLIT_BOARDS
         else c['live_base']/'原生工程'/physical)
 assert target.resolve().is_relative_to(c['live_base'].resolve())
 if target.exists():
  assert {p.relative_to(target).as_posix():sha(p) for p in target.rglob('*') if p.is_file()}==manifest,'已有不同正式目录；停止覆盖'
 else:shutil.copytree(folder,target)
 assert {p.relative_to(target).as_posix():sha(p) for p in target.rglob('*') if p.is_file()}==manifest
 result['正式单板原生目录']={'入口':str((target/Path(e['工程索引']).name).relative_to(ROOT)),
  '完整目录与已重开验证副本逐字节一致':True,'对应源文件SHA256':c['hashes'],
  '有效官方网表':bool(e.get('有效官方网表')),'ERC通过':bool(e.get('ERC通过')),
  '范围':'完整单板单页原生工程交付；网表、ERC、电气及制造放行分别记录，失败不变为PASS'}
 update(c,result);print(dump(result['正式单板原生目录']))


def publish_structured_folder(c):
 """更新真实查看入口；原生格式交付与电气/ERC/图面放行严格分开。"""
 c=dict(c,preview_only=True)
 current=lambda:all((c['live_base']/f).is_file() and sha(c['live_base']/f)==h for f,h in c['hashes'].items())
 assert current(),'作者活源已改变，保全候选不得覆盖当前入口'
 r=validation_result(c);record=r['结构图面候选']
 assert record['板源文件SHA256']==c['hashes'] and record['页数']==1
 assert record['官方编辑保存独立重开'] and record['官方重开全量逐脚BOM']
 origin_entry=ROOT/record['候选完整eprj3目录']['工程索引'];origin=origin_entry.parent.resolve()
 manifest=lambda folder:{p.relative_to(folder).as_posix():sha(p) for p in folder.rglob('*') if p.is_file()}
 expected=record['候选完整目录文件SHA256']
 assert origin.is_relative_to(CACHE.resolve()) and manifest(origin)==expected and len(expected)==4
 physical=c.get('physical_board',c['board'])
 if c['board'] in SPLIT_BOARDS:target=c['live_base']/physical/'原生候选/单页完整工程'
 else:target=c['live_base']/'原生工程'/('配电板' if c['board']=='配电' else physical)
 target=target.resolve()
 assert target.is_relative_to(c['live_base'].resolve()) and target!=c['live_base'].resolve()
 assert target.name in ('单页完整工程','驱动主板','中央稳压模块','辅助电源板','配电板')
 d=module('原理图交付')
 assert not [s for s in d.cli(EXE,'session','list')['value'] if s.get('status') not in ('closed','destroyed')]
 out=new_export_dir(origin.parent,'正式结构交付')
 prior_formal=r.get('正式单板原生目录',{})
 if not prior_formal and target.exists():
  # A new exact-source candidate may live in a new cache directory while
  # the human entry still refers to an older physical-board receipt. Preserve
  # that full receipt by its actual index; never treat it as the new PASS.
  live_record=read(c['live_base']/CONFIG[c['board']][4])
  previous_index=live_record.get('current_delivery_index',{}).get(physical,{})
  previous_path=previous_index.get('证据文件')
  if previous_path and (ROOT/previous_path).resolve()!=c['report'].resolve():
   previous_json=read(ROOT/previous_path)
   previous_validation=previous_json.get('native_validation_boards',{}).get(c['board'],{}) if c['board'] in SPLIT_BOARDS else previous_json.get('native_validation',{})
   historical=previous_validation.get('正式单板原生目录',{})
   if historical:
    assert historical['入口']==previous_index['当前版面正式eprj3入口']
    assert (ROOT/historical['入口']).parent.resolve()==target
    assert manifest(target)==historical['正式入口重开后目录SHA256'],'前版正式入口已变，不能保全或继承前版核验'
    r.setdefault('正式单板原生目录历史',[]).append(copy.deepcopy(historical))
    r['前版完整核验索引保全']={'文件':previous_path,'SHA256':sha(ROOT/previous_path),
     '前版完整原生记录已保留':True,'本版适用':False,'说明':'保留原始核验与旧原生文件；新版本仍重新保存重开和逐脚回读。'}
 if prior_formal:
  # Keep full receipts as well as the recoverable native directory bytes.
  history=r.setdefault('正式单板原生目录历史',[])
  if not history or history[-1]!=prior_formal:history.append(copy.deepcopy(prior_formal))
 resume=bool(prior_formal.get('入口验收失败') and not prior_formal.get('实际入口独立重开')
  and prior_formal.get('对应源文件SHA256')==c['hashes'] and target.exists()
  and manifest(target)==prior_formal.get('正式入口重开后目录SHA256'))
 previous=prior_formal.get('原入口保全')
 if target.exists() and manifest(target)!=expected and not resume:
  before=manifest(target)
  assert len(before)==4 and sum(n.endswith('.eprj3') for n in before)==1,'正式目标不符合已知四文件边界，停止替换'
  backup=out/'替换前完整工程';assert not backup.exists()
  assert backup.resolve().is_relative_to(CACHE.resolve())
  shutil.move(str(target),str(backup));assert manifest(backup)==before
  previous={'目录':str(backup.relative_to(ROOT)),'完整目录文件SHA256':before,'可恢复':True}
 if not target.exists():shutil.copytree(origin,target)
 assert current() and (resume or manifest(target)==expected)
 # 4.1.60 retained deleted title records after the public create/delete save.
 # Correct only that demonstrated presentation delta in the copied folder;
 # the independently reviewed candidate and all electrical records stay put.
 page_file=next(target.rglob('*.esch2'));rows=[row for _,row in d.records(page_file.read_text(encoding='utf8'))]
 attrs=collections.defaultdict(dict);part_by_ref={p['ref']:p for p in c['parts']};placement_changes=[];seen=set();page_kind=None
 for a,b in rows:
  if a['type']=='DOCHEAD':page_kind=b['docType']
  elif page_kind=='SCH_PAGE' and a['type']=='ATTR':attrs[b['parentId']][b['key']]=b
 for fields in attrs.values():
  if 'Designator' not in fields:continue
  ref=fields['Designator']['value'];assert ref in part_by_ref and ref not in seen;seen.add(ref)
  part=part_by_ref[ref];assert isinstance(part['onboard'],bool)
  want='yes' if part['onboard'] else 'no'
  assert fields['PCB_Placement']['value']==want,(ref,'BOM物理归属与作者不符')
  attribute=fields['Convert to PCB']
  if attribute['value']!=want:
   placement_changes.append({'位号':ref,'原值':attribute['value'],'修正':want,'依据':'同SHA作者onboard物理边界，不按封装就绪状态排除'})
   attribute['value']=want
 assert seen==set(part_by_ref)
 titles=[(a,b) for a,b in rows if a['type']=='TEXT' and '整板原理图' in b.get('value','')]
 assert titles and len({(b.get('x'),b.get('y')) for a,b in titles})==1
 clean_title=titles[0][1]['value'].split(' · 单页结构核对')[0]
 keep=next((a,b) for a,b in titles if b['value']==clean_title)
 removed={a['id'] for a,b in titles if a['id']!=keep[0]['id']}
 if removed or placement_changes:
  write_exclusive(out/'显示及PCB纳入修正前原图页.esch2',page_file.read_bytes())
  rows=[(a,b) for a,b in rows if not(a['type']=='TEXT' and a.get('id') in removed)]
  page_file.write_text('\n'.join(d.record_json(a)+'||'+d.record_json(b)+'|' for a,b in rows)+'\n',encoding='utf8',newline='\n')
 cleanup_manifest=manifest(target)
 if resume:
  assert not removed and not placement_changes,'失败入口在复验前仍有未经处理的属性差额'
  placement_changes=prior_formal['正式PCB纳入修正']
 entry=target/origin_entry.name;index=read(entry)
 assert all(len(index['profile'][k])==1 for k in ('boards','schematics','sheets'))
 inp=read(candidate_path(c).parent/'结构预览输入.json')
 formal={'入口':str(entry.relative_to(ROOT)),'对应源文件SHA256':c['hashes'],
  '复制时与已保存重开候选逐字节一致':True,'完整目录文件SHA256':cleanup_manifest,
  '正式入口纯显示修正':{'删除重复标题记录':sorted(removed),'保留标题':clean_title,'不修改网络及器件记录':True},
  '正式PCB纳入修正':placement_changes,'正式纳入统计':dict(collections.Counter('板上' if p['onboard'] else '板外' for p in c['parts'])),
  '磁盘结构':d.project_documents(entry),'原入口保全':previous,
  '实际入口独立重开':False,'有效官方网表':bool(record.get('有效官方网表')),
  '官方网表证据':record.get('官方PCB网表读取',record.get('官方网表全量核对')),
  'ERC通过':bool(record.get('ERC通过')),'原始ERC':record.get('官方ERC结果'),
  '图面视觉验收':record.get('视觉验收'),'整板放行':False,'制造放行':False,
  '范围':'完整可编辑单板单原理图单页查看入口；保存重开不代表缺封装、ERC、电气或layout放行'}
 if resume:
  formal['正式入口纯显示修正']=prior_formal['正式入口纯显示修正']
  formal['失败入口复验依据']={'前次失败':prior_formal['入口验收失败'],'目录SHA完全一致':True,
   '加载诊断':prior_formal.get('加载诊断'),'没有再次复制替换或重建图面':True}
 if r.get('正式单板原生目录'):r.setdefault('正式单板原生目录历史',[]).append(copy.deepcopy(r['正式单板原生目录']))
 r['正式单板原生目录']=formal
 session=None
 def invoke(code):return d.cli(EXE,'invoke','--session',session,'--ext-uuid','eda','--timeout','60000','--code',code)['value']
 try:
  session=d.cli(EXE,'open','--path',entry.as_posix(),'--headless','true')['value']['sessionId'];d.wait_for_project(invoke)
  pages=invoke('return await eda.dmt_Schematic.getAllSchematicPagesInfo();')
  assert len(pages)==1 and pages[0]['name']==inp['首页'];d.open_document(invoke,pages[0]['uuid'])
  titles=invoke('return (await eda.sch_PrimitiveText.getAll()).map(t=>t.getState_Content());')
  assert [t for t in titles if '整板原理图' in t]==[clean_title],('正式标题仍重复',titles)
  formal['实际公开属性重复NET显示修正']=hide_duplicate_net_captions(invoke,native_duplicate_caption_targets(entry.parent))
  assert invoke('return await eda.sch_Document.save();') is True
  d.cli(EXE,'session','close','--session',session,'--destroy');session=None
  session=d.cli(EXE,'open','--path',entry.as_posix(),'--headless','true')['value']['sessionId'];d.wait_for_project(invoke)
  pages=invoke('return await eda.dmt_Schematic.getAllSchematicPagesInfo();');assert len(pages)==1
  d.open_document(invoke,pages[0]['uuid'])
  titles=invoke('return (await eda.sch_PrimitiveText.getAll()).map(t=>t.getState_Content());')
  assert [t for t in titles if '整板原理图' in t]==[clean_title],('标题清理未保存',titles)
  formal['显示修正官方保存关闭独立重开']=True
  formal['实际重复NET独立重开核对']=verify_duplicate_net_captions(invoke,formal['实际公开属性重复NET显示修正']['attributes'])
  exported=invoke('const f=await eda.sys_FileManager.getProjectFile("正式结构入口回读",undefined,"epro2");const a=new Uint8Array(await f.arrayBuffer());let s="";for(let i=0;i<a.length;i+=32768)s+=String.fromCharCode(...a.subarray(i,i+32768));return {size:f.size,data:btoa(s)};')
  payload=base64.b64decode(exported['data'],validate=True);assert len(payload)==exported['size']
  path=out/'正式结构入口官方回读.epro2';write_exclusive(path,payload)
  graph=verify_current_graph(c,inp,path)
  svg=invoke('const f=await eda.sch_ManufactureData.getSvgFile("正式单页结构");return f?await f.text():null;')
  assert svg and '<svg' in svg;svgpath,svghash=save_export_text(out,'正式单页结构.svg',svg)
  formal.update(实际入口独立重开=True,实际入口逐脚BOM回读=graph,
   回读文件=str(path.relative_to(ROOT)),回读SHA256=sha(path),官方SVG=str(svgpath.relative_to(ROOT)),SVG_SHA256=svghash)
  erc=invoke(d.ERC_CODE);formal['修正后原始ERC']=erc
  formal['ERC通过']=not any(item.get('count',1) for item in erc['summary'])
  formal['有效官方网表']=False
  net_results={}
  if record.get('未绑定板上器件'):
   formal['官方网表未执行']={'状态':'NOT_RUN_KNOWN_ONBOARD_FOOTPRINT_GAPS',
    '本版缺封装板上位号':record['未绑定板上器件'],
    '原因':'已知真实板上封装缺口；不重复已知失败导出，不修改板上归属以绕过前检。'}
  net_formats=() if record.get('未绑定板上器件') else (('Protel2','ALTIUM_DESIGNER','.net',verify_protel2),('JLCEDA_PRO','JLCEDA_PRO','.enet',verify_jlceda))
  for kind,enum,suffix,checker in net_formats:
   reply=official_netlist_text(invoke,'正式单页结构网表',enum)
   if reply.get('text'):
    netpath,nethash=save_export_text(out,'正式单页结构-'+kind+suffix,reply['text'])
    try:
     check=checker(reply['text'],inp)
     net_results[kind]={'状态':check['status'],'文件':str(netpath.relative_to(ROOT)),'SHA256':nethash,'全量核对':check}
     formal['有效官方网表']|=check['status']=='PASS'
    except Exception as error:net_results[kind]={'状态':'FAIL_CONTENT','文件':str(netpath.relative_to(ROOT)),'SHA256':nethash,'错误':str(error)}
   else:net_results[kind]={'状态':'FAIL_NO_TEXT','返回':reply}
  formal['修正后官方网表']=net_results
  record.update(官方重开全量逐脚BOM=graph,官方重开交换文件=str(path.relative_to(ROOT)),官方重开交换SHA256=sha(path),
   官方ERC结果=erc,ERC通过=formal['ERC通过'],有效官方网表=formal['有效官方网表'],
   正式纳入标志同源一致=True,正式标题唯一=True,本次正式修正工具SHA256=c['tool_sha'])
 except Exception as error:
  formal['入口验收失败']=type(error).__name__+': '+str(error);raise
 finally:
  if session:d.cli(EXE,'session','close','--session',session,'--destroy')
  formal['正式入口重开后目录SHA256']=manifest(target)
  formal['逐板版本适用']=current()
  record['正式工程未覆盖_候选阶段历史值']=record.get('正式工程未覆盖')
  record['正式工程未覆盖']=False;record['正式工程入口']=formal['入口']
  update(c,r)
 assert formal['实际入口独立重开'] and current()
 print(dump({'正式入口':formal['入口'],'单原理图单页':True,'实际入口逐脚BOM':graph['actual_component_refs'],
  '有效官方网表':formal['有效官方网表'],'ERC通过':formal['ERC通过'],'整板放行':False}),flush=True)

def promote_structured_candidate(c):
 """保全旧入口后交付已保存的完整单页结构；ERC/图面缺口保持独立。"""
 e4=bool(c.get('e4_stable'))
 pd=bool(c.get('pd_stable')) and c['board']=='配电'
 versioned=e4 or pd
 assert c['board']=='外充板' or pd or (e4 and c['board']=='FOC' and c.get('physical_board') in ('驱动主板','中央稳压模块','辅助电源板'))
 result=validation_result(c);record=result['结构图面候选']
 assert record['板源文件SHA256']==c['hashes'] and record['页数']==1
 assert record['官方编辑保存独立重开'] and record['官方重开全量逐脚BOM']
 assert record['有效官方网表'] and record['官方PCB网表读取']['状态']=='PASS'
 if versioned:
  assert all(sha(c['live_base']/f)==h for f,h in c['hashes'].items()),'作者活源已改变，不能发布旧包'
  assert not record.get('未绑定板上器件')
  assert record.get('视觉验收')==('PASS_SCOPED_INDEPENDENT_SINGLE_SHEET_TRACEABILITY' if pd else 'PASS_SCOPED_READABLE_TRACEABLE')
  assert record.get('ERC通过') or record.get('ERC分类',{}).get('状态') in (
   'PASS_SCOPED_OFFBOARD_EMPTY_FOOTPRINT_CAUSAL_RULE_EXCEPTION',
   'PASS_SCOPED_OFFBOARD_EMPTY_FOOTPRINT_PERSISTED_CAUSAL_RULE_EXCEPTION',
   'PASS_SCOPED_OFFBOARD_FOOTPRINT_AND_FOUR_EXTERNAL_SINGLE_PIN_WARN_CAUSAL_EXCEPTION')
  accepted=record.get('独立原生验收',{})
  if pd:
   assert record.get('ERC通过') or record.get('ERC分类',{}).get('状态')=='PASS_SCOPED_OFFBOARD_EMPTY_FOOTPRINT_CAUSAL_RULE_EXCEPTION'
   prior=result.get('独立原生与图面接受',{})
   assert prior.get('状态')=='PASS_SCOPED_NATIVE_CANDIDATE_AND_SINGLE_SHEET_TRACEABILITY'
   assert prior.get('原生四文件SHA256')==record['候选完整目录文件SHA256']
   common=result.get('正式E4共同合同关联',{})
   assert common.get('实际标记')=='R2_FROZEN' and common.get('schema')=='0xE4' and common.get('revision')==2026100602
   assert common.get('common_SHA256')=='930303a4518f7900b5a2f3beaf00c666636cd2d59ff22ea020579533ef76cea8'
   accepted={'接受':True,'完整目录SHA256':prior['原生四文件SHA256'],'既有独立接受':copy.deepcopy(prior),'共同合同关联':copy.deepcopy(common)}
  assert accepted.get('接受') is True and accepted.get('完整目录SHA256')==record['候选完整目录文件SHA256'],'须有当前完整原生包独立验收'
 else:
  assert record.get('视觉验收')=='PARTIAL_RENDERED_REVIEW','须有真实图面阅读，不以静态断言代替'
  assert record.get('ERC分类',{}).get('保留原始ERC失败'),'不得因格式交付消除ERC缺口'
 d=module('原理图交付');inp=read(candidate_path(c).parent/'结构预览输入.json')
 source_entry=ROOT/record['候选完整eprj3目录']['工程索引'];origin=source_entry.parent.resolve()
 manifest=record['候选完整目录文件SHA256']
 file_manifest=lambda folder:{p.relative_to(folder).as_posix():sha(p) for p in folder.rglob('*') if p.is_file()}
 assert file_manifest(origin)==manifest and len(manifest)==4
 net=record['官方PCB网表读取'];assert sha(ROOT/net['文件'])==net['SHA256']
 physical='配电板' if pd else c.get('physical_board')
 target=(c['live_base']/'原生工程'/physical/('E4-2026100602-'+c['digest'][:12])).resolve() if versioned else (c['live_base']/'外充板/原生候选/单页完整工程').resolve()
 boundary=c['live_base']/'原生工程'/physical if versioned else c['live_base']/'外充板'
 assert origin.is_relative_to(CACHE.resolve()) and target.is_relative_to(boundary.resolve())
 assert not [s for s in d.cli(EXE,'session','list')['value'] if s.get('status') not in ('closed','destroyed')]
 out=new_export_dir(origin.parent,'正式结构交付') if versioned else origin.parent/'正式结构交付';out.mkdir(exist_ok=True)
 if target.exists() and file_manifest(target)!=manifest:
  assert not versioned,'E4正式目标已有不同字节，停止；不覆盖或移动'
  old=file_manifest(target);assert len(old)==4 and sum(n.endswith('.eprj3') for n in old)==1
  backup=out/'替换前完整工程';assert not backup.exists(),'旧入口保全目标存在，停止移动'
  assert backup.resolve().is_relative_to(CACHE.resolve())
  # Exact, narrow target only; move the complete old folder recoverably.
  shutil.move(str(target),str(backup));assert file_manifest(backup)==old
  record['旧入口保全']={'目录':str(backup.relative_to(ROOT)),'完整目录文件SHA256':old,'可恢复':True}
 if not target.exists():shutil.copytree(origin,target)
 assert file_manifest(target)==manifest
 entry=target/source_entry.name;structure=d.project_documents(entry)
 index=read(entry);assert all(len(index['profile'][k])==1 for k in ('boards','schematics','sheets'))
 formal={'入口':str(entry.relative_to(ROOT)),'对应源文件SHA256':c['hashes'],
  '分板输入SHA256':c.get('split_input_sha256'),'稳定输入SHA256':c.get('stable_manifest_sha'),
  '逐板版本适用':record.get('逐板版本适用'),
  '原始构建板源文件SHA256':record.get('原始构建板源文件SHA256'),
  '完整目录与已重开验证副本逐字节一致':True,
  '磁盘结构':structure,'有效官方网表':True,'官方网表文件':net['文件'],'官方网表SHA256':net['SHA256'],
  'ERC通过':record['ERC通过'],'ERC分类':record.get('ERC分类'),'图面视觉验收':record['视觉验收'],
  '范围':'单实体板单原理图单页的完整可编辑目录交付；未宣称ERC、电气、layout或制造放行',
  '实际入口独立重开':False}
 if versioned:
  old_index=read(c['live_base']/CONFIG[c['board']][4]).get('current_delivery_index',{}).get(c.get('physical_board',c['board']))
  formal['旧正式入口保留']=copy.deepcopy(old_index)
 result['正式单板原生目录']=formal
 if not versioned:update(c,result)
 session=None
 def invoke(code):return d.cli(EXE,'invoke','--session',session,'--ext-uuid','eda','--timeout','60000','--code',code)['value']
 try:
  session=d.cli(EXE,'open','--path',entry.as_posix(),'--headless','true')['value']['sessionId']
  d.wait_for_project(invoke);pages=invoke('return await eda.dmt_Schematic.getAllSchematicPagesInfo();')
  assert len(pages)==1 and pages[0]['name']==inp['首页'];d.open_document(invoke,pages[0]['uuid'])
  exported=invoke('const f=await eda.sys_FileManager.getProjectFile("正式结构入口回读",undefined,"epro2");const a=new Uint8Array(await f.arrayBuffer());let s="";for(let i=0;i<a.length;i+=32768)s+=String.fromCharCode(...a.subarray(i,i+32768));return {size:f.size,data:btoa(s)};')
  payload=base64.b64decode(exported['data'],validate=True);assert len(payload)==exported['size']
  path=out/'正式结构入口官方回读.epro2';write_exclusive(path,payload)
  graph=verify_current_graph(c,inp,path);erc=invoke(d.ERC_CODE)
  formal.update(实际入口独立重开=True,实际入口逐脚BOM回读=graph,
   回读文件=str(path.relative_to(ROOT)),回读SHA256=sha(path),实际入口原始ERC=erc)
  assert erc['summary']==record['官方ERC结果']['summary'],'正式入口ERC与候选发生变化'
  if versioned:
   svg=invoke('const f=await eda.sch_ManufactureData.getSvgFile("正式结构入口图面");return f?await f.text():null;')
   assert svg and '<svg' in svg
   svgpath,h=save_export_text(out,'正式结构入口图面.svg',svg)
   display=compare_official_svg_display(ROOT/record['官方SVG'],svgpath)
   assert display['状态']=='PASS_DISPLAY_IDENTICAL','实际正式图面不同，须重新阅读；不沿用候选'
   formal.update(官方SVG=str(svgpath.relative_to(ROOT)),SVG_SHA256=h,
    实际正式图面阅读={'实际入口导出SVG显示等价性':display,'已实际阅读图面证据':record['图面实际阅读核对'],
    '复用范围':'功能区及主功率链可读可追踪，未变图面不重验'},独立原生验收=accepted,
    正式入口SVG显示等价独立重开=True)
 finally:
  if session:d.cli(EXE,'session','close','--session',session,'--destroy')
  formal['正式入口重开后目录SHA256']=file_manifest(target)
  if not versioned:update(c,result)
 assert formal['实际入口独立重开'] and file_manifest(target)==manifest
 record['正式工程未覆盖_候选阶段历史值']=record.get('正式工程未覆盖')
 record['正式工程未覆盖']=bool(versioned)
 if versioned:record['新版本正式入口已交付_旧入口文件未覆盖']=True
 record['正式工程入口']=formal['入口']
 update(c,result)
 print(dump({'正式入口':formal['入口'],'独立重开':formal['实际入口独立重开'],
  '有效官方网表':True,'ERC原始失败保留':True,'图面视觉验收':formal['图面视觉验收']}),flush=True)


def diagnose_external_erc(c):
 """一次隔离且不保存的公开属性因果诊断，不为板外件指定制造封装。"""
 candidate_fp_causality=bool(c.get('candidate_fp_causality'))
 assert c['board'] in ('外充板','BMS板','配电') or (c['board']=='FOC' and c.get('physical_board') in ('辅助电源板','驱动主板','中央稳压模块'))
 if c['board']=='BMS板':
  assert c.get('revision')=='RevY-e79a970cac6f' and len(c['parts'])==877
  assert {p['ref'] for p in c['parts'] if not p['onboard']}==({'F_MAIN','F_BAL_SEC_LOW','F_BAL_SEC_TOP','F_AUX','F_CHG_OUT'}|{f'F_BAL{n}' for n in range(1,11)}|{f'NTC_{n}' for n in ('CELL1','CELL2','CELL3','CHG','DSG','SHUNT')}),'仅冻结877真实板外21位号可诊断'
 if c['board']=='FOC' and c.get('e4_stable'):
  assert c.get('candidate_only') and c.get('physical_board') in ('辅助电源板','驱动主板','中央稳压模块')
  assert all(p['board']==c['physical_board'] for p in c['parts'])
  external=[p for p in c['parts'] if not p['onboard']]
  assert (all(p.get('installation')=='板外' and p.get('pcb_footprint_required') is False and
   p.get('external_boundary',{}).get('pcb_pad_numbers_claimed') is False for p in external)), '仅允许稳定源明确声明板外且不声称PCB焊盘的器件进入隔离ERC归因'
 elif c['board']=='FOC' and c.get('physical_board') in ('驱动主板','中央稳压模块'):
  assert c.get('revision')=='RevZ-197103dc101a','只诊断已冻结且正式消费的RevZ实体板'
  assert all(p['board']==c['physical_board'] for p in c['parts'])
  assert len([p for p in c['parts'] if not p['onboard']])=={'驱动主板':35,'中央稳压模块':60}[c['physical_board']]
 if c['board']=='配电' and not c.get('candidate_only'):
  assert c['digest'] in ('5273659b78950f54d72bcf018fc64eeca8d8ac309c64ce7315d39827465b4fb3',
   '3e3b44b2029f8ebe3ab3a68e5365672b742f064fb4475fcac479b9ad94ec6abf')
  external={p['ref'] for p in c['parts'] if not p['onboard']}
  assert external=={f'R_{tag}_HS_LIMIT{n}' for tag in ('AUX','P5','P21') for n in (1,2)}|{'J_LIGHT','F_LIGHT','F_GIMBAL','J_GIMBAL'},'仅本版真实板外边界可诊断，不改板上安装归属'
 r=validation_result(c);record=r['结构图面候选']
 if c.get('candidate_only'):
  assert (c['board']=='配电' or c.get('e4_stable')) and record['板源文件SHA256']==c['hashes']
  assert record['官方编辑保存独立重开'] and record['官方重开全量逐脚BOM']
  formal={'入口':record['候选完整eprj3目录']['工程索引'],
   '正式入口重开后目录SHA256':record['候选完整目录文件SHA256']}
 else:formal=r['正式单板原生目录']
 board=c.get('physical_board',c['board']);livepath=c['live_base']/CONFIG[c['board']][4]
 previous_index=copy.deepcopy(read(livepath).get('current_delivery_index',{}).get(board,{}))
 entry=ROOT/formal['入口'];original=entry.parent.resolve()
 manifest=lambda folder:{p.relative_to(folder).as_posix():sha(p) for p in folder.rglob('*') if p.is_file()}
 before=manifest(original);assert before==formal['正式入口重开后目录SHA256']
 d=module('原理图交付');assert not [s for s in d.cli(EXE,'session','list')['value'] if s.get('status') not in ('closed','destroyed')]
 original_file_bytes={rel:(original/rel).read_bytes() for rel in before} if candidate_fp_causality else None
 if candidate_fp_causality:
  assert c.get('e4_stable') and c.get('physical_board')=='中央稳压模块' and c.get('candidate_only')
  prior=record.get('ERC明细探针历史',[]);assert prior
  prior_entry=ROOT/prior[-1]['隔离副本工程索引'];temporary=prior_entry.parent.resolve()
  assert temporary.is_relative_to(CACHE.resolve()) and prior_entry.name==entry.name
  assert manifest(temporary)==before==prior[-1]['隔离副本初始目录SHA256']
  project_manifest=read(temporary/entry.name)
  expected_project_docs={
   'board_uuid':next(iter(project_manifest['profile']['boards'])),
   'schematic_uuid':next(iter(project_manifest['profile']['schematics'])),
   'sheet_uuid':next(iter(project_manifest['profile']['sheets']))}
  assert project_manifest['profile']['boards'][expected_project_docs['board_uuid']]['uuid']==expected_project_docs['board_uuid']
  assert project_manifest['profile']['schematics'][expected_project_docs['schematic_uuid']]['uuid']==expected_project_docs['schematic_uuid']
  assert project_manifest['profile']['sheets'][expected_project_docs['sheet_uuid']]['uuid']==expected_project_docs['sheet_uuid']
  out=temporary.parent
 else:
  out=new_export_dir(c.get('build_root',c['base']),'本版ERC受控分类')
  temporary=out/'未保存ERC归因临时工程';assert not temporary.exists()
  shutil.copytree(original,temporary);assert manifest(temporary)==before
 attrs=collections.defaultdict(dict);fps={};fp_rows={};device_footprints={};kind=None;uid=None
 for _,(a,b) in d.records(next(original.rglob('*.esch2')).read_text(encoding='utf8')):
  if a['type']=='DOCHEAD':kind=b['docType'];uid=b['uuid']
  if kind=='FOOTPRINT':fp_rows.setdefault(uid,[]).append((a,b))
  if kind=='DEVICE' and a['type']=='META':device_footprints[uid]=b.get('attributes',{}).get('Footprint','')
  if kind=='FOOTPRINT' and a['type']=='PAD':fps.setdefault(uid,set()).add(b['num'])
  elif kind=='SCH_PAGE' and a['type']=='ATTR':attrs[b['parentId']][b['key']]=b['value']
 refs=tuple(p['ref'] for p in c['parts'] if not p['onboard']);targets=[]
 fixtures=[]
 for ref in refs:
  cid=next(k for k,v in attrs.items() if v.get('Designator')==ref)
  part=next(p for p in c['parts'] if p['ref']==ref)
  if c.get('candidate_only') and (attrs[cid].get('Footprint') or device_footprints.get(attrs[cid].get('Device'))):continue
  assert attrs[cid]['Convert to PCB']=='no' and not attrs[cid].get('Footprint')
  match=next((k for k,v in fps.items() if v==set(part['pins'])),None)
  if match is None:
   # A1/A2 contacts and one-terminal shield bonds need exact diagnostic
   # identities. Clone a local document only into the isolated copy; its
   # geometry is explicitly NOT a selected/manufacturing footprint.
   donor=next(k for k,v in fps.items() if len(v)>=len(part['pins']))
   match=hashlib.sha256(('UNSAVED_ERC_ONLY|'+ref+'|'+c['digest']).encode()).hexdigest()[:16]
   numbers=iter(sorted(part['pins']));pads=0;cloned=[]
   for a,b in copy.deepcopy(fp_rows[donor]):
    if a['type']=='DOCHEAD':b['uuid']=match
    elif a['type']=='META':b['title']='DIAGNOSTIC_ONLY_NOT_MANUFACTURING_'+ref
    elif a['type']=='PAD':
     if pads==len(part['pins']):continue
     b['num']=next(numbers);pads+=1
    cloned.append((a,b))
   assert pads==len(part['pins'])
   fixtures.extend(cloned);fps[match]=set(part['pins'])
  targets.append({'ref':ref,'component':cid,'temporaryFootprint':match,'physicalPadCount':len(fps[match]),
   'padNumbers':sorted(part['pins']),
   'temporaryOnly':True,'manufacturingBinding':False,'diagnosticFixture':match not in fp_rows})
 if candidate_fp_causality:
  onboard={p['ref'] for p in c['parts'] if p['onboard']};external={p['ref'] for p in c['parts'] if not p['onboard']}
  full_fp=record['全量交换逐脚BOM']['full_footprint_readback']
  assert len(c['parts'])==1091 and len(onboard)==967 and len(external)==124
  assert all(p.get('installation')=='板外' and p.get('pcb_footprint_required') is False for p in c['parts'] if not p['onboard'])
  assert full_fp['bound_count']==967 and {x['ref'] for x in full_fp['approved_shared_refs']}==onboard
  assert set(full_fp['missing_refs'])==external
  assert len(targets)==124 and {t['ref'] for t in targets}==external
 if fixtures:
  isolated=next(temporary.rglob('*.esch2'))
  original_rows=[row for _,row in d.records(isolated.read_text(encoding='utf8'))]
  page_heads=[i for i,(a,b) in enumerate(original_rows) if a['type']=='DOCHEAD' and b['docType']=='SCH_PAGE']
  assert len(page_heads)==1
  split=page_heads[0];assert not any(a['type']=='DOCHEAD' for a,b in original_rows[split+1:])
  # Folder schematics use [library documents..., SCH_PAGE]. Appending a
  # footprint after the page loads an empty editor even with valid JSON.
  payload='\n'.join(d.record_json(a)+'||'+d.record_json(b)+'|' for a,b in original_rows[:split]+fixtures+original_rows[split:])+'\n'
  isolated.write_text(payload,encoding='utf8',newline='\n')
  parsed=[row for _,row in d.records(isolated.read_text(encoding='utf8'))]
  heads=[b['uuid'] for a,b in parsed if a['type']=='DOCHEAD' and b['docType']=='FOOTPRINT']
  assert all(heads.count(t['temporaryFootprint'])==1 for t in targets if t['diagnosticFixture'])
  assert [b['docType'] for a,b in parsed if a['type']=='DOCHEAD'][-1]=='SCH_PAGE'
 refs=tuple(t['ref'] for t in targets)
 evidence={'范围':'隔离副本临时FP因果对照；PCB归属保持板外，诊断封装绝非制造封装',
  '源文件SHA256':c['hashes'],'读取工具SHA256':TOOL_SHA,
  '临时对象':targets,'隔离诊断专用文档数':sum(t['diagnosticFixture'] for t in targets),
  '正式目录SHA256_前':before,'临时目录':str(temporary.relative_to(ROOT))}
 source_before={name:sha(Path(c.get('source_paths',{}).get(name,c['live_base']/name))) for name in c['hashes']}
 if candidate_fp_causality:
  assert source_before==c['hashes']=={
   '设计数据.py':'9f9d47ce868951424e08e07f2265b46420dfff7abfc824ce3f50129b35afabb3',
   '中央稳压模块.py':'90b2c6e6fd4552a7acfdb0981ddd0b7456b14e0c7851db1662de142428075c89'}
  evidence['源文件SHA256_前']=source_before
 session=None
 def invoke(code):return d.cli(EXE,'invoke','--session',session,'--ext-uuid','eda','--timeout','60000','--code',code)['value']
 def invoke_targets(body):
  # Windows CreateProcess has a command-length ceiling. Read/write the same
  # frozen targets in bounded batches instead of passing 164 full rows at once.
  values=[]
  for start in range(0,len(targets),32):values.extend(invoke('const targets='+dump(targets[start:start+32])+';'+body))
  return values
 def loaded_page(page_uuid):
  expected={p['ref'] for p in c['parts']}
  for _ in range(20):
   state=invoke('return {page:(await eda.dmt_Schematic.getCurrentSchematicPageInfo())?.uuid,parts:(await eda.sch_PrimitiveComponent.getAll("part")).map(c=>({ref:c.getState_Designator(),id:c.getState_PrimitiveId(),addIntoPcb:c.getState_AddIntoPcb()}))};')
   if state.get('page')==page_uuid and {p['ref'] for p in state['parts']}==expected:return state
   time.sleep(.5)
  raise AssertionError(('ERC诊断图页未实际载入',state))
 def record_open_target(label,requested_entry,pages):
  page_uuid=pages[0]['uuid'] if pages else None
  project=invoke('const p=await eda.dmt_Project.getCurrentProjectInfo();return p?{uuid:p.uuid,friendlyName:p.friendlyName,name:p.name,data:(p.data||[]).map(x=>({itemType:x.itemType,uuid:x.uuid,name:x.name,parentProjectUuid:x.parentProjectUuid,page:(x.page||[]).map(y=>({uuid:y.uuid,name:y.name}))}))}:null;')
  evidence[label]={'requested_session_path':str(requested_entry.resolve()),'session_id':session,
   'project':project,'page_uuids':[p.get('uuid') for p in pages],
   'page_names':[p.get('name') for p in pages]}
  if candidate_fp_causality:
   assert page_uuid==expected_project_docs['sheet_uuid'],'隔离session页面UUID不符'
   assert project and project.get('uuid') and project.get('friendlyName')==project_manifest['name'], '隔离session工程名/工程UUID不符'
 offboard_refs=tuple(t['ref'] for t in targets)
 def assignment_summary():
  return invoke('const off=new Set('+dump(offboard_refs)+');const cs=await eda.sch_PrimitiveComponent.getAll("part");const out={count:cs.length,boardOnResolved:0,boardOnInvalid:[],offboardBlank:0,offboardInvalid:[]};for(const c of cs){const ref=c.getState_Designator(),fp=c.getState_Footprint(),add=c.getState_AddIntoPcb();if(off.has(ref)){if(add===false&&!fp)out.offboardBlank++;else out.offboardInvalid.push({ref,addIntoPcb:add,footprint:fp||null});}else{if(add===true&&fp?.uuid&&fp?.libraryUuid)out.boardOnResolved++;else out.boardOnInvalid.push({ref,addIntoPcb:add,footprint:fp||null});}}return out;')
 def erc_detail():
  return invoke('try{const raw=await eda.sch_Drc.check(true,false,true);return {type:Array.isArray(raw)?"array":typeof raw,raw};}catch(error){return {error:String(error)};}')
 def erc_boolean():
  return invoke('try{const raw=await eda.sch_Drc.check(true,false,false);return {type:typeof raw,raw};}catch(error){return {error:String(error)};}')
 try:
  requested_entry=(temporary/entry.name) if candidate_fp_causality else (temporary/entry.name)
  opened=d.cli(EXE,'open','--path',requested_entry.as_posix(),'--headless','true')['value']
  session=opened['sessionId']
  d.wait_for_project(invoke);pages=invoke('return await eda.dmt_Schematic.getAllSchematicPagesInfo();')
  assert len(pages)==1;d.open_document(invoke,pages[0]['uuid'])
  if candidate_fp_causality:record_open_target('临时属性变更session目标',requested_entry,pages)
  evidence['诊断实际载入图页']=loaded_page(pages[0]['uuid'])
  if candidate_fp_causality:
   evidence['候选封装基线API回读']=assignment_summary()
   assert evidence['候选封装基线API回读']['count']==1091
   assert evidence['候选封装基线API回读']['boardOnResolved']==967 and not evidence['候选封装基线API回读']['boardOnInvalid']
   assert evidence['候选封装基线API回读']['offboardBlank']==124 and not evidence['候选封装基线API回读']['offboardInvalid']
   evidence['基线ERC详细返回']=erc_detail();evidence['基线ERC原始布尔']=erc_boolean()
   evidence['基线ERC']={'passed':evidence['基线ERC原始布尔'].get('raw'),'summary':evidence['基线ERC详细返回'].get('raw')}
  else:
   evidence['基线ERC']=invoke(d.ERC_CODE)
   if c.get('diagnose_verbose'):
    evidence['基线公开详细重载实际返回']=invoke('const result=await eda.sch_Drc.check(true,false,true);return {jsType:typeof result,isArray:Array.isArray(result),result};')
  assignment_code='''const out=[];async function pinState(c){return (await c.getAllPins()).map(p=>({number:p.getState_PinNumber(),name:p.getState_PinName(),noConnected:p.getState_NoConnected(),x:p.getState_X(),y:p.getState_Y(),rotation:p.getState_Rotation()})).sort((a,b)=>a.number.localeCompare(b.number));}function noFootprint(p){const q={...(p||{})};delete q.Footprint;return q;}function padNumbers(source){const nums=[];for(const raw of (source||"").split("\\n")){const line=raw.trim(),i=line.indexOf("||");if(i<0)continue;const head=JSON.parse(line.slice(0,i));if(head.type!=="PAD")continue;const body=line.slice(i+2).replace(/\\|$/,"");nums.push(JSON.parse(body).num);}return nums.sort();}for(const t of targets){const before=await eda.sch_PrimitiveComponent.get(t.component);if(!before||before.getState_AddIntoPcb()!==false||before.getState_Footprint())throw new Error("offboard baseline changed "+t.ref);const propsBefore=before.getState_OtherProperty()||{},pinsBefore=await pinState(before),bomBefore=before.getState_AddIntoBom();if(JSON.stringify(pinsBefore.map(p=>p.number))!==JSON.stringify(t.padNumbers))throw new Error("symbol pin mismatch "+t.ref);await eda.sch_PrimitiveComponent.modify(t.component,{otherProperty:{...propsBefore,Footprint:t.temporaryFootprint}});const after=await eda.sch_PrimitiveComponent.get(t.component),assoc=after?.getState_Footprint(),item=assoc&&await eda.lib_Footprint.get(assoc.uuid,assoc.libraryUuid),source=assoc&&await eda.lib_Footprint.getDocumentSource(assoc.uuid,assoc.libraryUuid),pads=padNumbers(source),pinsAfter=await pinState(after),propsAfter=after.getState_OtherProperty()||{},valid=!!(assoc?.uuid===t.temporaryFootprint&&assoc?.libraryUuid&&item?.uuid===assoc.uuid&&item?.libraryUuid===assoc.libraryUuid&&source&&JSON.stringify(pads)===JSON.stringify(t.padNumbers));out.push({...t,apiFootprint:assoc||null,libraryItem:item?{uuid:item.uuid,libraryUuid:item.libraryUuid,name:item.name}:null,documentSourceAvailable:!!source,resolvedPadNumbers:pads,symbolPinReadbackUnchanged:JSON.stringify(pinsBefore)===JSON.stringify(pinsAfter),symbolPinNumbersMatch:JSON.stringify(pinsAfter.map(p=>p.number))===JSON.stringify(t.padNumbers),otherPropertiesExceptFootprintUnchanged:JSON.stringify(noFootprint(propsBefore))===JSON.stringify(noFootprint(propsAfter)),addIntoPcb:after.getState_AddIntoPcb(),addIntoBom:after.getState_AddIntoBom(),apiAssignmentValid:valid});if(!valid||!out[out.length-1].symbolPinReadbackUnchanged||!out[out.length-1].otherPropertiesExceptFootprintUnchanged||out[out.length-1].addIntoPcb!==false||out[out.length-1].addIntoBom!==bomBefore)throw new Error("API assignment not valid or changed non-FP state "+t.ref);}return out;'''
  if candidate_fp_causality:
   evidence['临时属性变更']=invoke_targets(assignment_code)
   assert len(evidence['临时属性变更'])==124 and all(t.get('apiAssignmentValid') and t.get('addIntoPcb') is False and t.get('symbolPinReadbackUnchanged') and t.get('otherPropertiesExceptFootprintUnchanged') for t in evidence['临时属性变更']),'公开API未解析有效脚号兼容封装，或非封装状态发生变化'
   evidence['临时FP官方保存']=invoke('return await eda.sch_Document.save();')
   assert evidence['临时FP官方保存'] is True,'隔离候选临时FP保存失败'
   time.sleep(9);evidence['临时FP保存后拓扑稳定等待秒']=9
   evidence['临时FP后封装API汇总']=assignment_summary()
   assert evidence['临时FP后封装API汇总']['count']==1091
   assert evidence['临时FP后封装API汇总']['boardOnResolved']==967 and not evidence['临时FP后封装API汇总']['boardOnInvalid']
   assert len(evidence['临时FP后封装API汇总']['offboardInvalid'])==124
   assert {x['ref'] for x in evidence['临时FP后封装API汇总']['offboardInvalid']}==set(offboard_refs)
   assert all(x['addIntoPcb'] is False and x['footprint'] for x in evidence['临时FP后封装API汇总']['offboardInvalid'])
   evidence['仅临时FP后ERC详细返回']=erc_detail();evidence['仅临时FP后ERC原始布尔']=erc_boolean()
   evidence['仅临时FP后ERC']={'passed':evidence['仅临时FP后ERC原始布尔'].get('raw'),'summary':evidence['仅临时FP后ERC详细返回'].get('raw')}
   evidence['临时属性会话恢复']=invoke_targets('const out=[];for(const t of targets){const c=await eda.sch_PrimitiveComponent.get(t.component);await eda.sch_PrimitiveComponent.modify(t.component,{otherProperty:{...(c.getState_OtherProperty()||{}),Footprint:""}});const q=await eda.sch_PrimitiveComponent.get(t.component);out.push({ref:t.ref,footprint:q.getState_Footprint()||null,addIntoPcb:q.getState_AddIntoPcb()});}return out;')
   assert len(evidence['临时属性会话恢复'])==124 and all(t.get('footprint') is None and t.get('addIntoPcb') is False for t in evidence['临时属性会话恢复'])
  else:
   evidence['临时属性变更']=invoke_targets('const out=[];for(const t of targets){const c=await eda.sch_PrimitiveComponent.get(t.component);if(!c||c.getState_AddIntoPcb()!==false)throw new Error("板外范围变化");const before=c.getState_OtherProperty()||{};await eda.sch_PrimitiveComponent.modify(t.component,{otherProperty:{...before,Footprint:t.temporaryFootprint}});const attrs=await eda.sch_PrimitiveAttribute.getAll(t.component);out.push({...t,actualFootprint:attrs.find(a=>a.getState_Key()==="Footprint")?.getState_Value(),addIntoPcb:(await eda.sch_PrimitiveComponent.get(t.component)).getState_AddIntoPcb()});}return out;')
   assert all(t.get('actualFootprint')==t['temporaryFootprint'] and t['addIntoPcb'] is False for t in evidence['临时属性变更']),'公开属性临时写入未实际生效；停止，不换私有接口'
   time.sleep(5);evidence['仅临时FP后ERC']=invoke(d.ERC_CODE)
   if c.get('diagnose_verbose'):
    evidence['临时FP后公开详细重载实际返回']=invoke('const result=await eda.sch_Drc.check(true,false,true);return {jsType:typeof result,isArray:Array.isArray(result),result};')
  if c.get('diagnose_public_log'):
   evidence['公开UI检查与公开日志']=invoke('const passed=await eda.sch_Drc.check(true,true,false);return {passed,logs:await eda.sys_Log.sort()};')
  if c.get('diagnose_nc'):
   assert c.get('e4_stable') and c.get('physical_board')=='辅助电源板'
   inp=read(candidate_path(c).parent/'结构预览输入.json')
   expected_nc=inp['NC'];assert len(expected_nc)==13
   evidence['未连接标记单变量目标']=expected_nc
   evidence['未连接标记公开API写入']=invoke('const targets='+dump(expected_nc)+';const cs=await eda.sch_PrimitiveComponent.getAll("part");const out=[];for(const [ref,num] of targets){const c=cs.find(c=>c.getState_Designator()===ref);if(!c)throw new Error("NC目标器件缺失 "+ref);const pins=await c.getAllPins();const p=pins.find(p=>p.getState_PinNumber()===num);if(!p)throw new Error("NC目标脚缺失 "+ref+":"+num);const before=p.getState_NoConnected();const edit=p.toAsync();edit.setState_NoConnected(true);await edit.done();const q=(await c.getAllPins()).find(p=>p.getState_PinNumber()===num);out.push({ref,num,before,after:q.getState_NoConnected()});}return out;')
   assert all(p['after'] is True for p in evidence['未连接标记公开API写入'])
   time.sleep(5);evidence['仅追加源既定NC标记后ERC']=invoke(d.ERC_CODE)
  # Restore empty values before closing, even though the isolated test is never saved.
  evidence['会话属性恢复']=invoke_targets('const out=[];for(const t of targets){const c=await eda.sch_PrimitiveComponent.get(t.component);await eda.sch_PrimitiveComponent.modify(t.component,{otherProperty:{...(c.getState_OtherProperty()||{}),Footprint:""}});const attrs=await eda.sch_PrimitiveAttribute.getAll(t.component);out.push({ref:t.ref,footprint:attrs.find(a=>a.getState_Key()==="Footprint")?.getState_Value(),addIntoPcb:(await eda.sch_PrimitiveComponent.get(t.component)).getState_AddIntoPcb()});}return out;')
  evidence['会话恢复ERC']=invoke(d.ERC_CODE)
 except Exception as error:
  evidence['诊断失败']=type(error).__name__+': '+str(error)
 finally:
  if session:
   try:d.cli(EXE,'session','close','--session',session,'--destroy')
   except Exception as error:evidence['临时会话关闭失败']=str(error)
   session=None
  if candidate_fp_causality:
   try:
    evidence['保存后隔离副本目录SHA256']=manifest(temporary)
    for path in temporary.rglob('*'):
     if path.is_file() and path.relative_to(temporary).as_posix() not in before:
      assert path.resolve().is_relative_to(temporary),'拒绝删除隔离副本目录外文件'
      path.unlink()
    for rel,payload in original_file_bytes.items():
     path=temporary/rel
     assert path.resolve().is_relative_to(temporary),'隔离副本恢复路径越界'
     path.write_bytes(payload)
    evidence['隔离副本字节恢复后SHA256']=manifest(temporary)
    evidence['隔离副本字节已恢复']=evidence['隔离副本字节恢复后SHA256']==before
   except Exception as error:evidence['隔离副本恢复失败']=str(error)
  try:
   sessions_after_first=d.cli(EXE,'session','list')['value']
   evidence['首次隔离会话关闭后活动会话']=[s for s in sessions_after_first if s.get('status') not in ('closed','destroyed')]
   if evidence['首次隔离会话关闭后活动会话']:
    evidence['临时会话关闭失败']=str(evidence.get('临时会话关闭失败',''))+' 活动会话仍存在，拒绝继续打开探针'
  except Exception as error:evidence['首次隔离会话状态读取失败']=str(error)
  evidence['正式目录SHA256_后']=manifest(original)
  assert before==evidence['正式目录SHA256_后'],'隔离诊断污染正式目录'
  if candidate_fp_causality:assert evidence.get('隔离副本字节已恢复'),'临时官方保存后的隔离副本字节未能原样恢复'
 try:
  assert not evidence.get('首次隔离会话关闭后活动会话'),'原探针会话未关闭'
  reopen_entry=(temporary/entry.name) if candidate_fp_causality else entry
  opened=d.cli(EXE,'open','--path',reopen_entry.as_posix(),'--headless','true')['value']
  session=opened['sessionId']
  d.wait_for_project(invoke);pages=invoke('return await eda.dmt_Schematic.getAllSchematicPagesInfo();');d.open_document(invoke,pages[0]['uuid'])
  if candidate_fp_causality:record_open_target('恢复后独立重开session目标',reopen_entry,pages)
  evidence['原目录实际载入图页']=loaded_page(pages[0]['uuid'])
  if candidate_fp_causality:
   evidence['恢复后隔离副本封装API回读']=assignment_summary()
   assert evidence['恢复后隔离副本封装API回读']['count']==1091
   assert evidence['恢复后隔离副本封装API回读']['boardOnResolved']==967 and not evidence['恢复后隔离副本封装API回读']['boardOnInvalid']
   assert evidence['恢复后隔离副本封装API回读']['offboardBlank']==124 and not evidence['恢复后隔离副本封装API回读']['offboardInvalid']
   evidence['恢复后隔离副本ERC详细返回']=erc_detail();evidence['恢复后隔离副本ERC原始布尔']=erc_boolean()
   evidence['恢复后隔离副本ERC']={'passed':evidence['恢复后隔离副本ERC原始布尔'].get('raw'),
    'summary':evidence['恢复后隔离副本ERC详细返回'].get('raw')}
  else:
   evidence['正式原目录独立重开ERC']=invoke(d.ERC_CODE)
   evidence['正式原属性回读']=invoke_targets('const out=[];for(const t of targets){const attrs=await eda.sch_PrimitiveAttribute.getAll(t.component);out.push({ref:t.ref,footprint:attrs.find(a=>a.getState_Key()==="Footprint")?.getState_Value()||"",addIntoPcb:(await eda.sch_PrimitiveComponent.get(t.component)).getState_AddIntoPcb()});}return out;')
   assert all(not t['footprint'] and t['addIntoPcb'] is False for t in evidence['正式原属性回读'])
 except Exception as error:
  evidence['恢复重开核验失败']=type(error).__name__+': '+str(error)
 finally:
  if session:
   try:d.cli(EXE,'session','close','--session',session,'--destroy')
   except Exception as error:evidence['恢复重开会话关闭失败']=str(error)
  try:
   sessions_after_reopen=d.cli(EXE,'session','list')['value']
   evidence['恢复重开后活动会话']=[s for s in sessions_after_reopen if s.get('status') not in ('closed','destroyed')]
  except Exception as error:evidence['恢复重开后会话状态读取失败']=str(error)
  evidence['原目录重开后SHA256']=manifest(original)
  evidence['隔离副本重开后SHA256']=manifest(temporary) if candidate_fp_causality else None
  source_after={name:sha(Path(c.get('source_paths',{}).get(name,c['live_base']/name))) for name in c['hashes']}
  evidence['源文件SHA256_后']=source_after
  assert before==evidence['原目录重开后SHA256']
  if candidate_fp_causality:
   evidence['冻结源SHA保持不变']=source_after==source_before==c['hashes']
   evidence['隔离副本恢复且重开字节一致']=evidence.get('隔离副本字节已恢复') is True and evidence.get('隔离副本重开后SHA256')==before
   formal['正式入口重开后目录SHA256']=evidence['原目录重开后SHA256']
   def fatal_count(result):
    if not isinstance(result,dict) or result.get('type')!='array' or not isinstance(result.get('raw'),list):return None
    return sum(int(item.get('count',1)) for item in result['raw'] if isinstance(item,dict) and item.get('type')=='fatalError')
   baseline_fatal=fatal_count(evidence.get('基线ERC详细返回'))
   temporary_fatal=fatal_count(evidence.get('仅临时FP后ERC详细返回'))
   restored_fatal=fatal_count(evidence.get('恢复后隔离副本ERC详细返回'))
   evidence['fatalError因果计数']={'基线':baseline_fatal,'临时FP后':temporary_fatal,'字节恢复并独立重开后':restored_fatal}
   assigned=evidence.get('临时属性变更',[])
   after_assign=evidence.get('临时FP后封装API汇总',{})
   restored_bool=evidence.get('恢复后隔离副本ERC原始布尔',{}).get('raw')
   classified=(not evidence.get('诊断失败') and not evidence.get('临时会话关闭失败') and not evidence.get('恢复重开会话关闭失败') and
    not evidence.get('隔离副本恢复失败') and not evidence.get('恢复重开后活动会话') and
    not evidence.get('首次隔离会话关闭后活动会话') and not evidence.get('首次隔离会话状态读取失败') and
    not evidence.get('恢复重开核验失败') and not evidence.get('恢复重开后会话状态读取失败') and
    evidence.get('基线ERC原始布尔',{}).get('raw') is False and baseline_fatal==124 and
    evidence.get('仅临时FP后ERC原始布尔',{}).get('raw') is True and temporary_fatal==0 and
    restored_bool is False and restored_fatal==124 and
    len(assigned)==124 and {x.get('ref') for x in assigned}==set(refs) and
    all(x.get('apiAssignmentValid') and x.get('symbolPinNumbersMatch') and x.get('symbolPinReadbackUnchanged') and
     x.get('otherPropertiesExceptFootprintUnchanged') and x.get('addIntoPcb') is False for x in assigned) and
    after_assign.get('count')==1091 and after_assign.get('boardOnResolved')==967 and not after_assign.get('boardOnInvalid') and
    len(after_assign.get('offboardInvalid',[]))==124 and {x['ref'] for x in after_assign.get('offboardInvalid',[])}==set(refs) and
    evidence.get('恢复后隔离副本封装API回读',{}).get('offboardBlank')==124 and
    not evidence.get('恢复后隔离副本封装API回读',{}).get('offboardInvalid') and
    evidence.get('隔离副本恢复且重开字节一致') is True and evidence['隔离副本重开后SHA256']==before and source_after==source_before)
  else:
   formal['正式入口重开后目录SHA256']=evidence['原目录重开后SHA256']
   classified=(not evidence.get('诊断失败') and evidence.get('基线ERC',{}).get('passed') is False and
    evidence.get('仅临时FP后ERC',{}).get('passed') is True and
    evidence.get('正式原目录独立重开ERC',{}).get('passed') is False and
    len(evidence.get('正式原属性回读',[]))==len(targets)>0 and
    all(not t['footprint'] and t['addIntoPcb'] is False for t in evidence.get('正式原属性回读',[])) and
    evidence['原目录重开后SHA256']==before)
  classification={'状态':'PASS_SCOPED_OFFBOARD_EMPTY_FOOTPRINT_CAUSAL_RULE_EXCEPTION' if classified else 'NOT_CLASSIFIED_REMAINING_OFFICIAL_ERC_BLOCK',
   '本版实际位号集合':list(refs),'本版正式文件SHA256':before,'官方详细错误集合可得':False,
   '受控公开属性证据':evidence,'原始官方ERC通过':False,'制造用封装或板外归属修改':False,
   '说明':'只在隔离副本对确切124个板外且pcb_footprint_required=false的器件临时分配针脚编号兼容封装；只有strict=true从fatal124/false到fatal0/true，逐脚/网络与其余属性不变，恢复克隆字节后独立重开回到fatal124/false，方可将本版真实集合标为范围例外。正式原生仍保留raw ERC false。'}
  if record.get('ERC受控归因诊断'):
   record.setdefault('ERC受控归因诊断历史',[]).append(copy.deepcopy(record['ERC受控归因诊断']))
  if formal.get('ERC分类'):
   formal.setdefault('ERC分类历史',[]).append(copy.deepcopy(formal['ERC分类']))
  record['ERC受控归因诊断']=evidence;formal['ERC分类']=classification
  if c.get('candidate_only'):record['ERC分类']=classification
  if candidate_fp_causality:
   record['候选唯一回修待办']={'状态':'PENDING_VISUAL_COMPLETE_REVIEW',
    '唯一事项':'L_SC_P1_POWER、L_SC_P2_POWER、L_SC_PORT_HV、L_SC_PORT_LV 的 winding start/end pin 文本与红色 coil 本体重叠。等待完整36区视觉验收包后一次修图；仅调整文字显示位置或隐藏这4个非极性2-pin器件的冗余pin name，保留pin number、netlabel及全部电气属性。'}
   document=read(c['report']);document['native_validation']['结构图面候选']=record;write(c['report'],document)
  else:update(c,r)
  # Preserve current exact-equivalence source associations on unchanged pages.
  live=read(livepath)
  if previous_index and not c.get('candidate_only'):
   previous_index.update(证据SHA256=sha(c['report']),当前版面ERC分类=classification)
   live['current_delivery_index'][board]=previous_index;write(livepath,live)
 print(dump({'板':board,'受控分类':classification['状态'],'实际板外集合':list(refs),'基线':evidence.get('基线ERC',evidence.get('基线ERC原始布尔')),
  '临时FP后':evidence.get('仅临时FP后ERC',evidence.get('仅临时FP后ERC原始布尔')),
  '恢复':evidence.get('恢复后隔离副本ERC',evidence.get('会话恢复ERC')),'fatalError因果计数':evidence.get('fatalError因果计数'),
  '候选原目录未变':evidence.get('正式目录SHA256_后')==before,'诊断失败':evidence.get('诊断失败')}),flush=True)


def verify_formal_folder(c):
 result=validation_result(c);formal=result['正式单板原生目录'];inp=read(packet(c));d=module('原理图交付')
 index=ROOT/formal['入口'];manifest=result['官方文件夹工程']['完整目录文件SHA256']
 assert {p.relative_to(index.parent).as_posix():sha(p) for p in index.parent.rglob('*') if p.is_file()}==manifest
 assert not [s for s in d.cli(EXE,'session','list')['value'] if s.get('status') not in ('closed','destroyed')]
 out=new_export_dir(CACHE/c['board'],'正式入口回读');session=None
 def invoke(code):return d.cli(EXE,'invoke','--session',session,'--ext-uuid','eda','--timeout','60000','--code',code)['value']
 try:
  session=d.cli(EXE,'open','--path',index.as_posix(),'--headless','true')['value']['sessionId'];d.wait_for_project(invoke)
  pages=invoke('return await eda.dmt_Schematic.getAllSchematicPagesInfo();')
  assert len(pages)==1 and pages[0]['name']==inp['首页'];d.open_document(invoke,pages[0]['uuid'])
  raw=invoke('const f=await eda.sys_FileManager.getProjectFile("正式入口回读",undefined,"epro2");const a=new Uint8Array(await f.arrayBuffer());let s="";for(let i=0;i<a.length;i+=32768)s+=String.fromCharCode(...a.subarray(i,i+32768));return {size:f.size,data:btoa(s)};')
  data=base64.b64decode(raw['data'],validate=True);assert len(data)==raw['size']
  path=out/'正式入口回读.epro2';write_exclusive(path,data)
  formal.update(实际入口独立重开=True,实际入口逐脚BOM回读=verify_current_graph(c,inp,path),
   回读文件=str(path.relative_to(ROOT)),回读SHA256=sha(path))
  if c['board']=='FOC' and c['revision']=='RevM-ea0190d573e5':
   latest=source('FOC',frozen=True,revision='RevN-ea9850dfdb77')
   old=runpy.run_path(str(c['base']/'设计数据.py'))['PARTS']
   new=runpy.run_path(str(latest['base']/'设计数据.py'))['PARTS']
   old=sorted((p for p in old if p['board']==c['physical_board']),key=lambda p:p['ref'])
   new=sorted((p for p in new if p['board']==c['physical_board']),key=lambda p:p['ref'])
   assert old==new,'本实体板PARTS变化，禁止沿用旧版原生验收'
   canonical=hashlib.sha256(json.dumps(new,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()
   formal['逐板版本适用']={'版本':'RevM -> RevN-ea9850dfdb77','板':c['physical_board'],
    '本板全部归属位号':len(new),'排序规则':'PARTS按ref排序，JSON sort_keys=True ensure_ascii=False compact UTF8',
    'canonical_SHA256':canonical,'全部PARTS字段逐项完全相同':True,'RevN源文件SHA256':latest['hashes'],
    '不扩展到其他板或整域电气放行':True}
 finally:
  if session:d.cli(EXE,'session','close','--session',session,'--destroy')
  formal['正式入口重开后目录SHA256']={p.relative_to(index.parent).as_posix():sha(p) for p in index.parent.rglob('*') if p.is_file()}
  update(c,result)
 print(dump({'入口':formal['入口'],'实际入口独立重开':formal.get('实际入口独立重开'),
  '逐板版本适用':formal.get('逐板版本适用')}))


def closed_reopen(c):
 """全部构建/编辑会话关闭后，从最终交付文件新开会话检查落盘结果。"""
 d=module('原理图交付');inp=read(packet(c));d.CACHE=new_export_dir(Path(inp.get('构建目录',CACHE/c['board'])),'最终重开');result=validation_result(c)
 assert result['板源文件SHA256']==c['hashes'] and result['官方编辑保存独立重开']
 target=c['base']/result['原生工程'];assert sha(target)==result['原生工程SHA256']
 session=d.cli(EXE,'open','--path',target.as_posix(),'--headless','true')['value']['sessionId']
 def invoke(code):return d.cli(EXE,'invoke','--session',session,'--ext-uuid','eda','--timeout','60000','--code',code)['value']
 try:
  d.wait_for_project(invoke);pages=invoke('return await eda.dmt_Schematic.getAllSchematicPagesInfo();')
  assert len(pages)==inp['页数'];first=next(p['uuid'] for p in pages if p['name']==inp.get('首页',c['parts'][0]['page']))
  d.open_document(invoke,first)
  texts=invoke('return (await eda.sch_PrimitiveText.getAll()).map(t=>t.getState_Content());')
  assert any('SQLite同版保存 '+c['digest'][:12] in t for t in texts)
  raw=invoke('const f=await eda.sys_FileManager.getProjectFile("关闭后回读",undefined,"epro2");const a=new Uint8Array(await f.arrayBuffer());let s="";for(let i=0;i<a.length;i+=32768)s+=String.fromCharCode(...a.subarray(i,i+32768));return {size:f.size,data:btoa(s)};')
  payload=base64.b64decode(raw['data'],validate=True);assert len(payload)==raw['size']
  export=d.CACHE/'SQLite全部会话关闭后回读.epro2';export.write_bytes(payload)
  ps=copy.deepcopy(c['parts']);bindings={b['位号']:b for b in inp['绑定']}
  for p in ps:
   p['model']=p['mpn'];p.pop('approved_binding',None);p.pop('mechanical_candidate',None);b=bindings[p['ref']]
   if b.get('库文件'):p['approved_binding']={'footprint':b['封装'],'member':b['库文件'],'sha256':b['封装SHA256'],'physical_pin_to_pad':b['引脚映射']}
  check=module('核验交换原理图').verify_exchange(export,{(r,p):n for r,p,n in inp['预期网络']},{tuple(x) for x in inp['NC']},parts=ps,hardware=HW,cap_specs=c['data'].get('CAP_SPECS'),strict_full_BOM=True)
  result.update(官方保存关闭独立重开=True,官方全部会话关闭后逐脚回读=check,
   关闭重开工具SHA256=sha(__file__),逐脚核验工具SHA256=sha(Path(__file__).with_name('核验交换原理图.py')))
 except Exception as e:
  result.update(官方保存关闭独立重开=False,关闭后重开失败=type(e).__name__+': '+str(e)[:3000]);raise
 finally:
  d.cli(EXE,'session','close','--session',session,'--destroy')
  result['原生工程SHA256']=sha(target);update(c,result)
 if c['board'] in SPLIT_BOARDS:enrich_bom(c)
 print('全部编辑会话关闭后最终交付重开通过',c['board'],check['actual_component_refs'],flush=True)

def verify_current_graph(c,inp,path):
 ps=copy.deepcopy(c['parts']);bindings={b['位号']:b for b in inp['绑定']}
 for p in ps:
  p['model']=p['mpn'];p.pop('approved_binding',None);p.pop('mechanical_candidate',None);b=bindings[p['ref']]
  if b.get('库文件'):p['approved_binding']={'footprint':b['封装'],'member':b['库文件'],'sha256':b['封装SHA256'],'physical_pin_to_pad':b['引脚映射']}
 return module('核验交换原理图').verify_exchange(path,{(r,p):n for r,p,n in inp['预期网络']},{tuple(x) for x in inp['NC']},parts=ps,hardware=HW,cap_specs=c['data'].get('CAP_SPECS'),strict_full_BOM=True)

def compact_graph_evidence(result):
 result=copy.deepcopy(result);footprints=result.get('full_footprint_readback')
 if isinstance(footprints,dict) and isinstance(footprints.get('approved_shared_refs'),list):
  refs=footprints.pop('approved_shared_refs')
  footprints['approved_shared_refs_count']=len(refs)
  footprints['approved_shared_refs_sha256']=hashlib.sha256(dump(refs).encode('utf8')).hexdigest()
 return result

def verify_protel2(text,inp):
 """Protel2的[]组件及()网络块；精确核对全体组件/连接与NC，不模糊改名。"""
 lines=text.lstrip('\ufeff').splitlines();components=set();actual={};netsets={};i=0
 tagged=bool(lines and lines[0].strip()=='PROTEL NETLIST 2.0')
 if tagged:i=1
 while i<len(lines):
  token=lines[i].strip();i+=1
  if not token:continue
  assert token in ('[','('),('未知Protel2记录',token[:160])
  stop=']' if token=='[' else ')';body=[]
  while i<len(lines) and lines[i].strip()!=stop:body.append(lines[i].strip());i+=1
  assert i<len(lines),('Protel2块未闭合',token);i+=1
  if token=='[':
   assert len(body)>=3,('组件记录不足',body)
   if tagged:
    assert body[0]=='DESIGNATOR' and body.count('DESIGNATOR')==1 and 'FOOTPRINT' in body and 'PARTTYPE' in body,('Protel2字段缺失',body[:6])
    ref=body[1]
   else:ref=body[0]
   assert ref and ref not in components,('组件记录无效或重复',ref)
   components.add(ref)
  else:
   assert len(body)>=2 and body[0] and body[0] not in netsets,('网络记录无效或重复',body[:4])
   net=body[0];pins=set()
   for endpoint in body[1:]:
    if not endpoint:continue
    if tagged:endpoint=endpoint.split()[0]
    assert '-' in endpoint,('引脚记录无效',endpoint)
    ref,pin=endpoint.rsplit('-',1);key=(ref,pin)
    assert key not in actual,('引脚多网或重复',key)
    actual[key]=net;pins.add(key)
   netsets[net]=pins
 expected={(r,p):n for r,p,n in inp['预期网络']};nc={tuple(x) for x in inp['NC']}
 refs={b['位号'] for b in inp['绑定']}
 missing=sorted(set(expected)-set(actual));extra=sorted(set(actual)-set(expected))
 wrong=[{'ref':r,'pin':p,'expected':n,'actual':actual.get((r,p))} for (r,p),n in expected.items() if (r,p) in actual and actual[(r,p)]!=n]
 expected_nets=set(expected.values())
 scope=inp.get('原理图范围') or {}
 scope_refs_match=(not scope or (len(refs)==scope.get('board_on_ref_count') and scope_digest(refs)==scope.get('board_on_refs_sha256')))
 result={'status':'PASS' if components==refs and actual==expected and set(netsets)==expected_nets and not nc.intersection(actual) and scope_refs_match else 'FAIL_COVERAGE',
  'actual_component_refs':len(components),'expected_component_refs':len(refs),
  'native_scope_component_refs_match':scope_refs_match,
  'connected_pins':len(actual),'expected_connected_pins':len(expected),'NC_excluded':not bool(nc.intersection(actual)),
  'expected_NC_pins':len(nc),'missing_refs':sorted(refs-components),'extra_refs':sorted(components-refs),
  'actual_nets':len(netsets),'expected_nets':len(expected_nets),'missing_nets':sorted(expected_nets-set(netsets)),'extra_nets':sorted(set(netsets)-expected_nets),
  'missing_pins':[list(x) for x in missing],'extra_pins':[list(x) for x in extra],'wrong_nets':wrong,
  'actual_connections_sha256':hashlib.sha256(dump([[r,p,n] for (r,p),n in sorted(actual.items())]).encode('utf8')).hexdigest()}
 return result

def official_netlist_text(invoke,name,enum):
 """ASCII传输原始官方网表字节，避免CLI长JSON中文字节边界的replacement。"""
 assert enum in ('ALTIUM_DESIGNER','JLCEDA_PRO')
 reply=invoke('try{const f=await eda.sch_ManufactureData.getNetlistFile('+dump(name)+',ESYS_NetlistType.'+enum+');if(!f)return {returnType:typeof f};const a=new Uint8Array(await f.arrayBuffer());let s="";for(let i=0;i<a.length;i+=32768)s+=String.fromCharCode(...a.subarray(i,i+32768));return {size:f.size,data:btoa(s)};}catch(e){return {error:String(e)};}' )
 if 'data' in reply:
  raw=base64.b64decode(reply.pop('data'),validate=True);assert len(raw)==reply['size']
  reply.update(text=raw.decode('utf8'),original_bytes_sha256=hashlib.sha256(raw).hexdigest(),transport='ASCII_BASE64_ORIGINAL_FILE_BYTES')
 return reply

def verify_jlceda(text,inp):
 """读取官方JLCEDA全量网表，含板外合同；NC只允许原声明的开路脚。"""
 document=json.loads(text);components=document['components'];refs=set();actual={};nc=set();missing_footprints=[];flags=[]
 bindings={b['位号']:b for b in inp['绑定']};expected={(r,p):n for r,p,n in inp['预期网络']};expected_nc={tuple(x) for x in inp['NC']}
 for component in components.values():
  props=component['props'];ref=props['Designator'];assert ref not in refs and ref in bindings,(ref,'重复或额外位号')
  refs.add(ref);binding=bindings[ref];assert props['Manufacturer Part']==binding['型号'],(ref,'官方网表完整型号变化')
  want_pcb=binding['安装'] in ('板上','待设计');assert props['Convert to PCB']==('yes' if want_pcb else 'no'),(ref,'物理装配范围改变')
  if not props.get('Footprint'):missing_footprints.append({'位号':ref,'板上':want_pcb})
  flags.append(want_pcb)
  assert set(component['pinInfoMap'])==set(binding['引脚映射'].values()),(ref,'官方网表缺物理引脚')
  for number,pin in component['pinInfoMap'].items():
   assert pin['number']==number and pin['props']['Pin Number']==number,(ref,number,'物理脚号变化')
   key=(ref,number);net=pin.get('net','')
   if net:actual[key]=net
   else:nc.add(key)
 scope=inp.get('原理图范围') or {}
 scope_refs_match=(not scope or (len(refs)==scope.get('board_on_ref_count') and scope_digest(refs)==scope.get('board_on_refs_sha256')))
 status='PASS' if refs==set(bindings) and actual==expected and nc==expected_nc and not any(x['板上'] for x in missing_footprints) and scope_refs_match else 'FAIL_COVERAGE'
 return {'status':status,'actual_component_refs':len(refs),'expected_component_refs':len(bindings),
  'native_scope_component_refs_match':scope_refs_match,
  'connected_pins':len(actual),'expected_connected_pins':len(expected),'NC_pins':len(nc),'expected_NC_pins':len(expected_nc),
  'actual_nets':len(set(actual.values())),'expected_nets':len(set(expected.values())),
  '板上位号':sum(flags),'板外合同位号':len(flags)-sum(flags),'缺封装属性':missing_footprints,
  'missing_pins':[list(x) for x in sorted(set(expected)-set(actual))],
  'extra_pins':[list(x) for x in sorted(set(actual)-set(expected))],
  'wrong_nets':[{'ref':r,'pin':p,'expected':n,'actual':actual.get((r,p))} for (r,p),n in expected.items() if actual.get((r,p))!=n],
  'NC完全相同':nc==expected_nc,'actual_connections_sha256':hashlib.sha256(dump([[r,p,n] for (r,p),n in sorted(actual.items())]).encode('utf8')).hexdigest()}

def recheck_folder_netlist(c):
 """Re-parse preserved official bytes after parser repair, without re-export."""
 result=validation_result(c);e=result['官方文件夹工程'];inp=read(packet(c))
 assert e['板源文件SHA256']==c['hashes'] and e['关闭独立重开']
 folder=(ROOT/e['工程索引']).parent
 for name,h in e['完整目录文件SHA256'].items():assert sha(folder/name)==h,(name,'原生证据文件已变')
 assert sha(ROOT/e['实际官方交换文件'])==e['实际官方交换SHA256']
 path=ROOT/e['官方网表文件'] if e.get('官方网表文件') else folder.parent/'官方网表.net'
 assert path.is_file() and path.parent==folder.parent
 h=sha(path)
 if e.get('官方网表SHA256'):assert e['官方网表SHA256']==h
 check=verify_protel2(path.read_text(encoding='utf8'),inp)
 e.update(官方网表文件=str(path.relative_to(ROOT)),官方网表SHA256=h,官方网表全量核对=check,
  有效官方网表=check['status']=='PASS',网表解析器SHA256=c['tool_sha'])
 if e.get('失败'):e.setdefault('历史失败',[]).append(e.pop('失败'))
 e['网表解析修复回验']='仅回验保全官方原字节；未再次调用或重建网表'
 update(c,result);print(dump(check),flush=True)

def protel2_once(c, settled_focus_retry=False):
 """仅在同版隔离副本调用一次官方Protel2 getter；原件不打开、不写回。"""
 result=validation_result(c);formats=result.setdefault('官方网表格式核验',{})
 assert result['板源文件SHA256']==c['hashes']
 target=c['base']/result['原生工程'];origin_sha=sha(target);assert origin_sha==result['原生工程SHA256']
 record_key='Protel2_稳定图页焦点复验' if settled_focus_retry else 'Protel2'
 if record_key in formats:
  integrity=validate_protel2_reuse(formats[record_key],c['hashes'],c['digest'],origin_sha)
  if integrity['status']!='REUSABLE_COMPLETE':
   print('保留不完整历史记录；不作为完整证据复用',c['board'],record_key,integrity,flush=True);return
  print('复用已逐项校验的既有证据，不再次调用',c['board'],record_key,integrity,flush=True);return
 inp=read(packet(c))
 assert inp['源SHA256']==c['digest']
 d=module('原理图交付');d.CACHE=CACHE/c['board']
 if settled_focus_retry:
  prior=formats['Protel2'];integrity=validate_protel2_reuse(prior,c['hashes'],c['digest'],origin_sha)
  if integrity['status']!='REUSABLE_COMPLETE':
   print('Protel2隔离副本来源证据不完整；拒绝开始复验',c['board'],integrity,flush=True);return
  work=ROOT/prior['隔离副本']
 else:
  work=Path(tempfile.mkdtemp(prefix='Protel2隔离-',dir=d.CACHE))/target.name
  assert work.resolve().is_relative_to(ROOT.resolve());d.sqlite_copy(target,work)
 evidence={'格式':'Protel2','接口':'SCH_ManufactureData.getNetlistFile','板源文件SHA256':c['hashes'],
  '源SHA256':c['digest'],'同版原件':str(target.relative_to(ROOT)),'原件SHA256_前':origin_sha,
  '隔离副本':str(work.relative_to(ROOT)),'隔离副本SHA256_前':sha(work),'工具SHA256':sha(__file__),
  '调用次数':0,'结论':'NOT_CALLED','ERC及电气FAIL不变':True}
 evidence['复验依据']='官方CLI指南要求查询网表前等待编辑器稳定5–10秒；此前缺少等待和当前图页焦点回读。' if settled_focus_retry else ''
 formats[record_key]=evidence;session=None
 def invoke(code):return d.cli(EXE,'invoke','--session',session,'--ext-uuid','eda','--timeout','60000','--code',code)['value']
 export_dir=new_export_dir(work.parent,record_key)
 evidence['隔离回读输出目录']=str(export_dir.relative_to(ROOT))
 def exported(name):
  raw=invoke('const f=await eda.sys_FileManager.getProjectFile("Protel2核对",undefined,"epro2");const a=new Uint8Array(await f.arrayBuffer());let s="";for(let i=0;i<a.length;i+=32768)s+=String.fromCharCode(...a.subarray(i,i+32768));return {size:f.size,data:btoa(s)};')
  payload=base64.b64decode(raw['data'],validate=True);assert len(payload)==raw['size'];path=export_dir/name
  file_sha=write_exclusive(path,payload)
  checked=compact_graph_evidence(verify_current_graph(c,inp,path))
  checked.update(实际官方交换文件=str(path.relative_to(ROOT)),实际官方交换SHA256=file_sha)
  return checked
 try:
  session=d.cli(EXE,'open','--path',work.as_posix(),'--headless','true')['value']['sessionId'];d.wait_for_project(invoke)
  pages=invoke('return await eda.dmt_Schematic.getAllSchematicPagesInfo();');assert len(pages)==inp['页数']
  expected_page=next(p['uuid'] for p in pages if p['name']==inp.get('首页',c['parts'][0]['page']))
  d.open_document(invoke,expected_page)
  if settled_focus_retry:
   time.sleep(5)
   focus=invoke('const s=await eda.dmt_Schematic.getCurrentSchematicInfo();const p=await eda.dmt_Schematic.getCurrentSchematicPageInfo();return {schematicUuid:s?.uuid,pageUuid:p?.uuid,parentSchematicUuid:p?.parentSchematicUuid};')
   evidence['当前焦点回读']=focus;assert focus.get('pageUuid')==expected_page and focus.get('schematicUuid')==focus.get('parentSchematicUuid'), '当前活动图页不符'
  evidence['调用前实际逐脚及位号回读']=exported('调用前.epro2')
  evidence.update(调用次数=1,结论='CALL_SUBMITTED');update(c,result)
  raw=invoke('try{const f=await eda.sch_ManufactureData.getNetlistFile("同版Protel2网表","Protel2");if(!f)return {returnType:typeof f,value:f??null};return {returnType:Object.prototype.toString.call(f),isFile:f instanceof File,name:f.name,size:f.size,data:await f.text()};}catch(e){return {returnType:"throw",error:String(e)};}')
  evidence['返回类型']=raw.get('returnType');evidence['返回文件名']=raw.get('name');evidence['返回文件字节数']=raw.get('size')
  if raw.get('isFile') and isinstance(raw.get('data'),str):
   text=raw['data'];path,file_sha=save_export_text(export_dir,'官方网表_Protel2.net',text)
   evidence.update(必要文件=str(path.relative_to(ROOT)),必要文件SHA256=file_sha)
   try:evidence['网表全量核对']=verify_protel2(text,inp);evidence['结论']=evidence['网表全量核对']['status']
   except Exception as e:evidence.update(结论='FAIL_FORMAT_OR_CONTENT',解析错误=type(e).__name__+': '+str(e)[:3000])
  else:evidence.update(结论='FAIL_NO_FILE' if raw.get('returnType')!='throw' else 'FAIL_API_THROW',返回值=raw.get('value'),错误=raw.get('error'),网表全量连接及NC核对='NOT_RUN_NO_FILE' if raw.get('returnType')!='throw' else 'NOT_RUN_API_THROW')
  evidence['调用后实际逐脚及位号回读']=exported('调用后.epro2')
  evidence['调用前后位号及连接与冻结源一致']=True
 except Exception as e:evidence.update(结论='FAIL_SESSION_OR_GRAPH',失败=type(e).__name__+': '+str(e)[:3500])
 finally:
  if session:
   try:d.cli(EXE,'session','close','--session',session,'--destroy')
   except Exception as e:evidence['会话关闭错误']=str(e)[:1000]
  evidence['隔离副本SHA256_后']=sha(work);evidence['原件SHA256_后']=sha(target)
  evidence['原件哈希不变']=evidence['原件SHA256_后']==origin_sha
  if not evidence['原件哈希不变']:evidence['结论']='FAIL_ORIGINAL_CHANGED'
  if evidence.get('结论')=='PASS' and evidence.get('调用前后位号及连接与冻结源一致') and evidence['原件哈希不变']:
   result['有效官方网表']=True
  update(c,result)
 print('Protel2一次核对',c['board'],evidence['结论'],'返回',evidence.get('返回类型'),'原件不变',evidence['原件哈希不变'],flush=True)

def native_netlist_compat(c):
 """One read-only official obsolete getter call on a fresh same-version clone."""
 result=validation_result(c);inp=read(packet(c));d=module('原理图交付')
 assert result['板源文件SHA256']==c['hashes'] and inp['源SHA256']==c['digest']
 target=c['base']/result['原生工程'];origin_sha=sha(target);assert origin_sha==result['原生工程SHA256']
 key='Protel2_官方兼容字符串';formats=result.setdefault('官方网表格式核验',{})
 if key in formats:
  integrity=validate_protel2_reuse(formats[key],c['hashes'],c['digest'],origin_sha)
  print('既有兼容调用记录已校验；不再调用',integrity,flush=True);return
 active=[s for s in d.cli(EXE,'session','list')['value'] if s.get('status') not in ('closed','destroyed')]
 assert not active,'其他官方会话仍活动，不能并发开始兼容验证'
 out=new_export_dir(Path(inp.get('构建目录',CACHE/c['board'])),'官方兼容拓扑')
 clone=out/target.name;assert not clone.exists();d.sqlite_copy(target,clone)
 evidence={'格式':'Protel2','接口':'eda.sch_Netlist.getNetlist','API状态':'官方obsolete兼容接口；未调用setNetlist',
  '实际客户端版本':'4.1.60.198f38ab','板源文件SHA256':c['hashes'],'源SHA256':c['digest'],
  '同版原件':str(target.relative_to(ROOT)),'原件SHA256_前':origin_sha,
  '隔离副本':str(clone.relative_to(ROOT)),'隔离副本SHA256_前':sha(clone),
  '工具SHA256':sha(__file__),'调用次数':0,'结论':'NOT_CALLED','ERC及电气FAIL不变':True}
 formats[key]=evidence;update(c,result);session=None
 def invoke(code):return d.cli(EXE,'invoke','--session',session,'--ext-uuid','eda','--timeout','60000','--code',code)['value']
 try:
  session=d.cli(EXE,'open','--path',clone.as_posix(),'--headless','true')['value']['sessionId'];d.wait_for_project(invoke)
  pages=invoke('return await eda.dmt_Schematic.getAllSchematicPagesInfo();');assert len(pages)==inp['页数']
  first=next(p['uuid'] for p in pages if p['name']==inp.get('首页',c['parts'][0]['page']));d.open_document(invoke,first);time.sleep(5)
  focus=invoke('const s=await eda.dmt_Schematic.getCurrentSchematicInfo();const p=await eda.dmt_Schematic.getCurrentSchematicPageInfo();return {schematicUuid:s?.uuid,pageUuid:p?.uuid,parentSchematicUuid:p?.parentSchematicUuid,methodType:typeof eda.sch_Netlist?.getNetlist};')
  evidence['当前图页及接口回读']=focus
  assert focus.get('pageUuid')==first and focus.get('schematicUuid')==focus.get('parentSchematicUuid'),'当前图页/原理图焦点错误'
  if focus.get('methodType')!='function':evidence.update(结论='FAIL_OFFICIAL_METHOD_UNAVAILABLE',网表全量连接及NC核对='NOT_RUN_METHOD_UNAVAILABLE')
  else:
   evidence.update(调用次数=1,结论='CALL_SUBMITTED');update(c,result)
   reply=invoke('try{const v=await eda.sch_Netlist.getNetlist("Protel2");return {returnType:typeof v,text:typeof v==="string"?v:null,value:typeof v==="string"?null:v??null};}catch(e){return {returnType:"throw",error:String(e)};}')
   evidence.update(返回类型=reply.get('returnType'),错误=reply.get('error'))
   if isinstance(reply.get('text'),str) and reply['text'].strip():
    path,file_sha=save_export_text(out,'官方兼容Protel2网表.net',reply['text'])
    evidence.update(必要文件=str(path.relative_to(ROOT)),必要文件SHA256=file_sha,返回文本长度=len(reply['text']))
    try:
     check=verify_protel2(reply['text'],inp);evidence.update(网表全量连接及NC核对=check,结论=check['status'])
    except Exception as e:evidence.update(结论='FAIL_FORMAT_OR_CONTENT',解析错误=type(e).__name__+': '+str(e)[:3000])
   else:evidence.update(结论='FAIL_API_THROW' if reply.get('returnType')=='throw' else 'FAIL_EMPTY_OR_NONSTRING',返回值=reply.get('text') if isinstance(reply.get('text'),str) else reply.get('value'),网表全量连接及NC核对='NOT_RUN_NO_OFFICIAL_TEXT')
  # Native manufacturing export, not a desktop screenshot or a reconstructed drawing.
  view=next((p for p in pages if p['name'].endswith('U相功率桥')),pages[0]);d.open_document(invoke,view['uuid']);time.sleep(2)
  preview=invoke('try{const f=await eda.sch_ManufactureData.getExportDocumentFile("原生图面预览","PNG",{theme:"Black on White",lineWidth:"Always 1px"},"Current Schematic Page");if(!f)return {returnType:typeof f};const a=new Uint8Array(await f.arrayBuffer());let s="";for(let i=0;i<a.length;i+=32768)s+=String.fromCharCode(...a.subarray(i,i+32768));return {name:f.name,size:f.size,mime:f.type,data:btoa(s)};}catch(e){return {error:String(e)};}')
  evidence['原生图面预览图页']=view['name']
  if preview.get('data'):
   payload=base64.b64decode(preview['data'],validate=True);assert len(payload)==preview['size']
   if payload.startswith(b'\x89PNG\r\n\x1a\n'):
    path=out/'原生图面预览.png';file_sha=write_exclusive(path,payload)
    evidence.update(原生图面预览=str(path.relative_to(ROOT)),原生图面预览SHA256=file_sha,原生图面预览MIME=preview.get('mime'))
   else:evidence['原生PNG导出限制']={'mime':preview.get('mime'),'size':len(payload),'原因':'API返回文件不是PNG'}
  else:evidence['原生PNG导出限制']=preview
  if not evidence.get('原生图面预览'):
   svg=invoke('try{const f=await eda.sch_ManufactureData.getSvgFile("原生图面预览");return f?{text:await f.text(),mime:f.type}:{returnType:typeof f};}catch(e){return {error:String(e)};}')
   if isinstance(svg.get('text'),str) and '<svg' in svg['text'][:1000]:
    path,file_sha=save_export_text(out,'官方原生图面.svg',svg['text'])
    evidence.update(官方原生SVG=str(path.relative_to(ROOT)),官方原生SVGSHA256=file_sha)
    runtime=Path.home()/'.cache/codex-runtimes/codex-primary-runtime/dependencies/node'
    node=runtime/'bin/node.exe';sharp=runtime/'node_modules/sharp';png=out/'原生图面预览.png'
    if node.is_file() and sharp.is_dir():
     try:
      script='const sharp=require(process.argv[1]);sharp(process.argv[2],{density:144}).png().toBuffer().then(b=>require("fs").writeFileSync(process.argv[3],b,{flag:"wx"})).catch(e=>{console.error(String(e));process.exit(1)});'
      completed=subprocess.run([str(node),'-e',script,str(sharp),str(path),str(png)],capture_output=True,text=True,timeout=60)
      assert completed.returncode==0,completed.stderr[:1000]
      evidence.update(原生图面预览=str(png.relative_to(ROOT)),原生图面预览SHA256=sha(png),原生图面预览MIME='image/png',图面栅格化来源='官方SVG原字节经Sharp渲染；非重绘或桌面截图')
     except Exception as e:evidence['原生SVG渲染限制']=str(e)[:1000]
   else:evidence['原生SVG导出限制']={k:v for k,v in svg.items() if k!='text'}
 except Exception as e:evidence.update(结论='FAIL_SESSION_OR_CONTEXT',失败=type(e).__name__+': '+str(e)[:3500])
 finally:
  if session:
   try:d.cli(EXE,'session','close','--session',session,'--destroy')
   except Exception as e:evidence['会话关闭错误']=str(e)[:1000]
  evidence.update(原件SHA256_后=sha(target),隔离副本SHA256_后=sha(clone))
  evidence['原件哈希不变']=sha(target)==origin_sha
  if not evidence['原件哈希不变']:evidence['结论']='FAIL_ORIGINAL_CHANGED'
  if evidence.get('结论')=='PASS':
   result.update(有效官方网表=True,当前官方网表接口='官方obsolete getNetlist Protel2兼容路径',当前官方网表文件=evidence['必要文件'],当前官方网表SHA256=evidence['必要文件SHA256'],当前网表阻塞=None)
  else:result['有效官方网表']=False
  update(c,result)
 print('官方兼容拓扑',c['board'],evidence['结论'],'原件不变',evidence['原件哈希不变'],flush=True)

def main():
 # 入口自检：本机客户端lceda-pro.exe是Electron应用，一旦环境里带着
 # ELECTRON_RUN_AS_NODE，它就会以纯Node启动，把子命令当脚本路径解析，
 # 于是所有官方CLI阶段都报 "Cannot find module '<cwd>\\session'"。
 # 这里显式报错而不静默清除：静默清除会掩盖调用方的环境问题。
 assert 'ELECTRON_RUN_AS_NODE' not in os.environ, (
  '环境变量 ELECTRON_RUN_AS_NODE 存在：lceda-pro.exe 会以纯Node运行，官方CLI阶段必然失败'
  '（Cannot find module "<cwd>\\session"）。请在调用前执行 '
  'Remove-Item Env:ELECTRON_RUN_AS_NODE（置空字符串无效：Electron只判断变量是否存在）。')
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--板',choices=CONFIG,required=True)
 ap.add_argument('--稳定输入',help='既有缓存中的完整稳定清单；只允许候选消费，保留旧正式入口')
 ap.add_argument('--阶段',choices=['查库','绑定','生成','单页候选','候选预览','候选修整','结构目录交付','结构提升','结构ERC归因','候选ERC明细','候选FP因果','冻结网表检查','官方','文件夹','直接文件夹','直接重开','保存诊断','修正引用','提升目录','正式重开','登记入口','网表回验','关闭重开','Protel2','Protel2稳定复验','兼容网表'],required=True)
 ap.add_argument('--保全输入',action='store_true',help='仅在保全旧源及缓存输出上验证公共工具，不放行当前电气源')
 ap.add_argument('--刷新绑定',action='store_true',help='显式允许保全源按当前公共库重建候选绑定；不改电气源')
 ap.add_argument('--物理板',choices=['驱动主板','辅助电源板','中央稳压模块','系统接线'],help='FOC保全输入独立工程；每实体板保持一完整页')
 ap.add_argument('--候选尝试',help='稳定源单页候选的全新缓存子目录；不得覆盖已有候选或正式目录')
 ap.add_argument('--输入版',choices=['RevL-8c24403679dc','RevM-ea0190d573e5','RevN-ea9850dfdb77','RevN-8bd580ddbc3e','RevN-c47d0646d155','RevN-8ff2fabbd4a7','RevN-b3e9f11ccab6','RevO-93c052142116','RevP-bdf928914670','RevQ-fe3d17b2b9ce','RevR-4f35e1c53af4','RevS-b9d5714fd58d','RevU-8be06130e9ee','RevV-1c41e297d19a','RevV-583066fa99a7','RevW-9a044a641d5c','RevU-f519d949e18c','RevV-d68cc398dbf1','RevV-8a893cee9b2b','RevV-4a8a056128cf','RevP-0f5f27059bb0','RevO-bcea12a69c16','RevP-4255b6ec31c8','RevP-f48f56be6bff'],help='作者自然提交且源已按精确SHA保全的输入版本')
 a=ap.parse_args();CACHE.mkdir(parents=True,exist_ok=True)
 if a.稳定输入:
  assert a.板 in ('配电','FOC') and not a.输入版
  assert a.板=='FOC' or not a.保全输入
  assert a.板=='FOC' or not a.物理板
  assert a.阶段 in ('查库','绑定','单页候选','候选预览','候选修整','结构ERC归因','候选ERC明细','候选FP因果','Protel2','兼容网表','直接重开','结构提升'),'只提升经独立验收的E4完整原生包'
  c=stable_pd_source(a.稳定输入) if a.板=='配电' else stable_foc_source(a.稳定输入,require_live=not a.保全输入)
 else:c=source(a.板,frozen=a.保全输入 or a.阶段 in ('单页候选','冻结网表检查'),revision=a.输入版)
 c['structured_regions']=a.阶段 in ('生成','单页候选','候选预览','候选修整','结构目录交付','候选ERC明细','候选FP因果')
 if c['structured_regions'] and a.板=='FOC':
  assert a.物理板,'结构化候选必须显式选择实体板，不把三块板合入一个图面'
 if a.保全输入 and not a.稳定输入:
  assert a.阶段 in ('单页候选','候选预览','候选修整','结构目录交付','结构提升','结构ERC归因','绑定','生成','官方','文件夹','直接文件夹','直接重开','保存诊断','修正引用','提升目录','正式重开','登记入口','网表回验','关闭重开','Protel2'),'保全输入仅用于明确工具开发阶段'
  c['packet_path']=(c['base']/c['board'] if c.get('revision') and c['board'] in SPLIT_BOARDS else c['base'] if c.get('revision') else CACHE/c['board'])/'单页工具集成输入.json'
 if c.get('revision') and c['board'] in SPLIT_BOARDS:
  # A candidate/cache belongs to the exact source revision, just like its
  # packet. Never replace another revision's shared board candidate.
  c.update(build_root=c['base']/c['board'],packet_path=c['base']/c['board']/'单页工具集成输入.json')
 elif c.get('revision') and c['board']=='配电':
  c.update(build_root=c['base'],packet_path=c['base']/'单页工具集成输入.json')
 if a.刷新绑定:
  assert a.阶段 in ('生成','单页候选','候选预览') and not a.物理板,'库写入须完整板域串行执行，不用物理子集覆盖板域绑定'
  c['refresh_bindings']=True
 if a.物理板:
  assert a.板=='FOC' and (a.保全输入 or c.get('e4_stable')),'物理分工程工具开发只消费保全FOC源'
  if c.get('revision') or c.get('e4_stable'):
   refs={p['ref'] for p in c['parts'] if (p['board'] if c['structured_regions'] or c.get('e4_stable') else '系统接线' if not p['onboard'] or p['board']=='外置模块' else p['board'])==a.物理板}
  else:
   inp=read(CACHE/'FOC/单页工具集成输入.json')
   assert inp['板源文件SHA256']==c['hashes']
   pages=[name for name in inp['标准端口计划'] if name.startswith(a.物理板+'-')]
   assert len(pages)==1,(a.物理板,pages)
   refs={ref for ref,page in inp['位号图页'].items() if page==pages[0]}
  c['parts']=[p for p in c['parts'] if p['ref'] in refs]
  assert len(c['parts'])==len(refs) and refs
  if a.物理板=='中央稳压模块' and c.get('e4_stable'):
   select_central_board_on_scope(c)
  scope=(c['base'] if c.get('revision') else CACHE/'FOC')/a.物理板
  if a.候选尝试:
   assert a.稳定输入 and c.get('e4_stable') and a.阶段 in ('生成','单页候选','候选预览','候选修整','候选ERC明细','候选FP因果','直接重开'), '候选尝试目录仅供稳定源缓存候选阶段使用'
   assert re.fullmatch(r'[a-z0-9][a-z0-9-]{2,63}',a.候选尝试), '候选尝试名须为安全小写标识'
   scope=scope/('attempt-'+a.候选尝试)
   if scope.exists():
    assert a.阶段!='单页候选' or not (scope/'单页图面候选.json').exists(), '现有单页候选不覆盖；改用新尝试名'
    assert a.阶段!='候选预览' or (scope/'单页图面候选.json').is_file(), '候选预览需要同尝试目录中已有单页候选'
    scope.mkdir(parents=True,exist_ok=True)
   else:scope.mkdir(parents=True,exist_ok=False)
  else:scope.mkdir(exist_ok=True)
  c.update(physical_board=a.物理板,build_root=scope,name=a.物理板+'原理图',
   target=scope/'原生工程',report=scope/'原理图核验.json',
   packet_path=scope/'单页工具集成输入.json',exchange_target=scope/(a.物理板+'原理图.epro2'))
 if a.阶段=='查库':fetch(c)
 elif a.阶段=='绑定':
  assert not a.物理板,'只对完整板域写公共绑定'
  bindings,diffs=bind(c);print(dump({'绑定':sum(bool(b['封装']) for b in bindings.values()),'总位号':len(bindings),'功能差异':len(diffs)}))
 elif a.阶段=='生成':generate(c)
 elif a.阶段=='单页候选':single_sheet_candidate(c)
 elif a.阶段=='候选预览':preview_structured_candidate(c)
 elif a.阶段=='候选修整':refine_structured_candidate(c)
 elif a.阶段=='结构目录交付':publish_structured_folder(c)
 elif a.阶段=='结构提升':promote_structured_candidate(c)
 elif a.阶段=='结构ERC归因':diagnose_external_erc(c)
 elif a.阶段=='候选ERC明细':probe_current_erc_detail(c)
 elif a.阶段=='候选FP因果':
  assert a.稳定输入 and a.候选尝试 and a.物理板=='中央稳压模块' and c.get('e4_stable')
  c['candidate_fp_causality']=True;diagnose_external_erc(c)
 elif a.阶段=='冻结网表检查':frozen_netlist_probe(c)
 elif a.阶段=='关闭重开':closed_reopen(c)
 elif a.阶段=='文件夹':folder_official(c)
 elif a.阶段=='直接文件夹':direct_folder(c)
 elif a.阶段=='直接重开':verify_direct_folder(c)
 elif a.阶段=='保存诊断':diagnose_folder_save(c)
 elif a.阶段=='修正引用':repair_folder_references(c)
 elif a.阶段=='提升目录':promote_folder(c)
 elif a.阶段=='正式重开':verify_formal_folder(c)
 elif a.阶段=='登记入口':finalize_delivery(c)
 elif a.阶段=='网表回验':recheck_folder_netlist(c)
 elif a.阶段=='Protel2':protel2_once(c)
 elif a.阶段=='Protel2稳定复验':protel2_once(c,settled_focus_retry=True)
 elif a.阶段=='兼容网表':native_netlist_compat(c)
 else:
  result=sqlite_official(c)
  print(dump({k:result.get(k,False) for k in ('官方导入','官方编辑保存独立重开','官方ERC已执行','有效官方网表','ERC通过')}))
  raise SystemExit(0 if result.get('官方编辑保存独立重开') else 1)
if __name__=='__main__':main()
