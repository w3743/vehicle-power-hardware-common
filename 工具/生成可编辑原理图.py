"""从审定连接表生成标准原理图，再由嘉立创官方转换器生成专业版工程。"""
from pathlib import Path
import collections, copy, hashlib, json, math, re, runpy, shutil, subprocess, zipfile
import sys
sys.dont_write_bytecode=True

BASE=Path(__file__).resolve().parents[2]/'FOC驱动与储能'
EXPORT=BASE/'导出'
REPORT=BASE/'核验'
LIB=BASE.parent/'公共/库'
DOCS=BASE/'文档'
TOOLS=BASE/'工具'
CACHE=Path.home()/'.cache/电机驱动设计归档/原理图转换'
NODE=Path.home()/'.cache/codex-runtimes/codex-primary-runtime/dependencies/node/bin/node.exe'
ENGINES=list(Path('D:/lceda-pro/resources/app/assets/chameleon').glob('*/js/convert-node-server.js'))
assert len(ENGINES)==1, '请确认本机转换器安装目录；不会猜测多个版本'
ENGINE=ENGINES[0]
GRID=5  # 专业版原理图50mil网格；仅影响符号与导线布局，不改变封装。

# 中央逐针源：TI 数据手册 Pin Functions + 专业版电气类型。
# PWR/DBVR/DCUR 指定封装的 NC 为 Undefined；TPS3700 的 OUTA/OUTB 是开漏输出。
PROFESSIONAL_PIN_TYPES={
    'INA240A2DR':{'1':'IN','2':'Ground','3':'IN','4':'Undefined','5':'OUT','6':'Power','7':'IN','8':'IN'},  # 同厂家SOIC D，仅卷带订货
    'INA240A4DR':{'1':'IN','2':'Ground','3':'IN','4':'Undefined','5':'OUT','6':'Power','7':'IN','8':'IN'},  # INA240.pdf p3, SOIC D，各增益同针号
    'INA149AID':{'1':'IN','2':'IN','3':'IN','4':'Power','5':'IN','6':'OUT','7':'Power','8':'Undefined'},  # ina149.pdf p5，双电源差分放大器
    'INA241A4IDGKR':{'1':'IN','2':'Ground','3':'IN','4':'Ground','5':'OUT','6':'Power','7':'IN','8':'IN'},  # 厂家p2/3针4 Reserved, connect to ground
    'INA241A5IDGKR':{'1':'IN','2':'Ground','3':'IN','4':'Ground','5':'OUT','6':'Power','7':'IN','8':'IN'},
    'TLV1701AIDBVR':{'1':'IN','2':'Power','3':'IN','4':'Open Collector','5':'Power'},  # 原厂TLV170x p1/5/7，DBV5开集输出
    'TLV1702AIDGKR':{'1':'Open Collector','2':'IN','3':'IN','4':'Power','5':'IN','6':'IN','7':'Open Collector','8':'Power'},  # 原厂TLV170x p1/5/7，DGK8开集输出
    'SN74LVC2G08DCUR':{'1':'IN','2':'IN','3':'OUT','4':'Ground','5':'IN','6':'IN','7':'OUT','8':'Power'},  # 原厂p3，DCU8
    'PCA9536DR':{'1':'BI','2':'BI','3':'BI','4':'Ground','5':'BI','6':'BI','7':'BI','8':'Power'},
    'INA240A2D':{'1':'IN','2':'Ground','3':'IN','4':'Undefined','5':'OUT','6':'Power','7':'IN','8':'IN'},  # INA240.pdf p3, SOIC D
    'PCA9536D':{'1':'BI','2':'BI','3':'BI','4':'Ground','5':'BI','6':'BI','7':'BI','8':'Power'},  # PCA9536.pdf p3
    'SN74HC74PWR':{'1':'IN','2':'IN','3':'IN','4':'IN','5':'OUT','6':'OUT','7':'Ground','8':'OUT','9':'OUT','10':'IN','11':'IN','12':'IN','13':'IN','14':'Power'},
    'SN74LVC08APWR':{'1':'IN','2':'IN','3':'OUT','4':'IN','5':'IN','6':'OUT','7':'Ground','8':'OUT','9':'IN','10':'IN','11':'OUT','12':'IN','13':'IN','14':'Power'},
    'SN74LVC1G11DBVR':{'1':'IN','2':'Ground','3':'IN','4':'OUT','5':'Power','6':'IN'},
    'SN74LVC1G08DBVR':{'1':'IN','2':'IN','3':'Ground','4':'OUT','5':'Power'},
    'SN74LVC1G17DBVR':{'1':'Undefined','2':'IN','3':'Ground','4':'OUT','5':'Power'},
    'SN74LVC3G17DCUR':{'1':'IN','2':'OUT','3':'IN','4':'Ground','5':'OUT','6':'IN','7':'OUT','8':'Power'},
    'SN74LVC1G97DBVR':{'1':'IN','2':'Ground','3':'IN','4':'OUT','5':'Power','6':'IN'},
    'TPS3700DDCR':{'1':'Open Collector','2':'Ground','3':'IN','4':'IN','5':'Power','6':'Open Collector'},
}
# 追加15型号的原厂逐针表；下列页码为已归档手册物理页号。
PROFESSIONAL_PIN_TYPES.update({
    'TLV3202AIDGKR':{'1': 'OUT', '2': 'IN', '3': 'IN', '4': 'Ground', '5': 'IN', '6': 'IN', '7': 'OUT', '8': 'Power'},  # TLV3202AIDGKR.pdf p3
    'INA241A2IDGKR':{'1': 'IN', '2': 'Ground', '3': 'IN', '4': 'Ground', '5': 'OUT', '6': 'Power', '7': 'IN', '8': 'IN'},  # INA241A2IDGKR.pdf p2,3
    'TPS3808G33DBVR':{'1': 'Open Collector', '2': 'Ground', '3': 'IN', '4': 'Passive', '5': 'IN', '6': 'Power'},  # TPS3808G33DBVR.pdf p4
    'REF5025ID':{'1': 'Undefined', '2': 'Power', '3': 'OUT', '4': 'Ground', '5': 'Passive', '6': 'OUT', '7': 'Undefined', '8': 'Undefined'},  # REF5025ID.pdf p4
    'TLV1704AIPWR':{'1': 'Open Collector', '2': 'Open Collector', '3': 'Power', '4': 'IN', '5': 'IN', '6': 'IN', '7': 'IN', '8': 'IN', '9': 'IN', '10': 'IN', '11': 'IN', '12': 'Ground', '13': 'Open Collector', '14': 'Open Collector'},  # TLV1704AIPWR.pdf p5
    'UCC27517DBVR':{'1': 'Power', '2': 'Ground', '3': 'IN', '4': 'IN', '5': 'OUT'},  # UCC27517DBVR.pdf p4
    'TCAN1051HGVDR':{'1': 'IN', '2': 'Ground', '3': 'Power', '4': 'OUT', '5': 'Power', '6': 'BI', '7': 'BI', '8': 'IN'},  # TCAN1051HGVDR.pdf p5
    'TPS3431SDRBR':{'1': 'Power', '2': 'Passive', '3': 'IN', '4': 'Ground', '5': 'IN', '6': 'IN', '7': 'Open Collector', '8': 'OUT', '9': 'Ground'},  # TPS3431SDRBR.pdf p3
    'LM5164DDAR':{'1': 'Ground', '2': 'Power', '3': 'IN', '4': 'Passive', '5': 'IN', '6': 'Open Collector', '7': 'Passive', '8': 'Passive', '9': 'Ground'},  # LM5164DDAR.pdf p3
    'LMR33630ADDAR':{'1': 'Ground', '2': 'Power', '3': 'IN', '4': 'Open Collector', '5': 'IN', '6': 'Power', '7': 'Passive', '8': 'Passive', '9': 'Ground'},  # LMR33630ADDAR.pdf p5
    'TLV61046ADBVR':{'1': 'Power', '2': 'Ground', '3': 'IN', '4': 'IN', '5': 'Power', '6': 'Power'},  # TLV61046ADBVR.pdf p3
    'TLV803EA30DBZR':{'1': 'Ground', '2': 'OUT', '3': 'Power'},  # TLV803EA30DBZR.pdf p5
    'UCC21520DWR':{'1': 'IN', '2': 'IN', '3': 'Power', '4': 'Ground', '5': 'IN', '6': 'Passive', '7': 'Undefined', '8': 'Power', '9': 'Ground', '10': 'OUT', '11': 'Power', '12': 'Undefined', '13': 'Undefined', '14': 'Ground', '15': 'OUT', '16': 'Power'},  # UCC21520DWR.pdf p4
    'LM74700QDBVRQ1':{'1': 'OUT', '2': 'Ground', '3': 'IN', '4': 'IN', '5': 'OUT', '6': 'Power'},  # LM74700QDBVRQ1.pdf p3
    'TPS26630RGER':{'1': 'Power', '2': 'Power', '3': 'OUT', '4': 'OUT', '5': 'Power', '6': 'IN', '7': 'IN', '8': 'Ground', '9': 'BI', '10': 'BI', '11': 'IN', '12': 'IN', '13': 'OUT', '14': 'Open Collector', '15': 'IN', '16': 'Open Collector', '17': 'Power', '18': 'Power', '19': 'Undefined', '20': 'Undefined', '21': 'Undefined', '22': 'Undefined', '23': 'Undefined', '24': 'Undefined', '25': 'Ground'},  # TPS26630RGER.pdf p3,4
})
# 末四型号按原厂Pin Functions及当前工作模式；热焊盘保持源接地。
PROFESSIONAL_PIN_TYPES.update({
    'DRV8353SRTAR':{'1': 'Power', '2': 'Power', '3': 'Power', '4': 'IN', '5': 'Power', '6': 'OUT', '7': 'IN', '8': 'OUT', '9': 'IN', '10': 'IN', '11': 'IN', '12': 'IN', '13': 'OUT', '14': 'IN', '15': 'OUT', '16': 'OUT', '17': 'IN', '18': 'OUT', '19': 'IN', '20': 'IN', '21': 'OUT', '22': 'OUT', '23': 'OUT', '24': 'Power', '25': 'Ground', '26': 'Open Collector', '27': 'Open Collector', '28': 'IN', '29': 'IN', '30': 'IN', '31': 'IN', '32': 'IN', '33': 'IN', '34': 'IN', '35': 'IN', '36': 'IN', '37': 'IN', '38': 'Power', '39': 'Ground', '40': 'Power', '41': 'Passive'},  # DRV8353SRTAR.pdf p6,7
    'LM5170PHPR':{'1': 'IN', '2': 'IN', '3': 'Undefined', '4': 'OUT', '5': 'Undefined', '6': 'Power', '7': 'Undefined', '8': 'IN', '9': 'IN', '10': 'IN', '11': 'Passive', '12': 'Passive', '13': 'IN', '14': 'Power', '15': 'BI', '16': 'Undefined', '17': 'BI', '18': 'Ground', '19': 'Power', '20': 'BI', '21': 'Undefined', '22': 'BI', '23': 'Power', '24': 'IN', '25': 'IN', '26': 'Passive', '27': 'BI', '28': 'IN', '29': 'IN', '30': 'IN', '31': 'Power', '32': 'Undefined', '33': 'OUT', '34': 'OUT', '35': 'IN', '36': 'IN', '37': 'OUT', '38': 'OUT', '39': 'IN', '40': 'IN', '41': 'OUT', '42': 'IN', '43': 'IN', '44': 'IN', '45': 'BI', '46': 'Ground', '47': 'IN', '48': 'IN', '49': 'Passive'},  # LM5170PHPR.pdf p3,4,5
    'LTC6811IG-1#PBF':{'1': 'Power', '2': 'IN', '3': 'BI', '4': 'IN', '5': 'BI', '6': 'IN', '7': 'BI', '8': 'IN', '9': 'BI', '10': 'IN', '11': 'BI', '12': 'IN', '13': 'BI', '14': 'IN', '15': 'BI', '16': 'IN', '17': 'BI', '18': 'IN', '19': 'BI', '20': 'IN', '21': 'BI', '22': 'IN', '23': 'BI', '24': 'IN', '25': 'BI', '26': 'IN', '27': 'BI', '28': 'BI', '29': 'BI', '30': 'Ground', '31': 'Ground', '32': 'BI', '33': 'BI', '34': 'OUT', '35': 'OUT', '36': 'IN', '37': 'Power', '38': 'OUT', '39': 'Open Collector', '40': 'IN', '41': 'IN', '42': 'IN', '43': 'IN', '44': 'Open Collector', '45': 'Passive', '46': 'IN', '47': 'BI', '48': 'BI'},  # LTC6811IG-1_PBF.pdf p16,17
    'LM4040A30IDBZR':{'1': 'BI', '2': 'Ground', '3': 'IN'},  # LM4040A30IDBZR.pdf p4,5
})
# LM5170 nFAULT为开漏输出兼外部关断输入，原厂I/O映射BI；不把它当推挽输出。
# EasyEDA Std P 字段只用于分板布局方向；Ground 与 Power 在 Std 均编码为 4。
_STD_ELECTRICAL_CODES={'Undefined':0,'IN':1,'OUT':2,'BI':3,'Open Collector':2,'Power':4,'Ground':4,'Passive':0,'HIZ':0}
EXPLICIT_ELECTRICAL_TYPES={
    mpn:{pin:_STD_ELECTRICAL_CODES[kind] for pin,kind in pins.items()}
    for mpn,pins in PROFESSIONAL_PIN_TYPES.items()
}

def convert(source, name, decoding='easyeda', encoding='easyeda-pro'):
    params={'decodingOptions':{'decodingType':decoding,'decodingFilePath':str(source)},
            'encodingOptions':{'encodingType':encoding,'savingDirPath':str(CACHE),'savingFileName':name}}
    p=CACHE/'转换参数.json'; p.write_text(json.dumps(params,ensure_ascii=False),encoding='utf8')
    # 官方解压器读取整个 ArrayBuffer；新版 Node 的 readFileSync 可能留有缓冲区尾部。
    # 只在本次子进程把二进制读取结果复制到等长缓冲区，不修改安装文件。
    preload=CACHE/'二进制读取兼容.cjs'
    preload.write_text("const fs=require('fs');const read=fs.readFileSync;fs.readFileSync=function(...a){const v=read.apply(this,a);if(!Buffer.isBuffer(v))return v;const b=Buffer.allocUnsafeSlow(v.length);v.copy(b);return b;};",encoding='utf8')
    result=subprocess.run([str(NODE),'--require',str(preload),str(ENGINE),'--cmd','conversion','--params-path',str(p)],capture_output=True,encoding='utf8',timeout=120)
    (CACHE/'转换日志.txt').write_text(result.stdout+result.stderr,encoding='utf8')
    assert result.returncode==0 and 'success: true' in result.stdout, result.stdout+result.stderr
    print(result.stdout[-1500:])

def text(s,x,y,kind='L',size=10,anchor='start',visible=1,ident=''):
    return f'T~{kind}~{x}~{y}~0~#17324D~Arial~{size}pt~normal~normal~~comment~{s}~{visible}~{anchor}~{ident}~0'

NUM=r'[-+]?(?:\d*\.\d+|\d+\.?\d*)(?:[eE][-+]?\d+)?'
def fmt(x): return f'{float(x):.5f}'.rstrip('0').rstrip('.') or '0'
def move_points(s,dx,dy):
    a=[float(x) for x in re.findall(NUM,s)]
    assert len(a)%2==0
    return ' '.join(fmt(v+(dx if i%2==0 else dy)) for i,v in enumerate(a))
def move_path(s,dx,dy):
    a=re.findall('[A-Za-z]|'+NUM,s); out=[]; i=0; first=True
    arity={'M':2,'L':2,'H':1,'V':1,'C':6,'S':4,'Q':4,'T':2,'A':7,'Z':0}
    while i<len(a):
        cmd=a[i]; assert cmd.isalpha(),s; i+=1; out.append(cmd)
        n=arity[cmd.upper()]
        while i<len(a) and not a[i].isalpha():
            v=list(map(float,a[i:i+n])); assert n and len(v)==n; i+=n
            if cmd.isupper() or first and cmd=='m':
                if cmd.upper()=='H':v[0]+=dx
                elif cmd.upper()=='V':v[0]+=dy
                elif cmd.upper()=='A':v[-2]+=dx;v[-1]+=dy
                else:v=[x+(dx if j%2==0 else dy) for j,x in enumerate(v)]
            first=False;out.extend(map(fmt,v))
    return ' '.join(out)

def shift(s,dx,dy,uid):
    chunks=s.split('^^'); f=chunks[0].split('~'); kind=f[0]
    def pair(a,i,j):a[i]=fmt(float(a[i])+dx);a[j]=fmt(float(a[j])+dy)
    if kind=='P':
        pair(f,4,5); f[7]=uid
        a=chunks[1].split('~');pair(a,0,1);chunks[1]='~'.join(a)
        a=chunks[2].split('~');a[0]=move_path(a[0],dx,dy);chunks[2]='~'.join(a)
        for k in [3,4,5]:
            a=chunks[k].split('~');pair(a,1,2);chunks[k]='~'.join(a)
        a=chunks[6].split('~');a[1]=move_path(a[1],dx,dy);chunks[6]='~'.join(a)
    elif kind in ['R','E']:pair(f,1,2);f[12 if kind=='R' else 9]=uid
    elif kind in ['PL','PG']:f[1]=move_points(f[1],dx,dy);f[6]=uid
    elif kind in ['PT','A','AR']:f[1]=move_path(f[1],dx,dy)
    else:raise ValueError(kind)
    chunks[0]='~'.join(f);return '^^'.join(chunks)

def pin(number,x,y,side,name='',electrical=0):
    left=side=='left'; rotation=180 if left else 0; sign=1 if left else -1
    anchor='start' if left else 'end'; other='end' if left else 'start'
    return (f'P~show~{electrical}~{number}~{x}~{y}~{rotation}~p{number}~0'
            f'^^{x}~{y}^^M {x} {y} h {sign*15}~#880000'
            f'^^{int(bool(name))}~{x+sign*19}~{y+3}~0~{name or number}~{anchor}~Arial~7pt~#17324D'
            f'^^1~{x+sign*8}~{y-3}~0~{number}~{other}~Arial~6pt~#17324D'
            f'^^0~{x+sign*12}~{y}^^0~M {x+sign*15} {y-3} L {x+sign*18} {y} L {x+sign*15} {y+3}')
def line(coords):return f'PL~{coords}~#880000~1~0~none~l~0'
def rect(x,y,w,h):return f'R~{x}~{y}~~~{w}~{h}~#880000~1~0~none~r~0~'

def custom(p,b):
    ref=p['ref']; nums=list(dict.fromkeys(b['引脚映射'].values())); n=len(nums)
    shapes=[]; functions=b.get('依据',{}).get('pin_functions',{})
    if n==2 and ref.startswith('J'):
        shapes=[rect(-25,-25,50,50)]
        for num,y in zip(nums,[-15,15]):
            shapes += [pin(num,-40,y,'left'),rect(-25,y-3,8,6)]
    elif p['mpn']=='STPS60150CT':
        # STPS60150CT 双二极管共阴极：1、3阳极，2及散热片阴极。
        shapes=[pin('1',-60,-20,'left',''),pin('3',-60,20,'left',''),pin('2',60,0,'right','')]
        for y in [-20,20]:
            shapes += [line(f'-45 {y} -15 {y}'),line(f'-15 {y-10} 5 {y} -15 {y+10} -15 {y-10}'),line(f'5 {y-10} 5 {y+10}'),line(f'5 {y} 25 {y} 25 0')]
        shapes += [line('25 0 45 0')]
    elif n==2:
        shapes=[pin(nums[0],-45,0,'left'),pin(nums[1],45,0,'right')]
        shapes += [line('-30 0 -15 0'),line('15 0 30 0')]
        if ref.startswith('C'):
            shapes += [line('-4 -13 -4 13'),line('4 -13 4 13'),line('-15 0 -4 0'),line('4 0 15 0')]
            if ref.startswith('C_BUS'):shapes += [line('-14 -14 -8 -14'),line('-11 -17 -11 -11')]
            elif p.get('polarized'):shapes += [line('-13 -10 -7 -10'),line('-10 -13 -10 -7')]
            if ref.startswith('C_SC_CELL'):shapes += [line('-20 -8 -12 -8'),line('-16 -12 -16 -4')]
        elif ref.startswith('L'):
            shapes += ['PT~M -15 0 C -15 -15 -5 -15 -5 0 C -5 -15 5 -15 5 0 C 5 -15 15 -15 15 0~#880000~1~0~none~p~0']
        elif ref.startswith('S'):
            closed='ESTOP' in ref
            shapes += [line(f'-15 0 15 {0 if closed else -10}'),line('0 -6 0 -18')]
        elif ref.startswith('FAN'):
            shapes += ['E~0~0~15~15~#880000~1~0~none~e~0',line('-7 7 -7 -7 0 3 7 -7 7 7')]
        elif ref.startswith('J'):
            shapes += [rect(-15,-8,30,16),line('-15 0 15 0')]
        elif ref.startswith('D'):
            # 此自建 TVS 的1脚为阴极，2脚为阳极。
            shapes += [line('-15 -10 -15 10'),line('15 -10 -15 0 15 10 15 -10')]
        else:
            shapes += [rect(-15,-7,30,14)]
            if ref.startswith('F'):shapes += [line('-15 0 15 0')]
            if ref.startswith('NTC'):shapes += [line('-20 12 18 -12'),line('-20 12 -12 12')]
    elif ref.startswith('R') and n==4:
        shapes=[pin('1',-55,0,'left',''),pin('2',55,0,'right',''),pin('3',-55,25,'left',''),pin('4',55,25,'right',''),rect(-20,-7,40,14),line('-40 0 -20 0'),line('20 0 40 0'),line('-40 25 -25 25 -25 0'),line('40 25 25 25 25 0')]
    elif ref=='K1':
        for a,c,y in [('1','2',-15),('3','4',15)]:
            shapes += [pin(a,-45,y,'left'),pin(c,45,y,'right'),line(f'-30 {y} -15 {y} 15 {y-10}'),line(f'15 {y} 30 {y}')]
        shapes += [line('0 -25 0 5')]
    else:
        # 连接器按奇偶脚分列；IC按功能标注，使用单体符号避免多单元丢电源脚。
        if ref.startswith('J'):
            left=nums[::2];right=nums[1::2];names={k:'' for k in nums}; width=60
        else:
            left=nums[:math.ceil(n/2)];right=nums[math.ceil(n/2):];names=functions;width=120
        count=max(len(left),len(right));height=max(50,count*20+10)
        shapes=[rect(-width/2,-height/2,width,height)]
        for side,ls in [('left',left),('right',right)]:
            for i,num in enumerate(ls):
                name=names.get(num,num).split('；')[0]
                explicit=EXPLICIT_ELECTRICAL_TYPES.get(p['mpn'])
                if explicit is not None:
                    electrical=explicit[str(num)]
                else:
                    # 未纳入审定的型号保留既有名字推断；这只是旧属性兼容，未核实，不能视为ERC完整。
                    electrical=2 if 'OUT' in name else 4 if name in ['VCC','GND'] else 1 if 'IN' in name else 0
                shapes.append(pin(num,(-1 if side=='left' else 1)*(width/2+15),-height/2+15+i*20,side,name,electrical))
    return {'head':{'x':0,'y':0},'shape':shapes}

def pin_info(shape):
    a=shape.split('^^');f=a[0].split('~')
    return a[4].split('~')[4],float(f[4]),float(f[5]),int(f[6])

def main(output_dir=None, report_dir=None):
    report_dir=Path(report_dir or REPORT).resolve()
    report_dir.mkdir(parents=True,exist_ok=True)
    CACHE.mkdir(parents=True,exist_ok=True)
    design=runpy.run_path(str(BASE/'设计数据.py'));parts=design['PARTS'];sections=design['SECTIONS']
    binding=json.loads((LIB/'封装绑定.json').read_text(encoding='utf8'))
    assert binding['设计源SHA256']==hashlib.sha256((BASE/'设计数据.py').read_bytes()).hexdigest()
    bindings={b['位号']:b for b in binding['位号绑定']}
    with zipfile.ZipFile(LIB/'嘉立创库数据.zip') as z:
        library={}
        for n in z.namelist():
            r=json.loads(z.read(n))['result'];d=r['dataStr'];d=json.loads(d) if isinstance(d,str) else d
            if d['shape']:library[r['title']]=d
    layout=runpy.run_path(str(TOOLS/'分板原理图.py'))
    sheets,source_nets,source_nc,inventory,reused,wiring=layout['generate'](parts,sections,bindings,library,globals())
    project={'docType':'5','title':'电机驱动原理图','schematics':[{'title':d['head']['c_para']['name'],'dataStr':d} for d in sheets]}
    source=CACHE/'原理图转换源.zip'
    with zipfile.ZipFile(LIB/'可导入封装库.zip') as fp,zipfile.ZipFile(source,'w',zipfile.ZIP_DEFLATED) as z:
        for n in fp.namelist():
            if n.endswith('.json'):
                f=json.loads(fp.read(n));f['shape']=[s for s in f['shape'] if not s.startswith('SVGNODE~')]
                for key in list(f['head'].get('c_para',{})):
                    if '3d' in key.lower():del f['head']['c_para'][key]
                z.writestr(n,json.dumps(f,ensure_ascii=False))
        z.writestr('电机驱动原理图.json',json.dumps(project,ensure_ascii=False))
    (CACHE/'分页数据.json').write_text(json.dumps(sheets,ensure_ascii=False),encoding='utf8')
    (CACHE/'核验基准.json').write_text(json.dumps({'网络':[[r,p,n] for (r,p),n in source_nets.items()],'NC':list(source_nc),'器件':inventory},ensure_ascii=False),encoding='utf8')
    convert(source,'电机驱动原理图')
    report=verify(CACHE/'电机驱动原理图.epro',parts,bindings,source_nets,source_nc)
    report.update({'页数':len(sheets),'复用嘉立创符号位号':reused,'补充符号位号':len(parts)-reused,'界面导入验收':False,'电气规则检查ERC':False,'PCB布局布线':False,'分板图面':wiring})
    # 旧格式只留缓存用于既有逐焊盘几何核验。交付使用现代交换格式和文件夹工程。
    convert(source,'电机驱动原理图',encoding='easyeda-pro-2')
    target=CACHE/'交付转换中间.epro2'
    shutil.copy2(CACHE/'电机驱动原理图.epro2',target)
    delivery=runpy.run_path(str(BASE.parent/'公共/工具/原理图交付.py'))
    flags={s['head']['c_para']['name']:s['metadata_native_flags'] for s in sheets}
    normalized=delivery['canonical_project'](Path('D:/lceda-pro/lceda-pro.exe'),target,target=output_dir,native_flags=flags,
                                             native_pin_types=PROFESSIONAL_PIN_TYPES)
    (CACHE/'规范化结果.json').write_text(json.dumps(normalized,ensure_ascii=False),encoding='utf8')
    project=Path(normalized['工程'])
    report['工程SHA256']=hashlib.sha256(project.read_bytes()).hexdigest()
    report['现代交换工程SHA256']=hashlib.sha256(target.read_bytes()).hexdigest()
    report['客户端加载及保存验收']=False
    report['ERC已执行']=False
    old_report=report_dir/'原理图核验.json'
    if old_report.exists():
        previous=json.loads(old_report.read_text(encoding='utf8'))
        if previous.get('设计源SHA256')==report['设计源SHA256'] and '本轮设计检查' in previous:
            report['本轮设计检查']=previous['本轮设计检查']
    old_report.write_text(json.dumps(report,ensure_ascii=False,indent=2),encoding='utf8')
    print(json.dumps(report,ensure_ascii=False,indent=2))

def verify(path,parts,bindings,expected,expected_nc):
    def rows(z,n):return [json.loads(s) for s in z.read(n).decode('utf8').splitlines() if s]
    actual={};ncs=set();refs=set();bound=0;checked_pads=0;smd_placeholder=0
    geometry_check=runpy.run_path(str(TOOLS/'分板原理图.py'))['board_geometry_check']
    with zipfile.ZipFile(LIB/'可导入封装库.zip') as z:
        library={n:json.loads(z.read(n)) for n in z.namelist() if n.endswith('.json')}
    with zipfile.ZipFile(path) as z:
        assert z.testzip() is None;meta=json.loads(z.read('project.json'))
        assert meta['schematics'] and not meta['pcbs']
        for name in [n for n in z.namelist() if n.endswith('.esch')]:
            r=rows(z,name);attrs=collections.defaultdict(dict)
            for a in r:
                if a[0]=='ATTR':attrs[a[2]][a[3]]=a[4]
            wires=[a for a in r if a[0]=='WIRE'];nc=[a for a in r if a[0]=='ATTR' and a[3]=='NO_CONNECT' and a[4]=='yes']
            coords={}
            for c in [a for a in r if a[0]=='COMPONENT']:
                a=attrs[c[1]];ref=a['Designator'];assert ref not in refs;refs.add(ref)
                b=bindings[ref];assert c[5]==c[6]==0
                dev=meta['devices'][a['Device']]['attributes'];assert a['Symbol']==dev['Symbol']
                assert a['Manufacturer Part']==b['型号']
                assert a['Convert to PCB']==('yes' if b['安装']=='板上' else 'no'), (ref,a)
                if b['封装']:
                    fp=dev['Footprint'];assert meta['footprints'][fp]['title']==b['封装'],ref
                    bound+=b['安装']=='板上'
                    native={str(v[5]):v for v in rows(z,f'FOOTPRINT/{fp}.efoo') if v[0]=='PAD'}
                    source=library[b['库文件']]
                    original={s.split('~')[8]:s.split('~') for s in source['shape'] if s.startswith('PAD~')}
                    assert set(native)==set(original)==set(b['引脚映射'].values()),ref
                    ox=float(source['head']['x']);oy=float(source['head']['y'])
                    for pin,pad in original.items():
                        v=native[pin];checked_pads+=1
                        want=[(float(pad[2])-ox)*10,-(float(pad[3])-oy)*10,float(pad[9])*20]
                        got=[v[6],v[7],v[9][1]]
                        assert all(abs(x-y)<0.001 for x,y in zip(want[:2],got[:2])),(ref,pin,want,got)
                        if pad[6] in ('1','2') and want[2]==0 and abs(got[2]-0.03937)<0.00001:
                            # 4.1转换器给无孔SMD写1µm最小占位值；铜层必须仍是单面。
                            smd_placeholder+=1
                        else:assert abs(want[2]-got[2])<0.001,(ref,pin,'钻孔',want[2],got[2])
                        assert v[4]=={'1':1,'2':2,'11':12}[pad[6]]
                        if pad[1] in ('RECT','OVAL','ELLIPSE'):
                            assert abs(v[10][1]-float(pad[4])*10)<0.001 and abs(v[10][2]-float(pad[5])*10)<0.001
                        # 中心对称的矩形/椭圆焊盘旋转180度具有完全相同铜形状。
                        angle=(v[8]+float(pad[11]))%180
                        assert angle<0.001 or abs(angle-180)<0.001,(ref,pin,'焊盘方向',v[8],pad[11])
                sr=rows(z,'SYMBOL/'+a['Symbol']+'.esym');pa=collections.defaultdict(dict)
                for v in sr:
                    if v[0]=='ATTR':pa[v[2]][v[3]]=v[4]
                for pinrow in [v for v in sr if v[0]=='PIN']:
                    pin=pa[pinrow[1]]['NUMBER'];xy=(round(c[3]+pinrow[4],4),round(c[4]+pinrow[5],4))
                    assert xy not in coords, (ref,pin,xy,coords.get(xy));coords[xy]=(ref,pin)
            segments=[];labels=[]
            for w in wires:
                net=attrs[w[1]].get('NET');assert net,(name,w)
                for seg in w[2]:
                    points=[(round(x/GRID),round(y/GRID)) for x,y in zip(seg[::2],seg[1::2])]
                    assert all(abs(v/GRID-round(v/GRID))<1e-5 for v in seg),w
                    segments.extend((a,b,net) for a,b in zip(points,points[1:]) if a!=b)
                visible=any(a[0]=='ATTR' and a[2]==w[1] and a[3]=='NET' and (a[5] or a[6]) for a in r)
                if visible and w[2]:
                    labels.append(((round(w[2][0][0]/GRID),round(w[2][0][1]/GRID)),net))
            pin_positions={key:((round(x/GRID),round(y/GRID)),expected[key]) for (x,y),key in coords.items() if key in expected}
            nc_positions={key:(round(x/GRID),round(y/GRID)) for (x,y),key in coords.items() if key in expected_nc}
            geometry_check(segments,pin_positions,nc_positions,labels)
            actual.update({key:net for key,(_,net) in pin_positions.items()})
            for c in nc:
                xy=(round(c[7],4),round(c[8],4));assert xy in coords,(name,c);ncs.add(coords[xy])
        if ncs!=expected_nc:
            # 名称版本差异在失败输出中保留，不能将缺少NC当作通过。
            print('NC records',[(n,[x for x in rows(z,n) if 'CONNECT' in str(x[0]) or x[0]=='NOERC']) for n in z.namelist() if n.endswith('.esch')])
        assert actual==expected,{'missing':list(set(expected.items())-set(actual.items()))[:10],'extra':list(set(actual.items())-set(expected.items()))[:10]}
        assert ncs==expected_nc,(ncs,expected_nc)
        assert refs=={p['ref'] for p in parts}
        assert not any(f.get('model_3d') for f in meta['footprints'].values())
    return {'器件':len(refs),'板上封装绑定':bound,'候选封装绑定':sum(b['安装']=='待设计' and bool(b['封装']) for b in bindings.values()),'板外器件':sum(b['安装']=='板外' for b in bindings.values()),'待设计器件':sum(b['安装']=='待设计' for b in bindings.values()),'内嵌封装':len(meta['footprints']),'逐焊盘几何核对':checked_pads,'SMD最小孔占位记录':smd_placeholder,'网络':len(set(actual.values())),'连接节点':len(actual),'明确不连接':len(ncs),'专业版回读连接一致':True,'工程SHA256':hashlib.sha256(path.read_bytes()).hexdigest(),'设计源SHA256':hashlib.sha256((BASE/'设计数据.py').read_bytes()).hexdigest()}

if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--输出目录',type=Path,help='在独立目录构建，避免改写可能仍打开的工程')
    parser.add_argument('--核验目录',type=Path,help='候选工程的核验记录位置')
    args=parser.parse_args()
    main(args.输出目录,args.核验目录)

