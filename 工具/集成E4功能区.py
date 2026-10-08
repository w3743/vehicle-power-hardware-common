"""FOC E4 原理图功能分区适配器；只消费稳定 PARTS，不改电气源。"""
from __future__ import annotations

import re


def _series5(n: int) -> str:
    return f"20S串联电容与检修链·{(n - 1) // 5 + 1}组（{(n - 1) // 5 * 5 + 1}至{(n - 1) // 5 * 5 + 5}）"


def _cell_group(first: int) -> str:
    lo = ((first - 1) // 5) * 5 + 1
    return f"20S逐节硬保护与采样·{(lo - 1) // 5 + 1}组（{lo}至{lo + 4}）"


def _central_role(p):
    r = p['ref']
    # The floating SOURCE return is a real local gate-driver circuit. Keep
    # its PSU/receiver with its MOS and OFF monitor instead of spanning rows.
    if r in {'PSU_SC_GATE_BUS','C_SC_GATE_BUS_IN','C_SC_GATE_BUS_OUT','U_SC_PORT_DRV'}:
        return 'BUS端口保险、磁件、分流与局部储能'
    if r in {'PSU_SC_GATE_CAP','C_SC_GATE_CAP_IN','C_SC_GATE_CAP_OUT'}:
        return 'CAP端口保险、磁件、分流与局部储能'
    # Power-path topology: keep each complete four-switch bridge and its
    # physical SW1--inductor--SW2 path together on the corresponding phase.
    m = re.fullmatch(r'C_SC_CELL(\d+)', r)
    if m:
        return _series5(int(m.group(1)))
    # 逐节常驻检修支路已于2026-10-07整体取消，其旧位号映射随之删除；
    # 该位号若再现，应按下方"未归属"显式报错，而不是静默并回串联组。
    m = re.fullmatch(r'R_Q_SC_P([12])_.*', r)
    if m:
        return f"双向桥相{m.group(1)}开关、门极与电感通路"
    m = re.fullmatch(r'(?:U|R|C|Q|D|L)_SC_P([12])(?:_|$).*', r)
    if m:
        phase = m.group(1)
        if (r.startswith(('Q_SC_P' + phase, 'R_Q_SC_P' + phase,
                          'D_SC_P' + phase, 'L_SC_P' + phase))
                or re.match(r'^(?:R|C)_SC_P' + phase + r'(?:BUS|CAP|IND|OUT|CSP|CSN|IMON)', r)):
            return f"双向桥相{phase}开关、门极与电感通路"
        if 'IMON' in r or r.endswith('_I') or 'PHASE' in r:
            return f"双向桥相{phase}电流测量与命令"
        return f"双向桥相{phase}控制器与补偿"
    if r in {'U_SC_SIGNED_CMD', 'C_SC_SIGNED_CMD'} or r.startswith((
            'R_SC_OP_', 'R_SC_ON_', 'R_SC_DAC_', 'R_SC_IMON_', 'R_SC_INJECT_')):
        return '双向桥互补电流命令与模拟接口'
    if re.fullmatch(r'C_SC_P[12]_IMON_(?:OP|ON)', r):
        return '双向桥互补电流命令与模拟接口'

    # Four continuous five-cell series segments; the segment names are visual
    # group names only. Existing SC_CELL_n nets remain the single real chain.
    cell_patterns = (
        r'R_SC_HW_LEAD(\d+)', r'U_SC_CELL_DIFF(\d+)', r'C_SC_DIFF(\d+)_',
        r'R_SC_HW_MIX(\d+)', r'Q_SC_REF_GND(\d+)', r'R_SC_REF_GND(\d+)',
        r'D_SC_REF_GS(\d+)',
    )
    m = next((x for pattern in cell_patterns if (x := re.search(pattern, r))), None)
    if m:
        return _cell_group(int(m.group(1)))
    m = re.fullmatch(r'(?:U|C)_SC_CELL_PAIR(\d+)', r)
    if m:
        return _cell_group(2 * int(m.group(1)) - 1)

    for bank in (0, 1):
        if f'SC_AFE{bank}_' in r or r in (f'U_SC_AFE{bank}',) or r.startswith(f'NTC_SC_AFE{bank}_'):
            return f"20S隔离AFE、偏置与采样链·{bank + 1}组"
    if r.startswith(('U_SC_AFE_UP_ISO', 'R_SC_AFE1_LED', 'Q_SC_AFE1_LED',
                     'R_SC_AFE1_RX_', 'C_U_SC_AFE')):
        return 'AFE双组健康隔离与链间接口'

    # Port-specific actual protection / precharge / measurement; bridge
    # switches above are deliberately excluded from these connector groups.
    if r in ('J_CENTRAL_BUS', 'J_CENTRAL_CAP') or r.startswith(('C_BUS_BULK',)):
        return '公共BUS储能与中央端口连接'
    for key, title in (('HV', 'BUS'), ('LV', 'CAP')):
        if (re.search(r'(?:^|_)SC_' + key + r'_', r) or
                r.startswith(('F_SC_' + key, 'Q_SC_' + key, 'D_SC_PORT_' + key,
                               'L_SC_PORT_' + key, 'R_SC_PORT_' + key,
                               'C_SC_PORT_' + key, 'J_SC_PORT_' + key,
                               'U_SC_' + key + '_'))):
            if any(t in r for t in ('DIFF', 'PRE', 'REQUEST', 'LATCH', 'MAINT', 'DELAY')):
                return f"{title}端口差压资格、预充与异步关断"
            return f"{title}端口保险、磁件、分流与局部储能"
    if r.startswith(('U_SC_BUS_TOTAL', 'U_SC_CAP_TOTAL', 'R_SC_BUS_TOTAL',
                      'R_SC_CAP_TOTAL', 'C_SC_BUS_INA', 'C_SC_CAP_INA',
                      'U_SC_PHASE1_I', 'C_SC_PHASE1_INA')) or r in {
            'R_SC_PHASE1_ADC_LP', 'C_SC_PHASE1_ADC_LP'}:
        return 'BUS/CAP端口总电流与相电流采样'
    if r.startswith(('R_SC_BUS_INNER_', 'R_SC_CAP_INNER_', 'U_SC_BUS_INNER_',
                      'U_SC_CAP_INNER_', 'C_SC_BUS_INNER_', 'C_SC_CAP_INNER_')):
        return 'BUS/CAP内侧端压监督'
    if r.startswith(('R_SC_BUS_V_', 'R_SC_CAP_V_', 'U_SC_BUS_V_', 'U_SC_CAP_V_',
                     'C_SC_BUS_V', 'C_SC_CAP_V')):
        return 'BUS/CAP电压分压、隔离与ADC'
    if r.startswith(('R_SC_BUS_', 'R_SC_CAP_', 'U_SC_BUS_', 'U_SC_CAP_',
                     'C_SC_BUS_', 'C_SC_CAP_')):
        return 'BUS/CAP端口电压与电流采样'

    if r.startswith(('SC_D1_', 'SC_D2_', 'R_SC_D1_', 'R_SC_D2_', 'C_SC_D1_',
                     'C_SC_D2_', 'Q_SC_D1_', 'Q_SC_D2_', 'U_SC_D1_', 'U_SC_D2_',
                     'D_SC_D1_', 'D_SC_D2_', 'J_SC_D1_', 'J_SC_D2_',
                     'NTC_SC_D1_', 'NTC_SC_D2_')):
        return '独立泄放支路1' if ('D1_' in r or 'DUMP1' in r) else '独立泄放支路2'
    if 'DUMP1' in r or 'DUMP_MAIN' in r or 'DUMP_TEMP_MAIN' in r:
        return '独立泄放支路1'
    if 'DUMP2' in r or 'DUMP_BACKUP' in r or 'DUMP_TEMP_BACKUP' in r:
        return '独立泄放支路2'

    if r.startswith(('SC_MAIN_', 'SC_ISO_', 'SC_U_SC_10V', 'SC_R_SC_10V',
                     'SC_C_SC_10V', 'SC_L_SC_10V', 'SC_C_MAIN_', 'SC_C_ISO_',
                     'C_SC_MAIN_VIN', 'C_SC_ISO_VIN')):
        return 'BUS输入双路MAIN12与浮置ISO12供电'
    if r.startswith(('SC_U_AUX_EFUSE', 'SC_R_AUX_', 'SC_C_AUX_EFUSE')):
        return 'BUS输入保险与偏置前端保护'
    if r.startswith(('PSU_SC_GATE_', 'C_SC_GATE_')):
        return '双向桥浮动门驱隔离电源'
    if r.startswith(('U_SC_5V', 'R_SC_5V', 'C_SC_5V', 'L_SC_5V',
                     'SC_U_SC_5V', 'SC_R_SC_5V', 'SC_C_SC_5V', 'SC_L_SC_5V')):
        return '主控与保护5V/3V3供电'
    if r.startswith(('U_SC_CAN', 'C_SC_CAN', 'J_SC_CAN', 'D_SC_CAN', 'R_SC_CAN',
                     'JP_SC_CAN', 'J_SC_CORE_',
                     'J_SC_MAINT', 'J_SC_SHIELD_BOND', 'JP_SC_TERM', 'R_SC_SPI_', 'R_SC_TERM', 'C_SC_TERM',
                     'T_SC_AFE_LINK')):
        return '主控核心板、CAN与本地维护接口'
    if r.startswith(('U_SC_EARLY_', 'R_SC_EARLY_', 'C_SC_EARLY_',
                     'U_SC_PRE_', 'R_SC_PRE_', 'C_SC_PRE_', 'Q_SC_PRE_')):
        return '本地硬件禁能、故障记忆与电源监督'
    if r == 'R_SC_RECOVERY_PERMIT_PD':
        return '本地硬件禁能、故障记忆与电源监督'
    if r in {'U_SC_NEG', 'R_SC_MAINT', 'R_SC_SWEN_REQ_PD', 'R_SC_PORT_PD',
             'R_SC_SWEN_PD', 'R_SC_SHDN_PD', 'R_SC_RVSOFF_PU',
             'R_SC_ICP', 'R_SC_ICN'} or r.startswith(('U_SC_PORT_', 'U_SC_SWEN_',
             'R_SC_SWEN_', 'C_SC_SWEN_', 'R_SC_SHDN_', 'C_SC_SHDN_',
             'R_SC_PORT_', 'C_SC_PORT_',
             'U_SC_NEG_', 'Q_SC_NEG_', 'U_SC_RUN_', 'U_SC_AFE_LOCAL_', 'U_SC_AFE0_READY',
             'U_SC_AFE1_READY', 'U_SC_HEALTH_', 'U_SC_WD', 'C_U_SC_',
             'U_SC_WIN_', 'R_SC_NEG_', 'R_SC_REF_', 'R_SC_WIN_', 'C_SC_WIN_', 'R_SC_HEALTH_',
             'R_SC_UV_', 'R_SC_OV_', 'R_SC_WD', 'C_SC_WD', 'R_SC_5_UV', 'R_SC_5_OV',
             'C_SC_NEG_', 'C_SC_REF_', 'C_SC_REF25', 'C_SC_WD',
             'U_SC_REF25', 'U_SC_5_MON')):
        return '本地硬件禁能、故障记忆与电源监督'
    if r.startswith(('R_SC_BUS_V_', 'R_SC_CAP_V_', 'U_SC_BUS_V_', 'U_SC_CAP_V_',
                     'C_SC_BUS_V', 'C_SC_CAP_V')):
        return 'BUS/CAP电压分压、隔离与ADC'
    if r.startswith(('U_SC_BUS_TOTAL', 'U_SC_CAP_TOTAL', 'R_SC_BUS_TOTAL',
                      'R_SC_CAP_TOTAL', 'C_SC_BUS_INA', 'C_SC_CAP_INA',
                      'U_SC_PHASE1_I', 'C_SC_PHASE1_INA')):
        return 'BUS/CAP端口总电流与相电流采样'
    if r.startswith(('R_SC_BUS_INNER_V_', 'R_SC_CAP_INNER_V_',
                     'U_SC_BUS_INNER_ADC_', 'U_SC_CAP_INNER_ADC_')):
        return 'BUS/CAP内侧端压监督'
    # Auxiliary safety channels use explicit signal-family names. Keep each
    # rail/current protection circuit as a single semantic role, not a BOM tile.
    if any(t in r for t in ('_OCP', '_OC_', '_OV_', '_UV_', '_MON', '_WDT',
                            '_READY', '_HEALTH', '_FAULT', '_CLR', '_AND', '_INV', '_OK_')):
        return '本地硬件保护、状态组合与复位'
    if '_DIFF' in r:
        return '端口差压检测与公共安全组合'
    if r.startswith(('R_SC_', 'C_SC_', 'U_SC_', 'D_SC_', 'Q_SC_', 'F_SC_',
                     'L_SC_', 'J_SC_', 'PSU_SC_', 'NTC_SC_', 'SC_')):
        # A final explicit fallback by circuit section is intentionally absent:
        # unknown refs must be reviewed and assigned rather than silently tiled.
        raise AssertionError(('中央新位号无E4功能区规则', r, p.get('section'), p.get('mpn')))
    raise AssertionError(('中央位号格式未知', r, p.get('section'), p.get('mpn')))


def _central_positions(group, preparations, title, helper, scope, old_positions):
    refs = {p['ref'] for p in group}
    if title.startswith('20S串联电容与检修链'):
        pos = {}
        nums = sorted(int(m.group(1)) for r in refs if (m := re.fullmatch(r'C_SC_CELL(\d+)', r)))
        assert len(nums) == 5 and nums == list(range(nums[0], nums[0] + 5)), (title, nums)
        # 逐节常驻检修泄放支路（F_SC_SERVICE*/R_SC_SERVICE*）已于2026-10-07
        # 按整体取消；本组现在只含实际存在的 C_SC_CELL* 五节，不摆已删件。
        for n in nums:
            x = 320 + (n - nums[0]) * 300
            pos[f'C_SC_CELL{n}'] = (x, 430)
        assert set(pos) == refs, (title, refs ^ set(pos))
        scope['WIDTH'] = max(scope.get('WIDTH', 0), 2200)
        scope['HEIGHT'] = max(scope.get('HEIGHT', 0), 1450)
        return pos
    bridge = re.fullmatch(r'双向桥相([12])开关、门极与电感通路', title)
    if bridge:
        phase = bridge.group(1)
        expected_switches = {f'Q_SC_P{phase}_{leg}' for leg in
                             ('BUSH', 'BUSL', 'CAPH', 'CAPL')}
        switches = {r for r in refs if re.fullmatch(r'Q_SC_P[12]_(?:BUSH|BUSL|CAPH|CAPL)', r)}
        inductors = {r for r in refs if r == f'L_SC_P{phase}_POWER'}
        assert switches == expected_switches and inductors == {f'L_SC_P{phase}_POWER'}, (title, switches, inductors)
        pos = {}
        # Two synchronous half bridges face the actual phase inductor.
        anchors = {'BUSH': (420, 380), 'BUSL': (420, 900),
                   'CAPH': (1580, 380), 'CAPL': (1580, 900)}
        for leg, (x, y) in anchors.items():
            q = f'Q_SC_P{phase}_{leg}'
            pos[q] = (x, y)
            for suffix in ('', '_GS'):
                r = f'R_Q_SC_P{phase}_{leg}{suffix}'
                if r in refs:
                    pos[r] = (x - 230 if leg.endswith('H') else x + 210, y + (100 if not suffix else -90))
            if leg.endswith('H'):
                for prefix, dx, dy in (('D_SC_P', -130, -210), ('C_SC_P', -10, -210)):
                    r = f'{prefix}{phase}_{leg[:3]}_BOOT'
                    if r in refs:
                        pos[r] = (x + dx, y + dy)
        pos[f'L_SC_P{phase}_POWER'] = (1000, 640)
        # Current shunt and Kelvin/filter parts flank the physical phase path.
        for i, r in enumerate(sorted(refs - set(pos))):
            pos[r] = (780 + (i % 3) * 300, 1050 + (i // 3) * 190)
        assert set(pos) == refs, (title, refs ^ set(pos))
        scope['WIDTH'] = max(scope.get('WIDTH', 0), 2400)
        scope['HEIGHT'] = max(scope.get('HEIGHT', 0), 1500)
        return pos
    if helper is not None and len(group) > 1:
        positions, width, height = helper(
            group, preparations,
            lambda net: scope.get('_rail', lambda n: n in {'BUS_MINUS', 'BUS_PLUS', 'SC_5V', 'SC_3V3'})(net),
        )
        scope['WIDTH'] = width
        scope['HEIGHT'] = height
        assert set(positions) == refs, (title, refs ^ set(positions))
        return positions
    pos = old_positions(group, preparations, title)
    assert set(pos) == refs, (title, refs ^ set(pos))
    return pos


def install(c, scope, complete_circuit_positions=None):
    """Install callbacks into the per-run scope. No source/cache writes."""
    old_function = scope['_function']
    old_positions = scope['_positions']
    old_bands = scope['_board_bands']
    old_main_power = scope['is_main_power']

    main_power_nets = {
        'BUS_PLUS', 'SC_BUS_POWER', 'SC_CAP_POWER',
        'SC_HV_OFF_AFTER', 'SC_HV_FUSED', 'SC_BUS_SHUNT_OUT', 'SC_HV_CHOKE_AFTER',
        'SC_CAP_SHUNT_IN', 'SC_CAP_PORT_SHUNT_IN', 'SC_LV_FUSED', 'SC_LV_CHOKE_AFTER',
        'SC_HV', 'SC_LV', 'SC_CELL_20', 'SC_CAP_FUSED',
        'FOC_FUSED', 'FOC_SWITCHED', 'K1_LINK',
        'AUX_BUS_FUSED', 'AUX_OR_RAW', 'AUX_IN', 'MOD15_IN', 'MOD_MAIN12_IN', 'MOD5_IN',
    }

    def is_main_power(net):
        if net == 'BUS_MINUS':
            return False
        if net in main_power_nets:
            return True
        return old_main_power(net) or bool(re.fullmatch(
            r'(?:SC_CELL_(?:[1-9]|1[0-9]|20)|SC_P[12]_(?:SW[12]|LOW_SOURCE))', net
        ))

    def role(p):
        board = p.get('board')
        if board == '中央稳压模块':
            return _central_role(p)
        if board == '辅助电源板':
            r = p['ref']
            can = {'J_AUX_CAN_1', 'J_AUX_CAN_2', 'D_AUX_CAN', 'R_AUX_TERM',
                   'JP_AUX_TERM', 'J_AUX_SHIELD_BOND'}
            if r in can:
                return '双CAN被动并联与可选终端'
            power = {
                'F_AUXBUS', 'D_AUXBUS', 'D_AUXTVS', 'J_AUXBUS_IN',
                'U_AUX_EFUSE', 'R_AUX_ILIM1', 'R_AUX_ILIM2', 'R_AUX_UV_T',
                'R_AUX_UV_B', 'R_AUX_OV_T', 'R_AUX_OV_B', 'C_AUX_EFUSE_IN',
                'C_AUX_EFUSE_DVDT', 'F_MOD1', 'F_MAIN1', 'F_MOD2', 'J_AUX_OR_OUT',
            }
            if r in power:
                if r in {'F_AUXBUS', 'D_AUXBUS', 'D_AUXTVS', 'J_AUXBUS_IN'}:
                    return '母线输入保护与辅助馈电'
                if r in {'U_AUX_EFUSE', 'R_AUX_ILIM1', 'R_AUX_ILIM2', 'R_AUX_UV_T',
                         'R_AUX_UV_B', 'R_AUX_OV_T', 'R_AUX_OV_B', 'C_AUX_EFUSE_IN',
                         'C_AUX_EFUSE_DVDT'}:
                    return '受控电子保险与欠过压保护'
                return '板外固定模块支路与保险分配'
            raise AssertionError(('辅助板E4未归属', r, p.get('section'), p.get('mpn')))
        if board == '驱动主板':
            r=p['ref']
            if p['section']=='01_input':return '公共BUS输入保险、手断与桥分流'
            modules={'J_MOD15_IN':'主板15V模块','J_MAIN12_IN':'主板主12V模块','J_MOD5_IN':'主板5V模块'}
            if r in modules:return modules[r]
            if r in {'J_FAN','FAN1'}:return '主12V风扇接口'
            if r in {'U_EFUSE1','U_OVP5_CLAMP','D_EFUSE5_OV_ISO','R_EFUSE5_REF_BIAS','R_EFUSE5_OV_TOP','R_EFUSE5_OV_BOT','R_EFUSE5_ILIM','C_EFUSE5_IN','C_EFUSE5_DVDT','C_EFUSE5_OUT'}:return '主5V本地欠过压与限流保护'
            if r.startswith(('R_FOC_OV_', 'C_FOC_OV_')) or r in {'U13','U14','C_OV','C_REF_IN','C_REF_NR','C_REF_OUT','C_COMP'}:
                return '本地硬OV参考、采样与异步撤桥'
            if r.startswith(('R_FOC_I_', 'C_FOC_I_')) or r in {'U_FOC_I_BUFFER','U_BRIDGE_SENSE','R_BRIDGE_SP','R_BRIDGE_SM','C_BRIDGE_DIFF','R_BRIDGE_ADC','C_BRIDGE_ADC','C_BRIDGE_VDD'}:
                return '桥净电流采样与双极平均滤波'
            if r.startswith(('U_OCP_', 'C_U_OCP_')):
                return '三相硬OCP组合与故障锁存'
            if r=='J_SHIELD_BOND':
                return 'CAN通信接口'
        if board == '驱动主板' and (p['ref']=='C_FOC_LOCAL' or p['ref'].startswith('C_FOC_COMMUTATION')):
            return '桥本地母线储能与换相电容'
        result = old_function(p)
        if not result:
            raise AssertionError(('E4位号未归属功能区', p.get('ref'), board, p.get('section')))
        return result

    def positions(group, preparations, title):
        if group and all(p.get('board') == '中央稳压模块' for p in group):
            return _central_positions(group, preparations, title, complete_circuit_positions, scope, old_positions)
        if group and all(p.get('board') == '辅助电源板' for p in group):
            pos = {}
            role_name = title
            by_role = {p['ref']: role(p) for p in group}
            if role_name == '双CAN被动并联与可选终端':
                coords = {'J_AUX_CAN_1': (250, 450), 'D_AUX_CAN': (850, 450),
                          'J_AUX_CAN_2': (1450, 450), 'R_AUX_TERM': (850, 700),
                          'JP_AUX_TERM': (1100, 700), 'J_AUX_SHIELD_BOND': (1450, 700)}
            elif role_name == '母线输入保护与辅助馈电':
                coords = {'J_AUXBUS_IN': (250, 450), 'F_AUXBUS': (620, 450),
                          'D_AUXBUS': (980, 450), 'D_AUXTVS': (980, 760)}
            elif role_name == '受控电子保险与欠过压保护':
                coords = {'C_AUX_EFUSE_IN': (250, 450), 'U_AUX_EFUSE': (950, 600),
                          'C_AUX_EFUSE_DVDT': (1350, 850), 'R_AUX_ILIM1': (520, 900),
                          'R_AUX_ILIM2': (700, 900), 'R_AUX_UV_T': (520, 1150),
                          'R_AUX_UV_B': (700, 1150), 'R_AUX_OV_T': (1180, 1150),
                          'R_AUX_OV_B': (1360, 1150)}
            elif role_name == '板外固定模块支路与保险分配':
                coords = {'F_MOD1': (250, 450), 'F_MAIN1': (750, 450),
                          'F_MOD2': (1250, 450), 'J_AUX_OR_OUT': (1750, 450)}
            else:
                raise AssertionError(('辅助板未知功能区', title, by_role))
            coords = {r: xy for r, xy in coords.items() if r in by_role}
            assert set(coords) == set(by_role), (title, set(coords) ^ set(by_role))
            scope['WIDTH'] = max(scope.get('WIDTH', 0), 2200)
            scope['HEIGHT'] = max(scope.get('HEIGHT', 0), 1500)
            return coords
        if title == '桥本地母线储能与换相电容':
            own=sorted(group,key=lambda p: 0 if p['ref']=='C_FOC_LOCAL' else int(p['ref'].removeprefix('C_FOC_COMMUTATION')))
            assert len(own)==17
            pos={p['ref']:(250+(i%4)*360,300+(i//4)*250) for i,p in enumerate(own)}
            scope['WIDTH']=2200;scope['HEIGHT']=1700
            return pos
        if title=='公共BUS输入保险、手断与桥分流':
            pos={'J_BAT_1':(200,330),'F1':(520,330),'K1':(900,330),'R_BRIDGE':(1420,330),'D_TVS':(1420,900),'R_BLEED':(1740,900),'J_BAT_2':(200,1000)}
            assert set(pos)=={p['ref'] for p in group};scope['WIDTH']=2400;scope['HEIGHT']=1500
            return pos
        retained={'核心板与PWM接口','三相栅极驱动','U相功率桥','V相功率桥','W相功率桥','A相电流快速保护','B相电流快速保护','C相电流快速保护','过流窗口基准','主板15V模块','主板主12V模块','主板5V模块'}
        if group[0]['board']=='驱动主板' and title not in retained:
            pos,width,height=complete_circuit_positions(group,preparations,scope['_rail'])
            scope['WIDTH']=width;scope['HEIGHT']=height
            assert set(pos)=={p['ref'] for p in group}
            return pos
        if title in {'本地硬OV参考、采样与异步撤桥','桥净电流采样与双极平均滤波','三相硬OCP组合与故障锁存'}:
            assert complete_circuit_positions is not None
            pos,width,height=complete_circuit_positions(group,preparations,scope['_rail'])
            scope['WIDTH']=width;scope['HEIGHT']=height
            assert set(pos)=={p['ref'] for p in group}
            return pos
        pos = old_positions(group, preparations, title)
        pos = {r:xy for r,xy in pos.items() if r in {p['ref'] for p in group}}
        assert set(pos) == {p['ref'] for p in group}, (title, {p['ref'] for p in group} ^ set(pos))
        return pos

    scope['_function'] = role
    scope['_positions'] = positions
    scope['is_main_power'] = is_main_power
    def board_bands(board, blocks):
        for b in blocks:
            b['metadata']['circuit_role'] = b['metadata']['title']
        return region_rows(board, {b['metadata']['circuit_role'] for b in blocks}, blocks, old_bands)
    scope['_board_bands'] = board_bands
    return scope


def regions(physical):
    """3-D semantic plan: rows contain zones, each zone contains role names."""
    if physical == '驱动主板':
        return [
            [['公共BUS输入保险、手断与桥分流','母线与辅助电源接口', '辅助电源分配', '电池输入与母线', '电池两级反向阻断', '预充电压确认', '接触器线圈驱动']],
            [['U相功率桥', 'V相功率桥', 'W相功率桥']],
            [['桥本地母线储能与换相电容']],
            [['三相栅极驱动', '核心板与PWM接口', '硬件联锁与驱动许可', '复位及独立看门狗']],
            [['A相电流快速保护', 'B相电流快速保护', 'C相电流快速保护', '过流窗口基准']],
            [['电池电流采样', '母线电压采样', '模拟输入与温度', '桥净电流采样与双极平均滤波']],
            [['本地硬OV参考、采样与异步撤桥','三相硬OCP组合与故障锁存']],
            [['主12V独立监督', '主泄放比较与电压窗', '主泄放功率与温控']],
            [['CAN通信接口', '霍尔输入接口']],
            [['备用泄放比较与电压窗·1', '备用泄放比较与电压窗·2', '备用泄放功率与温控']],
            [['主5V本地欠过压与限流保护','主12V风扇接口','主板电源模块', '主板15V模块', '主板主12V模块', '主板5V模块', '主板备用12V模块', '主板线圈12V模块']],
        ]
    if physical == '辅助电源板':
        return [[['母线输入保护与辅助馈电', '受控电子保险与欠过压保护']],
                [['板外固定模块支路与保险分配']],
                [['双CAN被动并联与可选终端']]]
    if physical == '中央稳压模块':
        return [
            [['BUS端口保险、磁件、分流与局部储能', '双向桥相1开关、门极与电感通路', '双向桥相2开关、门极与电感通路', 'CAP端口保险、磁件、分流与局部储能']],
            [['BUS端口差压资格、预充与异步关断', 'CAP端口差压资格、预充与异步关断', '公共BUS储能与中央端口连接']],
            [['BUS输入保险与偏置前端保护', 'BUS输入双路MAIN12与浮置ISO12供电', '主控与保护5V/3V3供电', '双向桥浮动门驱隔离电源']],
            [['双向桥相1控制器与补偿', '双向桥相2控制器与补偿', '双向桥相1电流测量与命令', '双向桥相2电流测量与命令', '双向桥互补电流命令与模拟接口']],
            [['20S串联电容与检修链·1组（1至5）', '20S串联电容与检修链·2组（6至10）', '20S串联电容与检修链·3组（11至15）', '20S串联电容与检修链·4组（16至20）']],
            [['20S逐节硬保护与采样·1组（1至5）'], ['20S逐节硬保护与采样·2组（6至10）'], ['20S逐节硬保护与采样·3组（11至15）'], ['20S逐节硬保护与采样·4组（16至20）']],
            [['20S隔离AFE、偏置与采样链·1组', '20S隔离AFE、偏置与采样链·2组', 'AFE双组健康隔离与链间接口']],
            [['BUS/CAP端口总电流与相电流采样', 'BUS/CAP端口电压与电流采样', 'BUS/CAP电压分压、隔离与ADC', 'BUS/CAP内侧端压监督']],
            [['独立泄放支路1', '独立泄放支路2']],
            [['本地硬件禁能、故障记忆与电源监督', '本地硬件保护、状态组合与复位', '端口差压检测与公共安全组合', '主控核心板、CAN与本地维护接口']],
        ]
    raise AssertionError(('未知E4物理板', physical))


def region_heading(physical, roles):
    if physical != '中央稳压模块':
        return ' / '.join(roles)
    first = roles[0]
    headings = {
        'BUS端口保险、磁件、分流与局部储能': '双向功率通路',
        'BUS端口差压资格、预充与异步关断': '预充与公共储能',
        'BUS输入保险与偏置前端保护': '偏置供电',
        '双向桥相1控制器与补偿': '双相控制与命令',
        '20S串联电容与检修链·1组（1至5）': '20S串联与检修',
        '20S隔离AFE、偏置与采样链·1组': '20S隔离采样',
        'BUS/CAP端口总电流与相电流采样': '端口采样',
        '独立泄放支路1': '独立双泄放',
        '本地硬件禁能、故障记忆与电源监督': '本地保护与CAN',
    }
    if first.startswith('20S逐节硬保护与采样·'):
        return '20S硬保护·' + first.split('·', 1)[1].split('（', 1)[0]
    assert first in headings, ('中央区域标题无简短映射', roles)
    return headings[first]


def region_rows(physical, roles, blocks, old_bands=None):
    """Return block objects in visual rows; every block is consumed once."""
    byrole = {}
    for b in blocks:
        meta = b.setdefault('metadata', {})
        role = meta.setdefault('circuit_role', meta.get('title'))
        if not role or role in byrole:
            raise AssertionError(('功能区block缺失或重复', physical, role))
        byrole[role] = b
    present = set(byrole)
    planned = regions(physical)
    rows = [[byrole[role] for zone in row for role in zone if role in present] for row in planned]
    rows = [row for row in rows if row]
    assigned_ids = [id(b) for row in rows for b in row]
    extras = sorted(present - {b['metadata']['circuit_role'] for row in rows for b in row})
    if extras:
        raise AssertionError(('功能区未进入E4布局计划', physical, extras))
    if len(assigned_ids) != len(blocks) or len(set(assigned_ids)) != len(blocks):
        raise AssertionError(('block未恰好布局一次', physical, len(blocks), len(assigned_ids)))
    return rows
