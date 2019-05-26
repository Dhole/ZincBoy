#!/usr/bin/env python3

import sys

ops = {
        'multiply':          '....000000..............1001....',
        'multiply_long':     '....00001...............1001....',
        'single_data_swap':  '....00010.00........00001001....',
        'branch_ex':         '....0001001011111111111100.1....',
        'hwdt_reg_off':      '....000..0..........00001..1....',
        'hwdt_imm_off':      '....000..1..............1..1....',
        'dataproc':          '....001.........................',
        'single_data_trans': '....011.................1..1....',
        'undefined':         '....011....................1....',
        'block_data_trans':  '....100.........................',
        'branch':            '....101.........................',
        'co_data_trans':     '....110.........................',
        'co_data_op':        '....1110...................0....',
        'co_reg_trans':      '....1110...................1....',
        'swi':               '....1111........................',
        }

ops_desc = {
    #                 |..3 ..................2 ..................1 ..................0|
    #                 |1_0_9_8_7_6_5_4_3_2_1_0_9_8_7_6_5_4_3_2_1_0_9_8_7_6_5_4_3_2_1_0|
    'data_proc_a':   '|_Cond__|0_0_0|___Op__|S|__Rn___|__Rd___|__Shift__|Typ|0|__Rm___|',  # DataProc
    'data_proc_b':   '|_Cond__|0_0_0|___Op__|S|__Rn___|__Rd___|__Rs___|0|Typ|1|__Rm___|',  # DataProc
    'data_proc_c':   '|_Cond__|0_0_1|___Op__|S|__Rn___|__Rd___|_Shift_|___Immediate___|',  # DataProc
    'psr_imm':       '|_Cond__|0_0_1_1_0|P|1|0|_Field_|__Rd___|_Shift_|___Immediate___|',  # PSR Imm
    'psr_reg':       '|_Cond__|0_0_0_1_0|P|L|0|_Field_|__Rd___|0_0_0_0|0_0_0_0|__Rm___|',  # PSR Reg
    'branch_reg':    '|_Cond__|0_0_0_1_0_0_1_0_1_1_1_1_1_1_1_1_1_1_1_1|0_0|L|1|__Rn___|',  # BX,BLX
    'bkpt':          '|1_1_1_0|0_0_0_1_0_0_1_0|________imm0___________|0_1_1_1|__imm1_|',  # ARM9:BKPT
    'clz':           '|_Cond__|0_0_0_1_0_1_1_0_1_1_1_1|__Rd___|1_1_1_1|0_0_0_1|__Rm___|',  # ARM9:CLZ
    'qalu':          '|_Cond__|0_0_0_1_0|Op_|0|__Rn___|__Rd___|0_0_0_0|0_1_0_1|__Rm___|',  # ARM9:QALU
    'multiply':      '|_Cond__|0_0_0_0_0_0|A|S|__Rd___|__Rn___|__Rs___|1_0_0_1|__Rm___|',  # Multiply
    'multiply_long': '|_Cond__|0_0_0_0_1|U|A|S|_RdHi__|_RdLo__|__Rs___|1_0_0_1|__Rm___|',  # MulLong
    'multiply_half': '|_Cond__|0_0_0_1_0|Op_|0|Rd_RdHi|Rn_RdLo|__Rs___|1|y|x|0|__Rm___|',  # MulHalfARM9
    'trans_swp_12':  '|_Cond__|0_0_0_1_0|B|0_0|__Rn___|__Rd___|0_0_0_0|1_0_0_1|__Rm___|',  # TransSwp12
    'trans_reg_10':  '|_Cond__|0_0_0|P|U|0|W|L|__Rn___|__Rd___|0_0_0_0|1|S|H|1|__Rm___|',  # TransReg10
    'trans_imm_10':  '|_Cond__|0_0_0|P|U|1|W|L|__Rn___|__Rd___|OffsetH|1|S|H|1|OffsetL|',  # TransImm10
    'trans_imm_9':   '|_Cond__|0_1_0|P|U|B|W|L|__Rn___|__Rd___|_________Offset________|',  # TransImm9
    'trans_reg_9':   '|_Cond__|0_1_1|P|U|B|W|L|__Rn___|__Rd___|__Shift__|Typ|0|__Rm___|',  # TransReg9
    'undefined':     '|_Cond__|0_1_1|________________xxx____________________|1|__yyy__|',  # Undefined
    'block_trans':   '|_Cond__|1_0_0|P|U|S|W|L|__Rn___|__________Register_List________|',  # BlockTrans
    'branch_off':    '|_Cond__|1_0_1|L|___________________Offset______________________|',  # B,BL,BLX
    'co_data_trans': '|_Cond__|1_1_0|P|U|N|W|L|__Rn___|__CRd__|__CPN__|____Offset_____|',  # CoDataTrans
    'co_rr':         '|_Cond__|1_1_0_0_0_1_0|L|__Rn___|__Rd___|__CPN__|_CPopc_|__CRm__|',  # CoRR ARM9
    'co_data_op':    '|_Cond__|1_1_1_0|_CPopc_|__CRn__|__CRd__|__CPN__|_CP__|0|__CRm__|',  # CoDataOp
    'co_reg_trans':  '|_Cond__|1_1_1_0|CPopc|L|__CRn__|__Rd___|__CPN__|_CP__|1|__CRm__|',  # CoRegTrans
    'swi':           '|_Cond__|1_1_1_1|_____________Ignored_by_Processor______________|',  # SWI
    }


def pattern(val, mask):
    return ''.join([v if m == '1' else '.' for (m, v) in zip(mask, val)])


ops = {}
for op, desc in ops_desc.items():
    elems = desc[1:].split('|')
    val, mask, = '', ''
    params = []
    elem_idx = 0
    is_param = True
    start = 1
    for i in range(1, 65):
        c = desc[i]
        if c == '|':
            if is_param:
                name = elems[elem_idx].replace('_', '')
                params.append((name, 31 - (i-1)//2, 31 - (start-1)//2))
            elem_idx += 1
            start = i+1
            is_param = True
            continue
        if i % 2 == 1:
            if c == '1' or c == '0':
                mask += '1'
                val += c
                is_param = False
            else:
                mask += '0'
                val += '0'

    ops[op] = (val, mask, params)
    # print(params)
    # print(pattern(val, mask))

print(ops)
sys.exit(0)

for op, data in ops.items():
    (val, mask, params) = data
    print(f'const op_{op}_val:  u32 = 0b{val};')
    print(f'const op_{op}_mask: u32 = 0b{mask};')
    op_name = f'op_{op}'
    print(f'struct {op_name} {{')
    for (name, start, end) in params:
        typ = 'u8'
        if start == end:
            typ = 'bool'
        print(f'  {name}: {typ},')
    print('}')

    print(f'impl {op_name} {{')
    print('  fn new(v: u32) -> Self {')
    print('    Self {')
    max_len_par = max(params, key=lambda p: len(p[0]))
    max_len = len(max_len_par[0])
    for (name, start, end) in params:
        cast = 'as u8'
        if start == end:
            cast = '!= 0'
        mask = 0x00000000 | sum([1 << i for i in range(start, end+1)])
        shift = start
        print('      {0:<{max_len}}: (v & 0b{1:032b} >> {2:02}) {3},'
              .format(name, mask, shift, cast, max_len=max_len))
    print('    }')
    print('  }')
    print('}')

print('enum OpRaw {')
for op, data in ops.items():
    print(f'  {op}(op_{op}),')
print('}')

max_len_op = max(ops.keys(), key=lambda op: len(op))
max_len = len(max_len_op)
print('impl OpRaw {')
print('  fn new(v: u32) -> Self {')
print('    match v {')
for op, data in ops.items():
    pad = ' ' * (max_len - len(op))
    print('      _ if (v & op_{op}_mask{pad}) == op_{op}_val{pad} => OpRaw::{op}{pad}({pad}op_{op}::new(v)),'
          .format(op=op, pad=pad))
print('      _ => unreachable!(),')
print('    }')
print('  }')
print('}')
