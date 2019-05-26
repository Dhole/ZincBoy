// build.rs

use std::collections::HashMap;
use std::env;
use std::fs::File;
use std::io;
use std::io::Write;
use std::path::Path;

extern crate inflector;
use inflector::Inflector;

#[macro_use]
extern crate maplit;

#[derive(Debug)]
struct Param {
    name: String,
    start: usize,
    end: usize,
}

#[derive(Debug)]
struct Op {
    value: String,
    mask: String,
    params: Vec<Param>,
}

fn bitarray2string(arr: [u32; 32]) -> String {
    arr.iter()
        .map(|b| b.to_string().chars().nth(0).unwrap())
        .fold(String::new(), |mut string, b| {
            string.push(b);
            string
        })
}

#[rustfmt::skip]
fn main() -> Result<(), io::Error> {
    let out_dir = env::var("OUT_DIR").unwrap();
    let dest_path = Path::new(&out_dir).join("op_raw.rs");
    let mut f = File::create(&dest_path).unwrap();

    let ops_desc = hashmap! {
    //                  |..3 ..................2 ..................1 ..................0|
    //                  |1_0_9_8_7_6_5_4_3_2_1_0_9_8_7_6_5_4_3_2_1_0_9_8_7_6_5_4_3_2_1_0|
    "data_proc_a"   => "|_Cond__|0_0_0|___Op__|S|__Rn___|__Rd___|__Shift__|Typ|0|__Rm___|",  // DataProc
    "data_proc_b"   => "|_Cond__|0_0_0|___Op__|S|__Rn___|__Rd___|__Rs___|0|Typ|1|__Rm___|",  // DataProc
    "data_proc_c"   => "|_Cond__|0_0_1|___Op__|S|__Rn___|__Rd___|_Shift_|___Immediate___|",  // DataProc
    "psr_imm"       => "|_Cond__|0_0_1_1_0|P|1|0|_Field_|__Rd___|_Shift_|___Immediate___|",  // PSR Imm
    "psr_reg"       => "|_Cond__|0_0_0_1_0|P|L|0|_Field_|__Rd___|0_0_0_0|0_0_0_0|__Rm___|",  // PSR Reg
    "branch_reg"    => "|_Cond__|0_0_0_1_0_0_1_0_1_1_1_1_1_1_1_1_1_1_1_1|0_0|L|1|__Rn___|",  // BX,BLX
    "bkpt"          => "|1_1_1_0|0_0_0_1_0_0_1_0|________imm0___________|0_1_1_1|__imm1_|",  // ARM9 =>BKPT
    "clz"           => "|_Cond__|0_0_0_1_0_1_1_0_1_1_1_1|__Rd___|1_1_1_1|0_0_0_1|__Rm___|",  // ARM9 =>CLZ
    "qalu"          => "|_Cond__|0_0_0_1_0|Op_|0|__Rn___|__Rd___|0_0_0_0|0_1_0_1|__Rm___|",  // ARM9 =>QALU
    "multiply"      => "|_Cond__|0_0_0_0_0_0|A|S|__Rd___|__Rn___|__Rs___|1_0_0_1|__Rm___|",  // Multiply
    "multiply_long" => "|_Cond__|0_0_0_0_1|U|A|S|_RdHi__|_RdLo__|__Rs___|1_0_0_1|__Rm___|",  // MulLong
    "multiply_half" => "|_Cond__|0_0_0_1_0|Op_|0|Rd_RdHi|Rn_RdLo|__Rs___|1|y|x|0|__Rm___|",  // MulHalfARM9
    "trans_swp_12"  => "|_Cond__|0_0_0_1_0|B|0_0|__Rn___|__Rd___|0_0_0_0|1_0_0_1|__Rm___|",  // TransSwp12
    "trans_reg_10"  => "|_Cond__|0_0_0|P|U|0|W|L|__Rn___|__Rd___|0_0_0_0|1|S|H|1|__Rm___|",  // TransReg10
    "trans_imm_10"  => "|_Cond__|0_0_0|P|U|1|W|L|__Rn___|__Rd___|OffsetH|1|S|H|1|OffsetL|",  // TransImm10
    "trans_imm_9"   => "|_Cond__|0_1_0|P|U|B|W|L|__Rn___|__Rd___|_________Offset________|",  // TransImm9
    "trans_reg_9"   => "|_Cond__|0_1_1|P|U|B|W|L|__Rn___|__Rd___|__Shift__|Typ|0|__Rm___|",  // TransReg9
    "undefined"     => "|_Cond__|0_1_1|________________xxx____________________|1|__yyy__|",  // Undefined
    "block_trans"   => "|_Cond__|1_0_0|P|U|S|W|L|__Rn___|__________Register_List________|",  // BlockTrans
    "branch_off"    => "|_Cond__|1_0_1|L|___________________Offset______________________|",  // B,BL,BLX
    "co_data_trans" => "|_Cond__|1_1_0|P|U|N|W|L|__Rn___|__CRd__|__CPN__|____Offset_____|",  // CoDataTrans
    "co_rr"         => "|_Cond__|1_1_0_0_0_1_0|L|__Rn___|__Rd___|__CPN__|_CPopc_|__CRm__|",  // CoRR ARM9
    "co_data_op"    => "|_Cond__|1_1_1_0|_CPopc_|__CRn__|__CRd__|__CPN__|_CP__|0|__CRm__|",  // CoDataOp
    "co_reg_trans"  => "|_Cond__|1_1_1_0|CPopc|L|__CRn__|__Rd___|__CPN__|_CP__|1|__CRm__|",  // CoRegTrans
    "swi"           => "|_Cond__|1_1_1_1|_____________Ignored_by_Processor______________|",  // SWI
    };

    let mut ops = HashMap::new();
    for (op, desc) in ops_desc.iter() {
        let elems: Vec<&str> = desc.split_at(1).1.split("|").collect();
        let mut params: Vec<Param> = Vec::new();
        let mut val = [0; 32];
        let mut mask = [0; 32];
        let mut is_param = true;
        let mut param_end = 1;
        let mut elem_idx = 0;
        for (i, c) in desc.chars().skip(1).enumerate() {
            if i % 2 == 1 && c == '|' {
                if is_param {
                    params.push(Param {
                        name: elems[elem_idx].replace("_", ""),
                        start: 31 - (i - 1) / 2,
                        end: 31 - (param_end) / 2,
                    })
                }
                elem_idx += 1;
                param_end = i + 1;
                is_param = true;
            } else if i % 2 == 0 {
                if c == '0' || c == '1' {
                    mask[i / 2] = 1;
                    val[i / 2] = if c == '1' { 1 } else { 0 };
                    is_param = false;
                } else {
                    mask[i / 2] = 0;
                    val[i / 2] = 0;
                }
            }
        }
        ops.insert(op, Op {
                value: bitarray2string(val),
                mask: bitarray2string(mask),
                params: params,
            },
        );
    }

    for (op_name, op) in &ops {
        write!(f, "pub const OP_{}_VAL:  u32 = 0b{};\n", op_name.to_uppercase(), op.value)?;
        write!(f, "pub const OP_{}_MASK: u32 = 0b{};\n\n", op_name.to_uppercase(), op.mask)?;
        let op_name = format!("op_{}", op_name).to_pascal_case();
        write!(f, "#[derive(Debug)]\n")?;
        write!(f, "pub struct {} {{\n", op_name)?;
        for param in &op.params {
            write!( f, "  {}: {},\n",
                param.name,
                if param.start == param.end { "bool" } else { "u8" }
            )?;
        }
        write!(f, "}}\n\n")?;

        write!(f, "impl {} {{\n", op_name)?;
        write!(f, "  pub fn new(v: u32) -> Self {{\n")?;
        write!(f, "    Self {{\n")?;
        let max_len = op.params.iter().max_by_key(|p| p.name.len()).unwrap().name.len();
        for param in &op.params {
            let mask = (param.start..param.end+1).map(|i| 1 << i).fold(0, |acc, x| acc+x);
            write!(f, "      {0:<max_len$}: (v & 0b{1:032b} >> {2:2}) {3},\n",
                param.name,
                mask,
                param.start,
                if param.start == param.end { "!= 0" } else { "as u8" },
                max_len = max_len
            )?;
        }
        write!(f, "    }}\n")?;
        write!(f, "  }}\n")?;
        write!(f, "}}\n\n")?;
    }

    write!(f, "#[derive(Debug)]\n")?;
    write!(f, "pub enum OpRaw {{\n")?;
    for (op_name, _) in &ops {
        write!(f, "  {0}(Op{0}),\n", op_name.to_pascal_case())?;
    }
    write!(f, "}}\n\n")?;

    let max_len_snake = ops.iter().max_by_key(|(name, _)| name.len()).unwrap().0.len();
    let max_len_pascal = ops.iter().max_by_key(|(name, _)| name.to_pascal_case().len())
        .unwrap().0.to_pascal_case().len();
    write!(f, "impl OpRaw {{\n")?;
    write!(f, "  pub fn new(v: u32) -> Self {{\n")?;
    write!(f, "    match v {{\n")?;
    for (op_name, _) in &ops {
        let pad_snake = max_len_snake - op_name.len();
        let pad_pascal = max_len_pascal - op_name.to_pascal_case().len();
        write!(f, "      _ if (v & OP_{op_up}_MASK{0:<pad0$}) == OP_{op_up}_VAL{0:<pad0$} => \
               OpRaw::{op}({0:>pad1$}{0:>pad1$}Op{op}::new(v)),\n",
               "",
               op_up= op_name.to_uppercase(),
               op=op_name.to_pascal_case(),
               pad0=pad_snake,
               pad1=pad_pascal)?;
    }
    write!(f, "      _ => unreachable!(),\n")?;
    write!(f, "    }}\n")?;
    write!(f, "  }}\n")?;
    write!(f, "}}\n")?;

    Ok(())
}
