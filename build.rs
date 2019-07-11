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

enum ParamType {
    Bool,
    U8,
    U16,
    U32,
}

impl Param {
    fn typ(&self) -> ParamType {
        let len = self.end - self.start;
        if len == 0 {
            return ParamType::Bool;
        } else if len > 15 {
            return ParamType::U32;
        } else if len > 7 {
            return ParamType::U16;
        } else {
            return ParamType::U8;
        }
    }
}

#[derive(Debug)]
struct Op {
    value: String,
    mask: String,
    params: Vec<Param>,
    priority: u8, // use priorities so that some op are matched before others in ambiguos cases
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
    //                   |..3 ..................2 ..................1 ..................0|
    //                   |1_0_9_8_7_6_5_4_3_2_1_0_9_8_7_6_5_4_3_2_1_0_9_8_7_6_5_4_3_2_1_0|
    "branch_reg"    => ("|_Cond__|0_0_0_1_0_0_1_0_1_1_1_1_1_1_1_1_1_1_1_1|0_0|L|1|__Rn___|", 0),  // BX,BLX *
    // "bkpt"       => ("|1_1_1_0|0_0_0_1_0_0_1_0|________imm0___________|0_1_1_1|__imm1_|", 1),  // ARM9:BKPT
    // "clz"        => ("|_Cond__|0_0_0_1_0_1_1_0_1_1_1_1|__Rd___|1_1_1_1|0_0_0_1|__Rm___|", 1),  // ARM9:CLZ
    "multiply"      => ("|_Cond__|0_0_0_0_0_0|A|S|__Rd___|__Rn___|__Rs___|1_0_0_1|__Rm___|", 1),  // Multiply *
    "multiply_long" => ("|_Cond__|0_0_0_0_1|U|A|S|_RdHi__|_RdLo__|__Rs___|1_0_0_1|__Rm___|", 0),  // MulLong *
    // "qalu"       => ("|_Cond__|0_0_0_1_0|Op_|0|__Rn___|__Rd___|0_0_0_0|0_1_0_1|__Rm___|", 1),  // ARM9:QALU
    "trans_swp_12"  => ("|_Cond__|0_0_0_1_0|B|0_0|__Rn___|__Rd___|0_0_0_0|1_0_0_1|__Rm___|", 0),  // TransSwp12 *
    "data_proc_a"   => ("|_Cond__|0_0_0|___Op__|S|__Rn___|__Rd___|__Shift__|Typ|0|__Rm___|", 1),  // DataProc *
    "data_proc_b"   => ("|_Cond__|0_0_0|___Op__|S|__Rn___|__Rd___|__Rs___|0|Typ|1|__Rm___|", 1),  // DataProc *
    "data_proc_c"   => ("|_Cond__|0_0_1|___Op__|S|__Rn___|__Rd___|_Shift_|___Immediate___|", 1),  // DataProc *
    "trans_imm_10"  => ("|_Cond__|0_0_0|P|U|1|W|L|__Rn___|__Rd___|OffsetH|1|S|H|1|OffsetL|", 1),  // TransImm10 *
    "trans_reg_10"  => ("|_Cond__|0_0_0|P|U|0|W|L|__Rn___|__Rd___|0_0_0_0|1|S|H|1|__Rm___|", 1),  // TransReg10 *
    "trans_imm_9"   => ("|_Cond__|0_1_0|P|U|B|W|L|__Rn___|__Rd___|_________Offset________|", 1),  // TransImm9 *
    "trans_reg_9"   => ("|_Cond__|0_1_1|P|U|B|W|L|__Rn___|__Rd___|__Shift__|Typ|0|__Rm___|", 1),  // TransReg9 *
    // "multiply_half" => "|_Cond__|0_0_0_1_0|Op_|0|Rd_RdHi|Rn_RdLo|__Rs___|1|y|x|0|__Rm___|", 1),  // MulHalfARM9
    "psr_reg"       => ("|_Cond__|0_0_0_1_0|P|L|0|_Field_|__Rd___|0_0_0_0|0_0_0_0|__Rm___|", 0),  // PSR Reg *
    "psr_imm"       => ("|_Cond__|0_0_1_1_0|P|1|0|_Field_|1_1_1_1|_Shift_|___Immediate___|", 0),  // PSR Imm *
    "undefined"     => ("|_Cond__|0_1_1|________________xxx____________________|1|__yyy__|", 1),  // Undefined *
    "block_trans"   => ("|_Cond__|1_0_0|P|U|S|W|L|__Rn___|__________Register_List________|", 1),  // BlockTrans *
    "branch_off"    => ("|_Cond__|1_0_1|L|___________________Offset______________________|", 1),  // B,BL,BLX *
    // "co_rr"      => ("|_Cond__|1_1_0_0_0_1_0|L|__Rn___|__Rd___|__CPN__|_CPopc_|__CRm__|", 1),  // CoRR ARM9
    "co_data_trans" => ("|_Cond__|1_1_0|P|U|N|W|L|__Rn___|__CRd__|__CPN__|____Offset_____|", 1),  // CoDataTrans
    "co_data_op"    => ("|_Cond__|1_1_1_0|_CPopc_|__CRn__|__CRd__|__CPN__|_CP__|0|__CRm__|", 1),  // CoDataOp
    "co_reg_trans"  => ("|_Cond__|1_1_1_0|CPopc|L|__CRn__|__Rd___|__CPN__|_CP__|1|__CRm__|", 1),  // CoRegTrans
    "swi"           => ("|_Cond__|1_1_1_1|_____________Ignored_by_Processor______________|", 1),  // SWI *
    };

    let mut ops = HashMap::new();
    for (op, (desc, priority)) in ops_desc.iter() {
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
                        name: elems[elem_idx].replace("_", "").to_snake_case(),
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
                priority: *priority as u8,
            },
        );
    }

    for (op_name, op) in &ops {
        write!(f, "pub const OP_{}_VAL:  u32 = 0b{};\n", op_name.to_uppercase(), op.value)?;
        write!(f, "pub const OP_{}_MASK: u32 = 0b{};\n\n", op_name.to_uppercase(), op.mask)?;
        let op_name = format!("op_raw_{}", op_name).to_pascal_case();
        write!(f, "#[derive(Debug)]\n")?;
        write!(f, "pub struct {} {{\n", op_name)?;
        write!(f, "  word: u32,\n")?;
        for param in &op.params {
            write!(f, "  {}: {},\n",
                param.name,
                match param.typ() {
                    ParamType::Bool => "bool",
                    ParamType::U32 => "u32",
                    ParamType::U16 => "u16",
                    ParamType::U8 => "u8",
                }
            )?;
        }
        write!(f, "}}\n\n")?;

        write!(f, "impl {} {{\n", op_name)?;
        write!(f, "  pub fn new(v: u32) -> Self {{\n")?;
        write!(f, "    Self {{\n")?;
        let max_len = op.params.iter().max_by_key(|p| p.name.len()).unwrap().name.len();
        write!(f, "      {0:<max_len$}: v,\n", "word", max_len = max_len)?;
        for param in &op.params {
            let mask = (param.start..param.end+1).map(|i| 1 << i).fold(0, |acc, x| acc+x);
            write!(f, "      {0:<max_len$}: ((v & 0b{1:032b}) >> {2:2}) {3},\n",
                param.name,
                mask,
                param.start,
                match param.typ() {
                    ParamType::Bool => "!= 0",
                    ParamType::U32 => "as u32",
                    ParamType::U16 => "as u16",
                    ParamType::U8 => "as u8",
                },
                max_len = max_len
            )?;
        }
        write!(f, "    }}\n")?;
        write!(f, "  }}\n")?;
        write!(f, "}}\n\n")?;
    }

    write!(f, "#[derive(Debug)]\n")?;
    write!(f, "pub struct OpRawUnknown {{\n")?;
    write!(f, "  cond: u8,\n")?;
    write!(f, "  word: u32,\n")?;
    write!(f, "}}\n\n")?;

    write!(f, "impl OpRawUnknown {{\n")?;
    write!(f, "  pub fn new(v: u32) -> Self {{\n")?;
    write!(f, "    Self {{\n")?;
    write!(f, "      cond     : ((v & 0b11110000000000000000000000000000) >> 28) as u8,\n")?;
    write!(f, "      word     : ((v & 0b11111111111111111111111111111111) >>  0) as u32,\n")?;
    write!(f, "    }}\n")?;
    write!(f, "  }}\n")?;
    write!(f, "}}\n\n")?;

    write!(f, "#[derive(Debug)]\n")?;
    write!(f, "pub enum OpRaw {{\n")?;
    for (op_name, _) in &ops {
        write!(f, "  {0}(OpRaw{0}),\n", op_name.to_pascal_case())?;
    }
    write!(f, "  Unknown(OpRawUnknown),\n")?;
    write!(f, "}}\n\n")?;

    let max_len_snake = ops.iter().max_by_key(|(name, _)| name.len()).unwrap().0.len();
    let max_len_pascal = ops.iter().max_by_key(|(name, _)| name.to_pascal_case().len())
        .unwrap().0.to_pascal_case().len();
    write!(f, "impl OpRaw {{\n")?;
    write!(f, "  pub fn new(v: u32) -> Self {{\n")?;
    write!(f, "    match v {{\n")?;
    for priority in 0..2 {
        if priority != 0 {
            write!(f, "      _ => match v {{\n")?;
        }
        for (op_name, op) in &ops {
            if op.priority != priority { continue }
            let pad_snake = max_len_snake - op_name.len();
            let pad_pascal = max_len_pascal - op_name.to_pascal_case().len();
            write!(f, "      _ if (v & OP_{op_up}_MASK{0:<pad0$}) == OP_{op_up}_VAL{0:<pad0$} => \
                   OpRaw::{op}({0:>pad1$}{0:>pad1$}OpRaw{op}::new(v)),\n",
                   "",
                   op_up= op_name.to_uppercase(),
                   op=op_name.to_pascal_case(),
                   pad0=pad_snake,
                   pad1=pad_pascal)?;
        }
        if priority != 0 {
            write!(f, "      _ {0:>pad$}=> OpRaw::Unknown({0:>pad1$}OpRawUnknown::new(v)),\n",
            "",
            pad=max_len_snake*2 + max_len_pascal*2 + 5,
            pad1=(max_len_pascal - "Unknown".len()) * 2,
            )?;
            write!(f, "      }},\n")?;
        }
    }
    write!(f, "    }}\n")?;
    write!(f, "  }}\n")?;
    write!(f, "}}\n\n")?;
    // write!(f, "  pub fn to_op(&self) -> Op {{\n")?;
    // write!(f, "    match self {{\n")?;
    // for (op_name, _) in &ops {
    //     let pad_pascal = max_len_pascal - op_name.to_pascal_case().len();
    //     write!(f, "      OpRaw::{op}({0:<pad$}v) => Op{{cond: Cond::from_u8(v.cond).unwrap()}},\n",
    //            "",
    //            op=op_name.to_pascal_case(),
    //            pad=pad_pascal)?;
    // }
    // write!(f, "    }}\n")?;
    // write!(f, "  }}\n")?;
    // write!(f, "}}\n\n")?;

    // for (op_name, op) in &ops {
    //     write!(f, "#[derive(Debug)]\n")?;
    //     write!(f, "pub struct Op{} {{\n", op_name.to_pascal_case())?;
    //     for param in &op.params {
    //         write!(f, "  {}: bool,\n", param.name)?;
    //     }
    //     write!(f, "}}\n\n")?;
    // }

    // write!(f, "#[derive(Debug)]\n")?;
    // write!(f, "pub struct Op {{\n")?;
    // write!(f, "  cond: Cond,\n")?;
    // write!(f, "}}\n")?;

    Ok(())
}
