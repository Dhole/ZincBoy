use std::fmt;
use std::num::Wrapping;

use num_derive::{FromPrimitive, ToPrimitive};
use num_traits::FromPrimitive;

include!(concat!(env!("OUT_DIR"), "/op_raw.rs"));

#[derive(Debug, Eq, PartialEq, FromPrimitive, ToPrimitive)]
pub enum Cond {
    EQ = 0b0000, // Z=1 (equal)
    NE = 0b0001, // Z=0 (not equal)
    CS = 0b0010, // C=1 (unsigned higher or same)
    CC = 0b0011, // C=0 (unsigned lower)
    MI = 0b0100, // N=1 (negative)
    PL = 0b0101, // N=0 (positive or zero)
    VS = 0b0110, // V=1 (overflow)
    VC = 0b0111, // V=0 (no overflow)
    HI = 0b1000, // C=1 and Z=0 (unsigned higher)
    LS = 0b1001, // C=0 or Z=1 (unsigned lower or same)
    GE = 0b1010, // N=V (greater or equal, >=)
    LT = 0b1011, // N!=V (less than, <)
    GT = 0b1100, // Z=0 and N=V (greater than, >)
    LE = 0b1101, // Z=1 or N!=V(less or equal, <=)
    AL = 0b1110, // always
    NV = 0b1111, // reserverd
}

impl fmt::Display for Cond {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Cond::EQ => "eq",
                Cond::NE => "ne",
                Cond::CS => "cs",
                Cond::CC => "cc",
                Cond::MI => "mi",
                Cond::PL => "pl",
                Cond::VS => "vs",
                Cond::VC => "vc",
                Cond::HI => "hi",
                Cond::LS => "ls",
                Cond::GE => "ge",
                Cond::LT => "lt",
                Cond::GT => "gt",
                Cond::LE => "le",
                Cond::AL => "",
                Cond::NV => "nv",
            }
        )
    }
}

#[derive(Debug, FromPrimitive, ToPrimitive)]
pub enum AluOp {
    AND = 0b0000, // AND logical;        Rd = Rn AND Op2
    EOR = 0b0001, // XOR logical;        Rd = XOR Op2
    SUB = 0b0010, // substract;          Rd = Rn - Op2
    RSB = 0b0011, // substract reversed; Rd = Op2 - Rn
    ADD = 0b0100, // add;                Rd = Rn + Op2
    ADC = 0b0101, // add with carry;     Rd = Rn + Op2 + Cy
    SBC = 0b0110, // sub with carry;     Rd = Rn - Op2 + Cy - 1
    RSC = 0b0111, // sub cy. reversed;   Rd = Op2 - Rn + Cy - 1
    TST = 0b1000, // test;                _ = Rn AND Op2
    TEQ = 0b1001, // test exclusive;      _ = Rn XOR Op2
    CMP = 0b1010, // compare;             _ = Rn - Op2
    CMN = 0b1011, // compare neg.;        _ = Rn + Op2
    ORR = 0b1100, // OR logical;         Rd = Rn OR Op2
    MOV = 0b1101, // move;               Rd = Op2
    BIC = 0b1110, // bit clear;          Rd = Rn AND NOT Op2
    MVN = 0b1111, // not;                Rd = NOT Op2
}

impl fmt::Display for AluOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                AluOp::AND => "and",
                AluOp::EOR => "eor",
                AluOp::SUB => "sub",
                AluOp::RSB => "rsb",
                AluOp::ADD => "add",
                AluOp::ADC => "adc",
                AluOp::SBC => "sbc",
                AluOp::RSC => "rsc",
                AluOp::TST => "tst",
                AluOp::TEQ => "teq",
                AluOp::CMP => "cmp",
                AluOp::CMN => "cmn",
                AluOp::ORR => "orr",
                AluOp::MOV => "mov",
                AluOp::BIC => "bic",
                AluOp::MVN => "mvn",
            }
        )
    }
}

#[derive(Debug, FromPrimitive, ToPrimitive)]
pub enum ShiftType {
    LSL = 0,
    LSR = 1,
    ASR = 2,
    ROR = 3,
}

impl fmt::Display for ShiftType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                ShiftType::LSL => "lsl",
                ShiftType::LSR => "lsr",
                ShiftType::ASR => "asr",
                ShiftType::ROR => "ror",
            }
        )
    }
}

#[derive(Debug)]
pub enum AluOp2RegisterShift {
    Immediate(u8),
    Register(u8),
}

#[derive(Debug)]
pub struct AluOp2Register {
    shift: AluOp2RegisterShift,
    st: ShiftType,
    rm: u8,
}

#[derive(Debug)]
pub struct AluOp2Immediate {
    shift: u8,
    immediate: u8,
}

#[derive(Debug)]
pub enum AluOp2 {
    Immediate(AluOp2Immediate),
    Register(AluOp2Register),
}

// Data Processing
#[derive(Debug)]
pub struct Alu {
    op: AluOp,
    s: bool,
    rn: u8,
    rd: u8,
    op2: AluOp2,
}

#[derive(Debug)]
pub enum BranchAddr {
    Register(u8),
    Offset(i32, bool), // nn, H
}

#[derive(Debug)]
pub struct Branch {
    link: bool,
    exchange: bool,
    addr: BranchAddr,
}
impl Branch {
    pub fn offset(&self, pc: u32) -> u32 {
        match self.addr {
            BranchAddr::Register(_) => 0,
            BranchAddr::Offset(nn, h) => {
                let mut offset = Wrapping(pc) + Wrapping(8);
                if self.exchange && h {
                    offset += Wrapping(2);
                }
                if nn < 0 {
                    offset -= Wrapping(-nn as u32 * 4);
                } else {
                    offset += Wrapping(nn as u32 * 4);
                }
                offset.0
            }
        }
    }
}

#[derive(Debug)]
pub enum Half {
    Top,
    Bottom,
}

#[derive(Debug)]
pub enum MultiplyReg {
    Reg(u8),
    RegHiLo(u8, u8),
}

// #[derive(Debug)]
// pub enum MultiplyOp {
//     Reg(u8),
//     RegHalf(u8, Half),
// }

#[derive(Debug)]
pub struct Multiply {
    acc: Option<MultiplyReg>,
    set_cond: bool,
    signed: bool,
    res: MultiplyReg,
    ops_reg: (u8, u8),
}

// #[derive(Debug)]
// pub struct Breakpoint {
//     comment: (u16, u8),
// }

#[derive(Debug)]
pub struct Undefined {
    xxx: (u32, u8),
}

#[derive(Debug)]
pub struct MsrSrcImmediate {
    shift: u8,
    immediate: u8,
}

#[derive(Debug)]
pub enum MsrSrc {
    Immediate(MsrSrcImmediate),
    Register(u8),
}

#[derive(Debug)]
pub struct Msr {
    f: bool,
    s: bool,
    x: bool,
    c: bool,
    src: MsrSrc,
}

#[derive(Debug)]
pub struct Mrs {
    rd: u8,
}

#[derive(Debug)]
pub enum PsrOp {
    Mrs(Mrs),
    Msr(Msr),
}

#[derive(Debug)]
pub struct Psr {
    spsr: bool,
    op: PsrOp,
}

#[derive(Debug)]
pub enum OpBase {
    Alu(Alu),
    Branch(Branch),
    // Breakpoint(Breakpoint),
    SoftInt(u32),
    Undefined(Undefined),
    Multiply(Multiply),
    Psr(Psr),
}

#[derive(Debug)]
pub struct Op {
    cond: Cond,
    base: OpBase,
}

impl OpRaw {
    pub fn to_op(&self) -> Option<Op> {
        let op = match self {
            OpRaw::DataProcA(o) => Op {
                cond: Cond::from_u8(o.cond).unwrap(),
                base: OpBase::Alu(Alu {
                    op: AluOp::from_u8(o.op).unwrap(),
                    s: o.s,
                    rn: o.rn,
                    rd: o.rd,
                    op2: AluOp2::Register(AluOp2Register {
                        shift: AluOp2RegisterShift::Immediate(o.shift),
                        st: ShiftType::from_u8(o.typ).unwrap(),
                        rm: o.rm,
                    }),
                }),
            },
            OpRaw::DataProcB(o) => Op {
                cond: Cond::from_u8(o.cond).unwrap(),
                base: OpBase::Alu(Alu {
                    op: AluOp::from_u8(o.op).unwrap(),
                    s: o.s,
                    rn: o.rn,
                    rd: o.rd,
                    op2: AluOp2::Register(AluOp2Register {
                        shift: AluOp2RegisterShift::Register(o.rs),
                        st: ShiftType::from_u8(o.typ).unwrap(),
                        rm: o.rm,
                    }),
                }),
            },
            OpRaw::DataProcC(o) => Op {
                cond: Cond::from_u8(o.cond).unwrap(),
                base: OpBase::Alu(Alu {
                    op: AluOp::from_u8(o.op).unwrap(),
                    s: o.s,
                    rn: o.rn,
                    rd: o.rd,
                    op2: AluOp2::Immediate(AluOp2Immediate {
                        shift: o.shift,
                        immediate: o.immediate,
                    }),
                }),
            },
            OpRaw::BranchReg(o) => Op {
                cond: Cond::from_u8(o.cond).unwrap(),
                base: OpBase::Branch(Branch {
                    link: o.l,
                    exchange: true,
                    addr: BranchAddr::Register(o.rn),
                }),
            },
            OpRaw::BranchOff(o) => {
                let exchange = o.cond == 0b1111;
                let link = if exchange { true } else { o.l };
                let offset = if o.offset < 0b100000000000000000000000 {
                    o.offset as i32
                } else {
                    -((0b1000000000000000000000000 - o.offset) as i32)
                };
                Op {
                    cond: Cond::from_u8(o.cond).unwrap(),
                    base: OpBase::Branch(Branch {
                        link: link,
                        exchange: exchange,
                        addr: BranchAddr::Offset(offset, o.l),
                    }),
                }
            }
            // OpRaw::Bkpt(o) => Op {
            //     cond: Cond::from_u8(o.cond).unwrap(),
            //     base: OpBase::Breakpoint(Breakpoint {
            //         comment: (o.imm_0, o.imm_1),
            //     }),
            // },
            OpRaw::Swi(o) => {
                let cond = Cond::from_u8(o.cond).unwrap();
                if cond != Cond::AL {
                    return None;
                }
                Op {
                    cond: cond,
                    base: OpBase::SoftInt(o.ignoredby_processor),
                }
            }
            OpRaw::Undefined(o) => Op {
                cond: Cond::from_u8(o.cond).unwrap(),
                base: OpBase::Undefined(Undefined {
                    xxx: (o.xxx, o.yyy),
                }),
            },
            OpRaw::Multiply(o) => Op {
                cond: Cond::from_u8(o.cond).unwrap(),
                base: OpBase::Multiply(Multiply {
                    acc: if o.a {
                        Some(MultiplyReg::Reg(o.rn))
                    } else {
                        None
                    },
                    signed: false,
                    set_cond: o.s,
                    res: MultiplyReg::Reg(o.rd),
                    ops_reg: (o.rm, o.rs),
                }),
            },
            OpRaw::MultiplyLong(o) => Op {
                cond: Cond::from_u8(o.cond).unwrap(),
                base: OpBase::Multiply(Multiply {
                    acc: if o.a {
                        Some(MultiplyReg::RegHiLo(o.rd_hi, o.rd_lo))
                    } else {
                        None
                    },
                    signed: o.u,
                    set_cond: o.s,
                    res: MultiplyReg::RegHiLo(o.rd_hi, o.rd_lo),
                    ops_reg: (o.rm, o.rs),
                }),
            },
            OpRaw::PsrImm(o) => Op {
                cond: Cond::from_u8(o.cond).unwrap(),
                base: OpBase::Psr(Psr {
                    spsr: o.p,
                    op: PsrOp::Msr(Msr {
                        f: o.field & 0b1000 != 0,
                        s: o.field & 0b0100 != 0,
                        x: o.field & 0b0010 != 0,
                        c: o.field & 0b0001 != 0,
                        src: MsrSrc::Immediate(MsrSrcImmediate {
                            shift: o.shift,
                            immediate: o.immediate,
                        }),
                    }),
                }),
            },
            OpRaw::PsrReg(o) => Op {
                cond: Cond::from_u8(o.cond).unwrap(),
                base: OpBase::Psr(Psr {
                    spsr: o.p,
                    op: if o.l {
                        PsrOp::Msr(Msr {
                            f: o.field & 0b1000 != 0,
                            s: o.field & 0b0100 != 0,
                            x: o.field & 0b0010 != 0,
                            c: o.field & 0b0001 != 0,
                            src: MsrSrc::Register(o.rm),
                        })
                    } else {
                        PsrOp::Mrs(Mrs { rd: o.rd })
                    },
                }),
            },
            _ => return None,
        };
        Some(op)
    }
}

impl Op {
    pub fn asm(&self, pc: u32) -> String {
        let (op, args) = match &self.base {
            OpBase::Alu(alu) => {
                let op2 = match &alu.op2 {
                    AluOp2::Immediate(imm) => format!("0x{}", imm.immediate << imm.shift * 2), // TODO: ROR
                    AluOp2::Register(reg) => format!("r{}{}", reg.rm, match reg.shift {
                        AluOp2RegisterShift::Immediate(imm) => match reg.st {
                            ShiftType::LSL if imm == 0 => format!(""),
                            ShiftType::LSR if imm == 0 => format!(", lsr 32"),
                            ShiftType::ASR if imm == 0 => format!(", asr 32"),
                            ShiftType::ROR if imm == 0 => format!(", rrx"),
                            _ => format!(", {} {}", reg.st, imm),
                        },
                        AluOp2RegisterShift::Register(rs) => format!(", {} r{}", reg.st, rs),
                    }),
                };
                (format!("{}{}", alu.op, match alu.op {
                    AluOp::TST | AluOp::TEQ | AluOp::CMP | AluOp::CMN => { if alu.rd == 0b1111 { "p" } else { "" } },
                    _ => if alu.s { "s" } else { "" }
                }),
                    match alu.op {
                        AluOp::AND | AluOp::EOR | AluOp::SUB | AluOp::RSB | AluOp::ADD | AluOp::ADC |
                                     AluOp::SBC | AluOp::RSC | AluOp::ORR | AluOp::BIC =>
                            format!("r{}, r{}, {}", alu.rd, alu.rn, op2),
                        AluOp::TST | AluOp::TEQ | AluOp::CMP | AluOp::CMN => format!("r{}, {}", alu.rn, op2),
                        AluOp::MOV | AluOp::MVN => format!("r{}, {}", alu.rd, op2),
                    })
            },
            OpBase::Branch(branch) => (
                format!(
                    "b{}{}",
                    if branch.link { "l" } else { "" },
                    if branch.exchange { "x" } else { "" }
                ),
                format!(
                    "{}",
                    match branch.addr {
                        BranchAddr::Register(rn) => format!("r{}", rn),
                        BranchAddr::Offset(_, _) => format!("0x{:08x}", branch.offset(pc),),
                    }
                ),
            ),
            // OpBase::Breakpoint(bkpt) => (
            //     "bkpt".to_string(),
            //     format!("{:03x}, {:01x}", bkpt.comment.0, bkpt.comment.1),
            // ),
            OpBase::SoftInt(imm) => ("swi".to_string(), format!("0x{:08x}", imm)),
            OpBase::Undefined(und) => (
                "undefined".to_string(),
                format!("{:05x}, {:01x}", und.xxx.0, und.xxx.1),
            ),
            OpBase::Multiply(mul) => (
                format!(
                    "{0}{1}{2}{3}",
                    if let MultiplyReg::Reg(_) = mul.res {
                        ""
                    } else {
                        if mul.signed {
                            "s"
                        } else {
                            "u"
                        }
                    },
                    if let None = mul.acc { "mul" } else { "mla" },
                    if let MultiplyReg::RegHiLo(_, _) = mul.res {
                        "l"
                    } else {
                        ""
                    },
                    if mul.set_cond { "s" } else { "" },
                ),
                format!(
                    "{0}, r{1}, r{2}{3}",
                    match mul.res {
                        MultiplyReg::Reg(rd) => format!("r{}", rd),
                        MultiplyReg::RegHiLo(rd_hi, rd_lo) => format!("r{}, r{}", rd_lo, rd_hi),
                    },
                    mul.ops_reg.0,
                    mul.ops_reg.1,
                    if let Some(MultiplyReg::Reg(rs)) = mul.acc {
                        format!(", r{}", rs)
                    } else {
                        "".to_string()
                    },
                ),
            ),
            OpBase::Psr(psr) => {
                let psr_set = if psr.spsr { "spsr" } else { "cpsr" };
                (match &psr.op {
                    PsrOp::Mrs(mrs) => ("mrs".to_string(), format!("r{}, {}", mrs.rd, psr_set)),
                    PsrOp::Msr(msr) => (
                        "msr".to_string(),
                        format!(
                            "{}_{}{}{}{}, {}",
                            psr_set,
                            if msr.f { "f" } else { "" },
                            if msr.s { "s" } else { "" },
                            if msr.x { "x" } else { "" },
                            if msr.c { "c" } else { "" },
                            match &msr.src {
                                MsrSrc::Immediate(imm) => {
                                    format!("{}", imm.immediate << imm.shift * 2)
                                }
                                MsrSrc::Register(rd) => format!("r{}", rd),
                            }
                        ),
                    ),
                })
            }
            // _ => ("TODO".to_string(), "TODO".to_string()),
        };
        format!("{}{} {}", op, self.cond, args)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn op_asm() {
        let pc = 0x12345678;
        #[rustfmt::skip]
        let words_asms = vec![
            (0b1110_0001001011111111111100_0_1_0011,      "bx r3"), // BX, BLX
            (0b1110_0001001011111111111100_1_1_0011,      "blx r3"), // BX, BLX
            (0b1110_101_0_000000000100011000101000,       "b 0x12356f20"), // B,BL,BLX
            (0b1110_101_1_100000000001000000101100,       "bl 0x10349730"), // B,BL,BLX
            (0b1110_1111_101010101010101010101010,        "swi 0x00aaaaaa"), // SWI
            (0b1110_000000_0_0_0011_0100_0101_1001_0110,  "mul r3, r6, r5"), // Multiply
            (0b1110_000000_0_1_0011_0100_0101_1001_0110,  "muls r3, r6, r5"), // Multiply
            (0b1110_000000_1_0_0011_0100_0101_1001_0110,  "mla r3, r6, r5, r4"),  // Multiply
            (0b1110_000000_1_1_0011_0100_0101_1001_0110,  "mlas r3, r6, r5, r4"),  // Multiply
            (0b1110_00001_0_0_0_0011_0100_0101_1001_0110, "umull r4, r3, r6, r5"),  // MulLong
            (0b1110_00001_0_0_1_0011_0100_0101_1001_0110, "umulls r4, r3, r6, r5"),  // MulLong
            (0b1110_00001_0_1_0_0011_0100_0101_1001_0110, "umlal r4, r3, r6, r5"),  // MulLong
            (0b1110_00001_0_1_1_0011_0100_0101_1001_0110, "umlals r4, r3, r6, r5"),  // MulLong
            (0b1110_00001_1_0_0_0011_0100_0101_1001_0110, "smull r4, r3, r6, r5"),  // MulLong
            (0b1110_00001_1_0_1_0011_0100_0101_1001_0110, "smulls r4, r3, r6, r5"),  // MulLong
            (0b1110_00001_1_1_0_0011_0100_0101_1001_0110, "smlal r4, r3, r6, r5"),  // MulLong
            (0b1110_00001_1_1_1_0011_0100_0101_1001_0110, "smlals r4, r3, r6, r5"),  // MulLong
            (0b1110_00010_0_0_0_1111_0011_00000000_0100,  "mrs r3, cpsr"),  // PSR Reg
            (0b1110_00010_1_0_0_1111_0011_00000000_0100,  "mrs r3, spsr"),  // PSR Reg
            (0b1110_00010_0_1_0_1010_1111_00000000_0011,  "msr cpsr_fx, r3"),  // PSR Reg
            (0b1110_00010_1_1_0_0101_1111_00000000_0100,  "msr spsr_sc, r4"),  // PSR Reg
            (0b1110_000_0000_0_0011_0100_00000_00_0_0101,  "and r4, r3, r5"), // DataProc A
            (0b1110_000_0001_1_0011_0100_00000_01_0_0101,  "eors r4, r3, r5, lsr 32"), // DataProc A
            (0b1110_000_0010_0_0011_0100_00000_10_0_0101,  "sub r4, r3, r5, asr 32"), // DataProc A
            (0b1110_000_0011_1_0011_0100_00000_11_0_0101,  "rsbs r4, r3, r5, rrx"), // DataProc A
            (0b1110_000_0100_0_0011_0100_00001_00_0_0101,  "add r4, r3, r5, lsl 1"), // DataProc A
            (0b1110_000_0101_1_0011_0100_00010_01_0_0101,  "adcs r4, r3, r5, lsr 2"), // DataProc A
            (0b1110_000_0110_0_0011_0100_00011_10_0_0101,  "sbc r4, r3, r5, asr 3"), // DataProc A
            (0b1110_000_0111_0_0011_0100_10100_11_0_0101,  "rsc r4, r3, r5, ror 20"), // DataProc A
            (0b1110_000_1000_1_0011_0000_00101_00_0_0101,  "tst r3, r5, lsl 5"), // DataProc A
            (0b1110_000_1001_1_0011_1111_00110_01_0_0101,  "teqp r3, r5, lsr 6"), // DataProc A
            (0b1110_000_1010_1_0011_0000_10111_10_0_0101,  "cmp r3, r5, asr 23"), // DataProc A
            (0b1110_000_1011_1_0011_1111_01000_11_0_0101,  "cmnp r3, r5, ror 8"), // DataProc A
            (0b1110_000_1100_0_0011_0100_01001_00_0_0101,  "orr r4, r3, r5, lsl 9"), // DataProc A
            //(0b1110_000_1101_1_0000_0100_11010_01_0_0101,  "lsrs r4, r5, 0x1a"), // DataProc A
            (0b1110_000_1110_0_0011_0100_01101_10_0_0101,  "bic r4, r3, r5, asr 13"), // DataProc A
            (0b1110_000_1111_1_0000_0100_11101_11_0_0101,  "mvns r4, r5, ror 29"), // DataProc A
            // (0b1110_000|___Op__|S|__Rn___|__Rd___|__Rs____0_Typ_1___Rm___|,     ""), // DataProc B
            // (0b1110_001|___Op__|S|__Rn___|__Rd___|_Shift_|___Immediate___|,     ""), // DataProc C
        ];
        println!("# Radare disasm");
        for (word, _) in &words_asms {
            println!(
                "rasm2 -a arm -b 32 -o 0x{:08x} -D {:08x}",
                pc,
                (*word as u32).to_be()
            );
        }
        for (word, asm_good) in &words_asms {
            let op = OpRaw::new(*word).unwrap();
            let asm = op.to_op().map_or("???".to_string(), |o| o.asm(pc));
            println!(
                "{:08x}: {:08x} {} | {:?} - {:?}",
                pc,
                (*word as u32).to_be(),
                asm,
                op,
                op.to_op()
            );
            assert_eq!(*asm_good, asm);
        }
    }
}
