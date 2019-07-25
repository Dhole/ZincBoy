use super::op_raw_arm;
use super::op_raw_thumb;

use std::fmt;
use std::num::Wrapping;

use num_derive::{FromPrimitive, ToPrimitive};
// use num_traits::FromPrimitive;

// include!(concat!(env!("OUT_DIR"), "/op_raw.rs"));
// include!(concat!(env!("OUT_DIR"), "/op_raw_thumb.rs"));

#[derive(Debug, Clone, Copy, Eq, PartialEq, FromPrimitive, ToPrimitive)]
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

impl Cond {
    fn as_str<'a>(&self) -> &'a str {
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
    }
}

impl fmt::Display for Cond {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

#[derive(Debug, Clone)]
pub struct StatusRegFields {
    pub f: bool,
    pub s: bool,
    pub x: bool,
    pub c: bool,
}

#[derive(Debug, Clone)]
pub enum StatusReg {
    Spsr,
    Cpsr,
}

#[derive(Debug, Clone)]
pub enum Arg {
    StatusReg(StatusReg, Option<StatusRegFields>),
    Reg(u8),
    Val(u32),
    Offset(u32),
    Shift(Box<Arg>, ShiftType, Box<Arg>),
    Negative(Box<Arg>),
    WriteBack(Box<Arg>),
    Address(Args),
    RegList([bool; 16], bool), // bool: psr_force_user_bit
}

impl fmt::Display for Arg {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Arg::Negative(arg) => write!(f, "-{}", arg),
            Arg::Reg(reg) => write!(f, "r{}", reg),
            Arg::StatusReg(sr, opt_srf) => {
                match sr {
                    StatusReg::Spsr => write!(f, "spsr")?,
                    StatusReg::Cpsr => write!(f, "cpsr")?,
                }
                if let Some(fields) = opt_srf {
                    write!(
                        f,
                        "_{}{}{}{}",
                        if fields.f { "f" } else { "" },
                        if fields.s { "s" } else { "" },
                        if fields.x { "x" } else { "" },
                        if fields.c { "c" } else { "" },
                    )?;
                }
                Ok(())
            }
            Arg::Val(val) => {
                if *val <= 64 {
                    write!(f, "{}", val)
                } else {
                    write!(f, "0x{:x}", val)
                }
            }
            Arg::Offset(off) => write!(f, "0x{:08x}", off),
            Arg::Shift(arg0, st, arg) => {
                write!(f, "{}", arg0)?;
                match **arg {
                    Arg::Val(0) => match st {
                        ShiftType::LSL => Ok(()),
                        ShiftType::LSR => write!(f, ", lsr 32",),
                        ShiftType::ASR => write!(f, ", asr 32",),
                        ShiftType::ROR => write!(f, ", rrx",),
                    },
                    _ => write!(f, ", {} {}", st.as_str(), arg),
                }
            }
            Arg::Address(args) => write!(f, "[{}]", args),
            Arg::WriteBack(arg) => write!(f, "{}!", arg),
            Arg::RegList(reg_bitmap, s) => {
                let mut regs = Args::new(&[]);
                for i in 0..16 {
                    if reg_bitmap[i] {
                        regs.push(Arg::Reg(i as u8))
                    }
                }
                write!(f, "{{{}}}", regs)?;
                if *s {
                    write!(f, " ^")?;
                }
                Ok(())
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct Args {
    v: Vec<Arg>,
}

impl Args {
    pub fn new(args_slice: &[Arg]) -> Self {
        let mut args = Self { v: Vec::new() };
        args.extend(args_slice);
        args
    }
    pub fn push(&mut self, arg: Arg) {
        self.v.push(arg);
    }
    pub fn extend(&mut self, args_slice: &[Arg]) {
        self.v.extend_from_slice(args_slice);
    }
}

impl fmt::Display for Args {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (i, arg) in self.v.iter().enumerate() {
            let arg_string = format!("{}", arg);
            if i != 0 && arg_string.len() != 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", arg_string)?;
        }
        Ok(())
    }
}

#[derive(Debug)]
pub struct Assembly<'a> {
    cond: Cond,
    pre: &'a str,
    mnemonic: &'a str,
    mode: Vec<&'a str>,
    args: Args,
}

impl<'a> Assembly<'a> {
    pub fn new(pre: &'a str, mnemonic: &'a str, mode: Vec<&'a str>, args: Args) -> Self {
        Assembly {
            cond: Cond::AL,
            pre,
            mnemonic,
            mode,
            args,
        }
    }
}

impl<'a> fmt::Display for Assembly<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}{}", self.pre, self.mnemonic)?;
        self.mode.iter().try_for_each(|m| write!(f, "{}", m))?;
        write!(f, "{}", self.cond.as_str())?;
        if self.args.v.len() > 0 {
            write!(f, " {}", self.args)?;
        }
        Ok(())
    }
}

#[derive(Debug)]
pub enum OpBase {
    Alu(Alu),
    Branch(Branch),
    // Breakpoint(Breakpoint),
    SoftInt(SoftInt),
    Multiply(Multiply),
    Psr(Psr),
    Memory(Memory),
    MemoryBlock(MemoryBlock),
    Swap(Swap),
    CoOp(CoOp),
    Undefined(Undefined),
    Unknown(Unknown),
    Invalid(Invalid),
}

#[derive(Debug)]
pub struct Op {
    pub cond: Cond,
    pub base: OpBase,
}

#[derive(Debug, Clone, Copy, FromPrimitive, ToPrimitive)]
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

impl AluOp {
    fn as_str<'a>(&self) -> &'a str {
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
    }
}

impl fmt::Display for AluOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

#[derive(Debug, Clone, Copy, FromPrimitive, ToPrimitive)]
pub enum ShiftType {
    LSL = 0,
    LSR = 1,
    ASR = 2,
    ROR = 3,
}

impl ShiftType {
    fn as_str<'a>(&self) -> &'a str {
        match self {
            ShiftType::LSL => "lsl",
            ShiftType::LSR => "lsr",
            ShiftType::ASR => "asr",
            ShiftType::ROR => "ror",
        }
    }
}

impl fmt::Display for ShiftType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

#[derive(Debug)]
pub enum AluOp2RegisterShift {
    Immediate(u8),
    Register(u8),
}

#[derive(Debug)]
pub struct AluOp2Register {
    pub shift: AluOp2RegisterShift,
    pub st: ShiftType,
    pub rm: u8,
}

#[derive(Debug)]
pub struct AluOp2Immediate {
    pub shift: u8,
    pub immediate: u8,
}

#[derive(Debug)]
pub enum AluOp2 {
    Immediate(AluOp2Immediate),
    Register(AluOp2Register),
}

// Data Processing
#[derive(Debug)]
pub struct Alu {
    pub op: AluOp,
    pub s: bool,
    pub rn: u8,
    pub rd: u8,
    pub op2: AluOp2,
    pub thumb: bool, // Wether the Op must be displayed as a thumb op (with special/reduced form)
}

impl Alu {
    pub fn asm(&self, _pc: u32) -> Assembly {
        // Thumb move shifted register
        if self.thumb {
            let mut mode = Vec::new();
            if self.s {
                mode.push("s");
            }
            let mut args = Args::new(&[Arg::Reg(self.rd)]);
            match (&self.op, &self.op2) {
                (
                    AluOp::MOV,
                    AluOp2::Register(AluOp2Register {
                        shift: AluOp2RegisterShift::Immediate(shift),
                        st,
                        rm,
                    }),
                ) => {
                    args.push(Arg::Reg(*rm));
                    let mnemonic = match st {
                        ShiftType::LSL if *shift == 0 => "mov",
                        ShiftType::LSL => "lsl",
                        ShiftType::LSR => "lsr",
                        ShiftType::ASR => "asr",
                        ShiftType::ROR => "ror",
                    };
                    match (st, shift) {
                        (ShiftType::LSL, 0) => (),
                        (_, 0) => args.push(Arg::Val(32)),
                        (_, _) => args.push(Arg::Val(*shift as u32)),
                    }
                    return Assembly::new("", mnemonic, mode, args);
                }
                _ => {
                    let mnemonic = self.op.as_str();
                    match &self.op2 {
                        AluOp2::Immediate(imm) => args.push(Arg::Val(imm.immediate as u32)),
                        AluOp2::Register(reg) => args.push(Arg::Reg(reg.rm)),
                    }
                    return Assembly::new("", mnemonic, mode, args);
                }
            }
        }
        let mnemonic = self.op.as_str();
        let mut mode = Vec::new();
        match &self.op {
            AluOp::TST | AluOp::TEQ | AluOp::CMP | AluOp::CMN => {
                if self.rd == 0b1111 {
                    mode.push("p");
                }
            }
            _ if self.s => mode.push("s"),
            _ => (),
        };
        let mut args = match self.op {
            AluOp::AND
            | AluOp::EOR
            | AluOp::SUB
            | AluOp::RSB
            | AluOp::ADD
            | AluOp::ADC
            | AluOp::SBC
            | AluOp::RSC
            | AluOp::ORR
            | AluOp::BIC => Args::new(&[Arg::Reg(self.rd), Arg::Reg(self.rn)]),
            AluOp::TST | AluOp::TEQ | AluOp::CMP | AluOp::CMN => Args::new(&[Arg::Reg(self.rn)]),
            AluOp::MOV | AluOp::MVN => Args::new(&[Arg::Reg(self.rd)]),
        };
        match &self.op2 {
            AluOp2::Immediate(imm) => args.push(Arg::Val(
                (imm.immediate as u32).rotate_right((imm.shift * 2).into()),
            )),
            AluOp2::Register(reg) => {
                args.push(Arg::Shift(
                    Box::new(Arg::Reg(reg.rm)),
                    reg.st,
                    match &reg.shift {
                        AluOp2RegisterShift::Immediate(imm) => Box::new(Arg::Val(*imm as u32)),
                        AluOp2RegisterShift::Register(rs) => Box::new(Arg::Reg(*rs)),
                    },
                ));
            }
        }
        Assembly::new("", mnemonic, mode, args)
    }
    pub fn validate(self, inst_bin: u32) -> OpBase {
        match self.op {
            AluOp::MOV | AluOp::MVN if self.rn != 0b0000 => OpBase::Invalid(Invalid::new(inst_bin)),
            AluOp::CMP | AluOp::CMN | AluOp::TST | AluOp::TEQ
                if self.rd != 0b0000 && self.rd != 0b1111 =>
            {
                OpBase::Invalid(Invalid::new(inst_bin))
            }
            _ => OpBase::Alu(self),
        }
    }
}

#[derive(Debug)]
pub enum BranchAddr {
    Register(u8),
    Offset(i32, bool), // nn, H
}

#[derive(Debug)]
pub struct Branch {
    pub link: bool,
    pub exchange: bool,
    pub addr: BranchAddr,
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
    pub fn asm(&self, pc: u32) -> Assembly {
        let mut mode = Vec::new();
        if self.link {
            mode.push("l");
        }
        if self.exchange {
            mode.push("x");
        }
        let args = Args::new(&[match self.addr {
            BranchAddr::Register(rn) => Arg::Reg(rn),
            BranchAddr::Offset(_, _) => Arg::Offset(self.offset(pc)),
        }]);
        Assembly::new("", "b", mode, args)
    }
    pub fn validate(self, _inst_bin: u32) -> OpBase {
        OpBase::Branch(self)
    }
    // TODO: According to the spec, Results is undefined behaviour if rn = r15.  Figure out what to
    // do.
}

#[derive(Debug)]
pub struct SoftInt {
    pub imm: u32,
}

impl SoftInt {
    pub fn asm(&self, _pc: u32) -> Assembly {
        Assembly::new("", "swi", vec![], Args::new(&[Arg::Val(self.imm)]))
    }
    pub fn validate(self, _inst_bin: u32) -> OpBase {
        OpBase::SoftInt(self)
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
    pub acc: Option<MultiplyReg>,
    pub set_cond: bool,
    pub signed: bool,
    pub res: MultiplyReg,
    pub ops_reg: (u8, u8),
}

impl Multiply {
    pub fn asm(&self, _pc: u32) -> Assembly {
        let pre = match (&self.res, &self.signed) {
            (MultiplyReg::Reg(_), _) => "",
            (_, true) => "s",
            (_, false) => "u",
        };
        let mnemonic = if let None = self.acc { "mul" } else { "mla" };
        let mut mode = Vec::new();
        if let MultiplyReg::RegHiLo(_, _) = self.res {
            mode.push("l");
        }
        if self.set_cond {
            mode.push("s")
        }
        let mut args = match self.res {
            MultiplyReg::Reg(rd) => Args::new(&[Arg::Reg(rd)]),
            MultiplyReg::RegHiLo(rd_hi, rd_lo) => Args::new(&[Arg::Reg(rd_lo), Arg::Reg(rd_hi)]),
        };
        args.extend(&[Arg::Reg(self.ops_reg.0), Arg::Reg(self.ops_reg.1)]);
        if let Some(MultiplyReg::Reg(rs)) = self.acc {
            args.push(Arg::Reg(rs));
        }
        Assembly::new(pre, mnemonic, mode, args)
    }
    pub fn validate(self, _inst_bin: u32) -> OpBase {
        OpBase::Multiply(self)
    }
}

// #[derive(Debug)]
// pub struct Breakpoint {
//     comment: (u16, u8),
// }

#[derive(Debug)]
pub struct Undefined {
    pub xxx: (u32, u8),
}

impl Undefined {
    pub fn asm(&self, _pc: u32) -> Assembly {
        Assembly::new(
            "",
            "undefined",
            Vec::new(),
            Args::new(&[Arg::Val(self.xxx.0), Arg::Val(self.xxx.1 as u32)]),
        )
    }
}

#[derive(Debug)]
pub struct MsrSrcImmediate {
    pub shift: u8,
    pub immediate: u32,
}

#[derive(Debug)]
pub enum MsrSrc {
    Immediate(MsrSrcImmediate),
    Register(u8),
}

#[derive(Debug)]
pub struct Msr {
    pub f: bool,
    pub s: bool,
    pub x: bool,
    pub c: bool,
    pub src: MsrSrc,
}

#[derive(Debug)]
pub struct Mrs {
    pub rd: u8,
}

#[derive(Debug)]
pub enum PsrOp {
    Mrs(Mrs),
    Msr(Msr),
}

#[derive(Debug)]
pub struct Psr {
    pub spsr: bool,
    pub op: PsrOp,
}

impl Psr {
    pub fn asm(&self, _pc: u32) -> Assembly {
        let status_reg = if self.spsr {
            StatusReg::Spsr
        } else {
            StatusReg::Cpsr
        };
        let mnemonic = match &self.op {
            PsrOp::Mrs(_) => "mrs",
            PsrOp::Msr(_) => "msr",
        };
        let args = match &self.op {
            PsrOp::Mrs(mrs) => Args::new(&[Arg::Reg(mrs.rd), Arg::StatusReg(status_reg, None)]),
            PsrOp::Msr(msr) => {
                let fields = StatusRegFields {
                    f: msr.f,
                    s: msr.s,
                    x: msr.x,
                    c: msr.c,
                };
                Args::new(&[
                    Arg::StatusReg(status_reg, Some(fields)),
                    match &msr.src {
                        MsrSrc::Immediate(imm) => {
                            Arg::Val(imm.immediate.rotate_right((imm.shift * 2) as u32))
                        }
                        MsrSrc::Register(rd) => Arg::Reg(*rd),
                    },
                ])
            }
        };
        Assembly::new("", mnemonic, vec![], args)
    }
    pub fn validate(self, inst_bin: u32) -> OpBase {
        match &self.op {
            PsrOp::Msr(msr) => {
                if !msr.f && !msr.s && !msr.x && !msr.c {
                    // TODO: Figure out if this configuration is invalid or just a NOP
                    OpBase::Invalid(Invalid::new(inst_bin))
                } else {
                    OpBase::Psr(self)
                }
            }
            _ => OpBase::Psr(self),
        }
    }
}

#[derive(Debug)]
pub enum MemoryOp {
    Store,
    Load,
}

#[derive(Debug)]
pub struct MemoryAddrReg {
    pub rm: u8,
    pub st: ShiftType,
    pub shift: u8,
}

#[derive(Debug)]
pub enum MemoryAddr {
    Immediate(u16),
    Register(MemoryAddrReg),
}

#[derive(Debug)]
pub enum MemoryPrePost {
    Post(bool), // Add offset after transfer (T: force non-privileged access).  Write-back enabled.
    Pre(bool),  // Add offset after transfer (W: write address into base)
}

#[derive(Debug)]
pub enum MemorySize {
    Byte,
    Half,
    Word,
}

// Load, Store
#[derive(Debug)]
pub struct Memory {
    pub op: MemoryOp,
    pub addr: MemoryAddr,
    pub rn: u8,
    pub rd: u8,
    pub pre_post: MemoryPrePost,
    pub add_offset: bool,
    pub size: MemorySize,
    pub signed: bool,
}

impl Memory {
    pub fn asm(&self, _pc: u32) -> Assembly {
        let mnemonic = match self.op {
            MemoryOp::Load => "ldr",
            MemoryOp::Store => "str",
        };
        let mut mode = Vec::new();
        if self.signed {
            mode.push("s");
        }
        match self.size {
            MemorySize::Byte => mode.push("b"),
            MemorySize::Half => mode.push("h"),
            _ => (),
        }
        if let MemoryPrePost::Post(true) = self.pre_post {
            mode.push("t");
        }
        let mut offset = match &self.addr {
            MemoryAddr::Immediate(imm) => Arg::Val(*imm as u32),
            MemoryAddr::Register(reg) => Arg::Shift(
                Box::new(Arg::Reg(reg.rm)),
                reg.st,
                Box::new(Arg::Val(reg.shift as u32)),
            ),
        };
        if !self.add_offset {
            offset = Arg::Negative(Box::new(offset));
        }
        let mut args = Args::new(&[Arg::Reg(self.rd)]);
        match self.pre_post {
            MemoryPrePost::Post(_) => {
                args.extend(&[Arg::Address(Args::new(&[Arg::Reg(self.rn)])), offset])
            }
            MemoryPrePost::Pre(w) => {
                let mut addr = Arg::Address(Args::new(&[Arg::Reg(self.rn), offset]));
                if w {
                    addr = Arg::WriteBack(Box::new(addr));
                }
                args.extend(&[addr])
            }
        }
        Assembly::new("", mnemonic, mode, args)
    }
    pub fn validate(self, inst_bin: u32) -> OpBase {
        if self.rn == self.rd {
            return OpBase::Invalid(Invalid { inst_bin });
        }
        if let MemoryAddr::Register(reg) = &self.addr {
            if self.rn == reg.rm {
                return OpBase::Invalid(Invalid { inst_bin });
            }
        }
        OpBase::Memory(self)
    }
}

// Load, Store Memory
#[derive(Debug)]
pub struct MemoryBlock {
    pub pre: bool,
    pub add_offset: bool,
    pub psr_force_user_bit: bool,
    pub write_back: bool,
    pub op: MemoryOp,
    pub rn: u8,
    pub reg_list: [bool; 16],
}

impl MemoryBlock {
    pub fn asm(&self, _pc: u32) -> Assembly {
        let mnemonic = match self.op {
            MemoryOp::Load => "ldm",
            MemoryOp::Store => "stm",
        };
        let mode = vec![match (self.pre, self.add_offset) {
            (false, false) => "da",
            (false, true) => "",
            (true, false) => "db",
            (true, true) => "ib",
        }];
        let mut arg0 = Arg::Reg(self.rn);
        if self.write_back {
            arg0 = Arg::WriteBack(Box::new(arg0));
        }
        let args = Args::new(&[arg0, Arg::RegList(self.reg_list, self.psr_force_user_bit)]);
        Assembly::new("", mnemonic, mode, args)
    }
    pub fn validate(self, inst_bin: u32) -> OpBase {
        if self.rn == 15 {
            OpBase::Invalid(Invalid { inst_bin })
        } else {
            OpBase::MemoryBlock(self)
        }
    }
}

#[derive(Debug)]
pub struct Swap {
    pub rn: u8,
    pub rd: u8,
    pub rm: u8,
    pub byte: bool,
}

impl Swap {
    pub fn asm(&self, _pc: u32) -> Assembly {
        let args = Args::new(&[
            Arg::Reg(self.rd),
            Arg::Reg(self.rm),
            Arg::Address(Args::new(&[Arg::Reg(self.rn)])),
        ]);
        Assembly::new("", "swp", if self.byte { vec!["b"] } else { vec![] }, args)
    }
    pub fn validate(self, inst_bin: u32) -> OpBase {
        if self.rn == 15 || self.rd == 15 || self.rm == 15 {
            OpBase::Invalid(Invalid { inst_bin })
        } else {
            OpBase::Swap(self)
        }
    }
}

#[derive(Debug)]
pub enum CoOp {
    Todo(u32),
}

impl CoOp {
    pub fn asm(&self, _pc: u32) -> Assembly {
        Assembly::new("", "CoOp(TODO)", vec![], Args::new(&[]))
    }
    pub fn validate(self, _inst_bin: u32) -> OpBase {
        OpBase::CoOp(self)
    }
}

#[derive(Debug)]
pub enum InstructionBin {
    ARM(u32),
    Thumb(u16),
}

#[derive(Debug)]
pub struct Unknown {
    pub inst: InstructionBin,
}

impl Unknown {
    pub fn asm(&self, _pc: u32) -> Assembly {
        Assembly::new("", "Unknown(TODO)", vec![], Args::new(&[]))
    }
}

#[derive(Debug)]
pub struct Invalid {
    pub inst_bin: u32,
}

impl Invalid {
    pub fn new(inst_bin: u32) -> Self {
        Invalid { inst_bin }
    }
    pub fn asm(&self, _pc: u32) -> Assembly {
        Assembly::new("", "invalid", vec![], Args::new(&[]))
    }
}

impl Op {
    pub fn decode_arm(inst_bin: u32) -> Op {
        let op_raw = op_raw_arm::OpRaw::new(inst_bin);
        op_raw.to_op()
    }
    pub fn decode_thumb(inst_bin: u16) -> Op {
        Op {
            cond: Cond::AL,
            base: OpBase::Undefined(Undefined { xxx: (0, 0) }),
        }
    }
    pub fn asm(&self, pc: u32) -> Assembly {
        let mut asm = match &self.base {
            OpBase::Alu(op) => op.asm(pc),
            OpBase::Branch(op) => op.asm(pc),
            OpBase::SoftInt(op) => op.asm(pc),
            OpBase::Multiply(op) => op.asm(pc),
            OpBase::Psr(op) => op.asm(pc),
            OpBase::Memory(op) => op.asm(pc),
            OpBase::Swap(op) => op.asm(pc),
            OpBase::MemoryBlock(op) => op.asm(pc),
            OpBase::CoOp(op) => op.asm(pc),
            OpBase::Undefined(op) => op.asm(pc),
            OpBase::Unknown(op) => op.asm(pc),
            OpBase::Invalid(op) => op.asm(pc),
        };
        asm.cond = self.cond;
        asm
    }
}

#[cfg(test)]
mod tests {
    use super::op_raw_arm;
    use super::op_raw_thumb;

    #[test]
    fn op_arm_asm() {
        let pc = 0x12345678;
        #[rustfmt::skip]
        let insts_bin_asm = vec![
            // Cond
            (0b0000_0001001011111111111100_0_1_0011,      "bxeq r3 ", "BX, BLX"),
            (0b0001_0001001011111111111100_0_1_0011,      "bxne r3 ", "BX, BLX"),
            (0b0010_0001001011111111111100_0_1_0011,      "bxcs r3 ", "BX, BLX"),
            (0b0011_0001001011111111111100_0_1_0011,      "bxcc r3 ", "BX, BLX"),
            (0b0100_0001001011111111111100_0_1_0011,      "bxmi r3 ", "BX, BLX"),
            (0b0101_0001001011111111111100_0_1_0011,      "bxpl r3 ", "BX, BLX"),
            (0b0110_0001001011111111111100_0_1_0011,      "bxvs r3 ", "BX, BLX"),
            (0b0111_0001001011111111111100_0_1_0011,      "bxvc r3 ", "BX, BLX"),
            (0b1000_0001001011111111111100_0_1_0011,      "bxhi r3 ", "BX, BLX"),
            (0b1001_0001001011111111111100_0_1_0011,      "bxls r3 ", "BX, BLX"),
            (0b1010_0001001011111111111100_0_1_0011,      "bxge r3 ", "BX, BLX"),
            (0b1011_0001001011111111111100_0_1_0011,      "bxlt r3 ", "BX, BLX"),
            (0b1100_0001001011111111111100_0_1_0011,      "bxgt r3 ", "BX, BLX"),
            (0b1101_0001001011111111111100_0_1_0011,      "bxle r3 ", "BX, BLX"),
            (0b1110_0001001011111111111100_0_1_0011,      "bx r3 ", "BX, BLX"),
            //                             L   Rn
            (0b1110_0001001011111111111100_0_1_0011,      "bx r3 ", "BX, BLX"),
            (0b1110_0001001011111111111100_1_1_0011,      "blx r3", "BX, BLX"),
            //          L Offset
            (0b1110_101_0_000000000100011000101000,       "b 0x12356f20 ", "B,BL,BLX"),
            (0b1110_101_1_100000000001000000101100,       "bl 0x10349730", "B,BL,BLX"),
            //           Ignored
            (0b1110_1111_101010101010101010101010,        "swi 0xaaaaaa", "SWI"),
            //             A S Rd   Rn   Rs        Rm
            (0b1110_000000_0_0_0011_0100_0101_1001_0110,  "mul r3, r6, r5     ", "Multiply"),
            (0b1110_000000_0_1_0011_0100_0101_1001_0110,  "muls r3, r6, r5    ", "Multiply"),
            (0b1110_000000_1_0_0011_0100_0101_1001_0110,  "mla r3, r6, r5, r4 ", "Multiply"),
            (0b1110_000000_1_1_0011_0100_0101_1001_0110,  "mlas r3, r6, r5, r4", "Multiply"),
            //            U A S RdHi RdLo Rs        Rm
            (0b1110_00001_0_0_0_0011_0100_0101_1001_0110, "umull r4, r3, r6, r5 ", "MulLong"),
            (0b1110_00001_0_0_1_0011_0100_0101_1001_0110, "umulls r4, r3, r6, r5", "MulLong"),
            (0b1110_00001_0_1_0_0011_0100_0101_1001_0110, "umlal r4, r3, r6, r5 ", "MulLong"),
            (0b1110_00001_0_1_1_0011_0100_0101_1001_0110, "umlals r4, r3, r6, r5", "MulLong"),
            (0b1110_00001_1_0_0_0011_0100_0101_1001_0110, "smull r4, r3, r6, r5 ", "MulLong"),
            (0b1110_00001_1_0_1_0011_0100_0101_1001_0110, "smulls r4, r3, r6, r5", "MulLong"),
            (0b1110_00001_1_1_0_0011_0100_0101_1001_0110, "smlal r4, r3, r6, r5 ", "MulLong"),
            (0b1110_00001_1_1_1_0011_0100_0101_1001_0110, "smlals r4, r3, r6, r5", "MulLong"),
            //            P L   Fiel Rd            Rm
            (0b1110_00010_0_0_0_1111_0011_00000000_0100,  "mrs r3, cpsr   ", "PSR Reg"),
            (0b1110_00010_1_0_0_1111_0011_00000000_0100,  "mrs r3, spsr   ", "PSR Reg"),
            (0b1110_00010_0_1_0_1010_1111_00000000_0011,  "msr cpsr_fx, r3", "PSR Reg"),
            (0b1110_00010_1_1_0_0101_1111_00000000_0100,  "msr spsr_sc, r4", "PSR Reg"),
            (0b1110_00010_1_0_0_0111_0011_00000000_0100,  "invalid        ", "PSR Reg"),
            (0b1110_00010_0_1_0_0000_1111_00000000_0011,  "invalid        ", "PSR Reg"),
            //            P    Fiel      Shif Imm
            (0b1110_00110_0_10_0001_1111_0000_00000000,  "msr cpsr_c, 0            ", "PSR Imm"),
            (0b1110_00110_0_10_0010_1111_0001_00000001,  "msr cpsr_x, 0x40000000   ", "PSR Imm"),
            (0b1110_00110_0_10_1111_1111_0001_01000001,  "msr cpsr_fsxc, 0x40000010", "PSR Imm"),
            (0b1110_00110_1_10_0100_1111_0011_00000010,  "msr spsr_s, 0x8000000    ", "PSR Imm"),
            (0b1110_00110_1_10_1000_1111_0010_00000110,  "msr spsr_f, 0x60000000   ", "PSR Imm"),
            (0b1110_00110_1_10_0110_1111_0101_01010010,  "msr spsr_sx, 0x14800000  ", "PSR Imm"),
            (0b1110_00110_1_10_0101_1111_1010_11000010,  "msr spsr_sc, 0xc2000     ", "PSR Imm"),
            (0b1110_00110_0_10_0000_1111_0001_00000001,  "invalid                  ", "PSR Imm"),
            (0b1110_00110_1_10_0000_1111_0011_00000010,  "invalid                  ", "PSR Imm"),
            //          Op   S Rn   Rd   Shift St   Rm
            (0b1110_000_0000_0_0011_0100_00000_00_0_0101,  "and r4, r3, r5         ", "DataProc A"),
            (0b1110_000_0001_1_0011_0100_00000_01_0_0101,  "eors r4, r3, r5, lsr 32", "DataProc A"),
            (0b1110_000_0010_0_0011_0100_00000_10_0_0101,  "sub r4, r3, r5, asr 32 ", "DataProc A"),
            (0b1110_000_0011_1_0011_0100_00000_11_0_0101,  "rsbs r4, r3, r5, rrx   ", "DataProc A"),
            (0b1110_000_0100_0_0011_0100_00001_00_0_0101,  "add r4, r3, r5, lsl 1  ", "DataProc A"),
            (0b1110_000_0101_1_0011_0100_00010_01_0_0101,  "adcs r4, r3, r5, lsr 2 ", "DataProc A"),
            (0b1110_000_0110_0_0011_0100_00011_10_0_0101,  "sbc r4, r3, r5, asr 3  ", "DataProc A"),
            (0b1110_000_0111_0_0011_0100_10100_11_0_0101,  "rsc r4, r3, r5, ror 20 ", "DataProc A"),
            (0b1110_000_1000_1_0011_0000_00101_00_0_0101,  "tst r3, r5, lsl 5      ", "DataProc A"),
            (0b1110_000_1000_1_0011_0001_00101_00_0_0101,  "invalid                ", "DataProc A"),
            (0b1110_000_1001_1_0011_1111_00110_01_0_0101,  "teqp r3, r5, lsr 6     ", "DataProc A"),
            (0b1110_000_1001_1_0011_0011_00110_01_0_0101,  "invalid                ", "DataProc A"),
            (0b1110_000_1010_1_0011_0000_10111_10_0_0101,  "cmp r3, r5, asr 23     ", "DataProc A"),
            (0b1110_000_1010_1_0011_0001_10111_10_0_0101,  "invalid                ", "DataProc A"),
            (0b1110_000_1011_1_0011_1111_01000_11_0_0101,  "cmnp r3, r5, ror 8     ", "DataProc A"),
            (0b1110_000_1011_1_0011_0001_01000_11_0_0101,  "invalid                ", "DataProc A"),
            (0b1110_000_1100_0_0011_0100_01001_00_0_0101,  "orr r4, r3, r5, lsl 9  ", "DataProc A"),
            (0b1110_000_1101_1_0000_0100_11010_01_0_0101,  "movs r4, r5, lsr 26    ", "DataProc A"),
            (0b1110_000_1101_1_0001_0100_11010_01_0_0101,  "invalid                ", "DataProc A"),
            (0b1110_000_1110_0_0011_0100_01101_10_0_0101,  "bic r4, r3, r5, asr 13 ", "DataProc A"),
            (0b1110_000_1111_1_0000_0100_11101_11_0_0101,  "mvns r4, r5, ror 29    ", "DataProc A"),
            (0b1110_000_1111_1_0001_0100_11101_11_0_0101,  "invalid                ", "DataProc A"),
            //          Op   S Rn   Rd   Rs     St   Rm
            (0b1110_000_0000_0_0011_0100_0000_0_00_1_0101,  "and r4, r3, r5, lsl r0 ", "DataProc B"),
            (0b1110_000_0001_1_0011_0100_0000_0_01_1_0101,  "eors r4, r3, r5, lsr r0", "DataProc B"),
            (0b1110_000_0010_0_0011_0100_0000_0_10_1_0101,  "sub r4, r3, r5, asr r0 ", "DataProc B"),
            (0b1110_000_0011_1_0011_0100_0000_0_11_1_0101,  "rsbs r4, r3, r5, ror r0", "DataProc B"),
            (0b1110_000_0100_0_0011_0100_0000_0_00_1_0101,  "add r4, r3, r5, lsl r0 ", "DataProc B"),
            (0b1110_000_0101_1_0011_0100_0001_0_01_1_0101,  "adcs r4, r3, r5, lsr r1", "DataProc B"),
            (0b1110_000_0110_0_0011_0100_0001_0_10_1_0101,  "sbc r4, r3, r5, asr r1 ", "DataProc B"),
            (0b1110_000_0111_0_0011_0100_1010_0_11_1_0101,  "rsc r4, r3, r5, ror r10", "DataProc B"),
            //          Op   S Rn   Rd   Shift Imm
            (0b1110_001_0000_0_0011_0100_0000_00000001,  "and r4, r3, 1          ", "DataProc C"),
            (0b1110_001_0001_1_0011_0100_0001_00000101,  "eors r4, r3, 0x40000001", "DataProc C"),
            (0b1110_001_0010_0_0011_0100_0010_00000111,  "sub r4, r3, 0x70000000 ", "DataProc C"),
            (0b1110_001_0011_1_0011_0100_0011_00010101,  "rsbs r4, r3, 0x54000000", "DataProc C"),
            (0b1110_001_0100_0_0011_0100_0100_00110101,  "add r4, r3, 0x35000000 ", "DataProc C"),
            (0b1110_001_0101_1_0011_0100_0101_00111111,  "adcs r4, r3, 0xfc00000 ", "DataProc C"),
            (0b1110_001_0110_0_0011_0100_0111_11000000,  "sbc r4, r3, 0x3000000  ", "DataProc C"),
            (0b1110_001_0111_0_0011_0100_1010_11110101,  "rsc r4, r3, 0xf5000    ", "DataProc C"),
            //          P U B W L Rn   Rd   Offset
            (0b1110_010_0_0_0_0_0_0100_0101_000000000011,  "str r5, [r4], -3     ", "TransImm9"),
            (0b1110_010_0_1_0_1_0_0100_0101_000000000111,  "strt r5, [r4], 7     ", "TransImm9"),
            (0b1110_010_1_1_0_0_0_0100_0101_000000011001,  "str r5, [r4, 25]     ", "TransImm9"),
            (0b1110_010_1_1_1_1_0_0100_0101_000011000010,  "strb r5, [r4, 0xc2]! ", "TransImm9"),
            (0b1110_010_1_1_0_1_1_0100_0101_001010010100,  "ldr r5, [r4, 0x294]! ", "TransImm9"),
            (0b1110_010_0_1_1_1_1_0100_0101_000011011011,  "ldrbt r5, [r4], 0xdb ", "TransImm9"),
            (0b1110_010_1_0_0_0_1_0100_0101_100000000000,  "ldr r5, [r4, -0x800] ", "TransImm9"),
            (0b1110_010_0_0_1_0_1_0100_0101_100111001001,  "ldrb r5, [r4], -0x9c9", "TransImm9"),
            (0b1110_010_0_0_1_0_1_0100_0100_100111001001,  "invalid              ", "TransImm9"),
            //          P U B W L Rn   Rd   Shift St   Rm
            (0b1110_011_0_0_0_0_0_0100_0101_00000_00_0_0110,  "str r5, [r4], -r6         ", "TransReg9"),
            (0b1110_011_0_1_0_1_0_0100_0101_00001_01_0_0110,  "strt r5, [r4], r6, lsr 1  ", "TransReg9"),
            (0b1110_011_1_1_0_0_0_0100_0101_00010_10_0_0110,  "str r5, [r4, r6, asr 2]   ", "TransReg9"),
            (0b1110_011_1_1_1_1_0_0100_0101_00110_11_0_0110,  "strb r5, [r4, r6, ror 6]! ", "TransReg9"),
            (0b1110_011_1_1_0_1_1_0100_0101_01001_00_0_0110,  "ldr r5, [r4, r6, lsl 9]!  ", "TransReg9"),
            (0b1110_011_0_1_1_1_1_0100_0101_10100_01_0_0110,  "ldrbt r5, [r4], r6, lsr 20", "TransReg9"),
            (0b1110_011_1_0_0_0_1_0100_0101_01010_10_0_0110,  "ldr r5, [r4, -r6, asr 10] ", "TransReg9"),
            (0b1110_011_0_0_1_0_1_0100_0101_00100_11_0_0110,  "ldrb r5, [r4], -r6, ror 4 ", "TransReg9"),
            (0b1110_011_0_0_1_0_1_0100_0100_00100_11_0_0110,  "invalid                   ", "TransReg9"),
            (0b1110_011_0_0_1_0_1_0100_0101_00100_11_0_0100,  "invalid                   ", "TransReg9"),
            //          P U   W L Rn   Rd   OffH   S H   OffL
            (0b1110_000_0_0_1_0_0_0100_0101_0000_1_0_1_1_0000,  "strh r5, [r4], -0   ", "TransImm10"),
            (0b1110_000_0_1_1_0_0_0100_0101_0000_1_0_1_1_0011,  "strh r5, [r4], 3    ", "TransImm10"),
            (0b1110_000_1_0_1_0_0_0100_0101_0001_1_0_1_1_0011,  "strh r5, [r4, -19]  ", "TransImm10"),
            (0b1110_000_1_1_1_0_0_0100_0101_0010_1_0_1_1_0111,  "strh r5, [r4, 39]   ", "TransImm10"),
            (0b1110_000_0_0_1_0_1_0100_0101_0100_1_0_1_1_1000,  "ldrh r5, [r4], -0x48", "TransImm10"),
            (0b1110_000_0_1_1_0_1_0100_0101_0010_1_1_0_1_0111,  "ldrsb r5, [r4], 39  ", "TransImm10"),
            (0b1110_000_1_0_1_0_1_0100_0101_0000_1_1_1_1_0011,  "ldrsh r5, [r4, -3]  ", "TransImm10"),
            (0b1110_000_1_1_1_0_1_0100_0101_1100_1_0_1_1_1100,  "ldrh r5, [r4, 0xcc] ", "TransImm10"),
            (0b1110_000_1_1_1_0_1_0100_0100_1100_1_0_1_1_1100,  "invalid             ", "TransImm10"),
            //          P U   W L Rn   Rd         S H   Rm
            (0b1110_000_0_0_0_0_0_0100_0101_00001_0_1_1_0110,  "strh r5, [r4], -r6 ", "TransReg10"),
            (0b1110_000_0_1_0_0_0_0100_0101_00001_0_1_1_0110,  "strh r5, [r4], r6  ", "TransReg10"),
            (0b1110_000_1_0_0_0_0_0100_0101_00001_0_1_1_0110,  "strh r5, [r4, -r6] ", "TransReg10"),
            (0b1110_000_1_1_0_1_0_0100_0101_00001_0_1_1_0110,  "strh r5, [r4, r6]! ", "TransReg10"),
            (0b1110_000_0_0_0_0_1_0100_0101_00001_0_1_1_0110,  "ldrh r5, [r4], -r6 ", "TransReg10"),
            (0b1110_000_0_1_0_0_1_0100_0101_00001_1_0_1_0110,  "ldrsb r5, [r4], r6 ", "TransReg10"),
            (0b1110_000_1_0_0_0_1_0100_0101_00001_1_1_1_0110,  "ldrsh r5, [r4, -r6]", "TransReg10"),
            (0b1110_000_1_1_0_1_1_0100_0101_00001_0_1_1_0110,  "ldrh r5, [r4, r6]! ", "TransReg10"),
            (0b1110_000_1_1_0_1_1_0100_0100_00001_0_1_1_0110,  "invalid            ", "TransReg10"),
            (0b1110_000_1_1_0_1_1_0100_0101_00001_0_1_1_0100,  "invalid            ", "TransReg10"),
            //          Xxx                    Yyy
            (0b1110_011_00000000000000000000_1_0000,  "undefined 0, 0", "Undefined"),
            //            B    Rn   Rd            Rm
            (0b1110_00010_0_00_0011_0100_00001001_0101,  "swp r4, r5, [r3] ", "TransSwp12"),
            (0b1110_00010_1_00_0011_0100_00001001_0101,  "swpb r4, r5, [r3]", "TransSwp12"),
            (0b1110_00010_1_00_1111_0100_00001001_0101,  "invalid          ", "TransSwp12"),
            (0b1110_00010_1_00_0011_1111_00001001_0101,  "invalid          ", "TransSwp12"),
            (0b1110_00010_1_00_0011_0100_00001001_1111,  "invalid          ", "TransSwp12"),
            //          P U S W L Rn   RegisterList
            (0b1110_100_0_0_0_0_0_0100_0000000000000001,  "stmda r4, {r0}                        ", "BlockTrans"),
            (0b1110_100_0_0_0_1_0_0100_0000000000000011,  "stmda r4!, {r0, r1}                   ", "BlockTrans"),
            (0b1110_100_0_0_1_0_0_0100_0000000000000101,  "stmda r4, {r0, r2} ^                  ", "BlockTrans"),
            (0b1110_100_0_0_1_1_0_0100_0000000000010110,  "stmda r4!, {r1, r2, r4} ^             ", "BlockTrans"),
            (0b1110_100_0_1_0_0_0_0100_0000000011011001,  "stm r4, {r0, r3, r4, r6, r7}          ", "BlockTrans"),
            (0b1110_100_0_1_0_1_0_0100_0001000100000101,  "stm r4!, {r0, r2, r8, r12}            ", "BlockTrans"),
            (0b1110_100_0_1_1_0_0_0100_0100010001000000,  "stm r4, {r6, r10, r14} ^              ", "BlockTrans"),
            (0b1110_100_0_1_1_1_0_0100_0001001001001010,  "stm r4!, {r1, r3, r6, r9, r12} ^      ", "BlockTrans"),
            (0b1110_100_1_0_0_0_0_0100_0100000011000010,  "stmdb r4, {r1, r6, r7, r14}           ", "BlockTrans"),
            (0b1110_100_1_0_0_1_0_0100_0001010010000010,  "stmdb r4!, {r1, r7, r10, r12}         ", "BlockTrans"),
            (0b1110_100_1_0_1_0_0_0100_0101001100001000,  "stmdb r4, {r3, r8, r9, r12, r14} ^    ", "BlockTrans"),
            (0b1110_100_1_0_1_1_0_0100_0000000100000000,  "stmdb r4!, {r8} ^                     ", "BlockTrans"),
            (0b1110_100_1_1_0_0_0_0100_0000010101010010,  "stmib r4, {r1, r4, r6, r8, r10}       ", "BlockTrans"),
            (0b1110_100_1_1_0_1_0_0100_0000001100001000,  "stmib r4!, {r3, r8, r9}               ", "BlockTrans"),
            (0b1110_100_1_1_1_0_0_0100_0000000000000010,  "stmib r4, {r1} ^                      ", "BlockTrans"),
            (0b1110_100_1_1_1_1_0_0100_0001010100110000,  "stmib r4!, {r4, r5, r8, r10, r12} ^   ", "BlockTrans"),
            (0b1110_100_0_0_0_0_1_0100_0000100101010000,  "ldmda r4, {r4, r6, r8, r11}           ", "BlockTrans"),
            (0b1110_100_0_0_0_1_1_0100_0001000010100000,  "ldmda r4!, {r5, r7, r12}              ", "BlockTrans"),
            (0b1110_100_0_0_1_0_1_0100_0100000110111000,  "ldmda r4, {r3, r4, r5, r7, r8, r14} ^ ", "BlockTrans"),
            (0b1110_100_0_0_1_1_1_0100_0001010001000010,  "ldmda r4!, {r1, r6, r10, r12} ^       ", "BlockTrans"),
            (0b1110_100_0_1_0_0_1_0100_0000000101010000,  "ldm r4, {r4, r6, r8}                  ", "BlockTrans"),
            (0b1110_100_0_1_0_1_1_0100_0001010000101011,  "ldm r4!, {r0, r1, r3, r5, r10, r12}   ", "BlockTrans"),
            (0b1110_100_0_1_1_0_1_0100_1111111111111111,
                    "ldm r4, {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15} ^", "BlockTrans"),
            (0b1110_100_0_1_1_1_1_0100_0001000100010000,  "ldm r4!, {r4, r8, r12} ^              ", "BlockTrans"),
            (0b1110_100_0_1_0_0_1_1111_0000000101010000,  "invalid                  ", "BlockTrans"),
        ];
        println!("# Radare disasm");
        for (inst_bin, _, desc) in &insts_bin_asm {
            println!(
                "rasm2 -a arm -b 32 -o 0x{:08x} -D {:08x} # {}",
                pc,
                (*inst_bin as u32).to_be(),
                desc,
            );
        }
        for (inst_bin, asm_good, _) in &insts_bin_asm {
            let op_raw = op_raw_arm::OpRaw::new(*inst_bin);
            let op = op_raw.to_op();
            let asm = op.asm(pc);
            println!(
                "{:08x}: {:08x} {} {:?}| {:?} - {:?}",
                pc,
                (*inst_bin as u32).to_be(),
                asm,
                asm,
                op,
                op_raw,
            );
            assert_eq!(*asm_good.trim_end(), format!("{}", asm));
        }
    }

    #[test]
    fn op_thumb_asm() {
        let pc = 0x12345678;
        #[rustfmt::skip]
        let insts_bin_asm = vec![
            //     Op Off   Rs  Rd
            (0b000_00_00001_001_010, "lsls r2, r1, 1 ", "Shifted (1)"),
            (0b000_00_00000_001_010, "movs r2, r1    ", "Shifted (1)"),
            (0b000_01_00110_001_010, "lsrs r2, r1, 6 ", "Shifted (1)"),
            (0b000_01_00000_001_010, "lsrs r2, r1, 32", "Shifted (1)"),
            (0b000_10_11001_001_010, "asrs r2, r1, 25", "Shifted (1)"),
            (0b000_10_00000_001_010, "asrs r2, r1, 32", "Shifted (1)"),
            //       I O Rn  Rs  Rd
            (0b00011_0_0_011_001_010, "adds r2, r1, r3", "ADD/SUB (2)"),
            (0b00011_0_1_011_001_010, "subs r2, r1, r3", "ADD/SUB (2)"),
            (0b00011_1_0_001_001_010, "adds r2, r1, 1 ", "ADD/SUB (2)"),
            (0b00011_1_1_110_001_010, "subs r2, r1, 6 ", "ADD/SUB (2)"),
            (0b00011_1_0_000_001_010, "adds r2, r1, 0 ", "ADD/SUB (2)"),
            (0b00011_1_1_000_001_010, "subs r2, r1, 0 ", "ADD/SUB (2)"),
            (0b00011_1_0_101_010_010, "adds r2, r2, 5 ", "ADD/SUB (2)"),
            (0b00011_1_1_101_010_010, "subs r2, r2, 5 ", "ADD/SUB (2)"),
            //     Op Rd  Offset
            (0b001_00_010_00000011, "movs r2, 3   ", "Immedi. (3)"),
            (0b001_01_010_00010100, "cmp r2, 20   ", "Immedi. (3)"),
            (0b001_10_010_10001000, "adds r2, 0x88", "Immedi. (3)"),
            (0b001_11_010_10010110, "subs r2, 0x96", "Immedi. (3)"),
        ];
        println!("# Radare disasm");
        for (inst_bin, _, desc) in &insts_bin_asm {
            println!(
                "rasm2 -a arm -b 16 -o 0x{:08x} -D {:04x} # {}",
                pc,
                (*inst_bin as u16).to_be(),
                desc,
            );
        }
        for (inst_bin, asm_good, _) in &insts_bin_asm {
            let op_raw = op_raw_thumb::OpRaw::new(*inst_bin);
            let op = op_raw.to_op();
            let asm = op.asm(pc);
            println!(
                "{:08x}: {:04x} {} {:?}| {:?} - {:?}",
                pc,
                (*inst_bin as u16).to_be(),
                asm,
                asm,
                op,
                op_raw,
            );
            assert_eq!(*asm_good.trim_end(), format!("{}", asm));
        }
    }
}
