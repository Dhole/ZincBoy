use num_derive::{FromPrimitive, ToPrimitive};
use num_traits::FromPrimitive;

include!(concat!(env!("OUT_DIR"), "/op_raw.rs"));

#[derive(Debug, FromPrimitive, ToPrimitive)]
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

#[derive(Debug, FromPrimitive, ToPrimitive)]
pub enum ShiftType {
    LSL = 0,
    LSR = 1,
    ASR = 2,
    ROR = 3,
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

#[derive(Debug)]
pub struct Alu {
    op: AluOp,
    rn: u8,
    rd: u8,
    op2: AluOp2,
}

#[derive(Debug)]
pub enum OpBase {
    Alu(Alu),
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
                    rn: o.rn,
                    rd: o.rd,
                    op2: AluOp2::Immediate(AluOp2Immediate {
                        shift: o.shift,
                        immediate: o.immediate,
                    }),
                }),
            },
            // OpRaw::DataProcB(o) => Op {
            //     cond: Cond::from_u8(o.cond).unwrap(),
            // },
            // OpRaw::DataProcC(o) => Op {
            //     cond: Cond::from_u8(o.cond).unwrap(),
            // },
            _ => return None,
        };
        Some(op)
    }
}
