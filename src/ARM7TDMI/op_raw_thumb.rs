use super::op::*;

use num_traits::FromPrimitive;

include!(concat!(env!("OUT_DIR"), "/op_raw_thumb.rs"));

impl OpRaw {
    pub fn to_op(&self) -> Op {
        match self {
            OpRaw::StmLdm(o) => o.to_op(),
            OpRaw::AddSpNn(o) => o.to_op(),
            OpRaw::Swi(o) => o.to_op(),
            OpRaw::AluOp(o) => o.to_op(),
            OpRaw::Shifted(o) => o.to_op(),
            OpRaw::BranchLink(o) => o.to_op(),
            OpRaw::Imm(o) => o.to_op(),
            OpRaw::XSp(o) => o.to_op(),
            OpRaw::PushPop(o) => o.to_op(),
            OpRaw::AddPcSp(o) => o.to_op(),
            OpRaw::BranchCond(o) => o.to_op(),
            OpRaw::XHSbSh(o) => o.to_op(),
            OpRaw::XH(o) => o.to_op(),
            OpRaw::HiRegBx(o) => o.to_op(),
            OpRaw::LdrStr(o) => o.to_op(),
            OpRaw::AddSub(o) => o.to_op(),
            OpRaw::XB(o) => o.to_op(),
            OpRaw::LdrPc(o) => o.to_op(),
            OpRaw::Branch(o) => o.to_op(),
            OpRaw::Unknown(o) => o.to_op(),
        }
    }
}


impl OpRawShifted {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::AL,
            base: OpBase::Alu(Alu {
                thumb: true,
                op: AluOp::MOV,
                s: true,
                rn: 0,
                rd: self.rd,
                op2: AluOp2::Register(AluOp2Register {
                    shift: AluOp2RegisterShift::Immediate(self.shift),
                    st: ShiftType::from_u8(self.op).unwrap(),
                    rm: self.rs,
                })
            }),
        }
    }
}

impl OpRawAddSub {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::AL,
            base: OpBase::Unknown(Unknown { inst: InstructionBin::Thumb(self.inst_bin) }),
        }
    }
}

impl OpRawImm {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::AL,
            base: OpBase::Unknown(Unknown { inst: InstructionBin::Thumb(self.inst_bin) }),
        }
    }
}

impl OpRawAluOp {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::AL,
            base: OpBase::Unknown(Unknown { inst: InstructionBin::Thumb(self.inst_bin) }),
        }
    }
}

impl OpRawHiRegBx {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::AL,
            base: OpBase::Unknown(Unknown { inst: InstructionBin::Thumb(self.inst_bin) }),
        }
    }
}

impl OpRawLdrPc {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::AL,
            base: OpBase::Unknown(Unknown { inst: InstructionBin::Thumb(self.inst_bin) }),
        }
    }
}

impl OpRawLdrStr {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::AL,
            base: OpBase::Unknown(Unknown { inst: InstructionBin::Thumb(self.inst_bin) }),
        }
    }
}

impl OpRawXHSbSh {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::AL,
            base: OpBase::Unknown(Unknown { inst: InstructionBin::Thumb(self.inst_bin) }),
        }
    }
}

impl OpRawXB {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::AL,
            base: OpBase::Unknown(Unknown { inst: InstructionBin::Thumb(self.inst_bin) }),
        }
    }
}

impl OpRawXH {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::AL,
            base: OpBase::Unknown(Unknown { inst: InstructionBin::Thumb(self.inst_bin) }),
        }
    }
}

impl OpRawXSp {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::AL,
            base: OpBase::Unknown(Unknown { inst: InstructionBin::Thumb(self.inst_bin) }),
        }
    }
}

impl OpRawAddPcSp {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::AL,
            base: OpBase::Unknown(Unknown { inst: InstructionBin::Thumb(self.inst_bin) }),
        }
    }
}

impl OpRawAddSpNn {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::AL,
            base: OpBase::Unknown(Unknown { inst: InstructionBin::Thumb(self.inst_bin) }),
        }
    }
}

impl OpRawPushPop {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::AL,
            base: OpBase::Unknown(Unknown { inst: InstructionBin::Thumb(self.inst_bin) }),
        }
    }
}

impl OpRawStmLdm {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::AL,
            base: OpBase::Unknown(Unknown { inst: InstructionBin::Thumb(self.inst_bin) }),
        }
    }
}

impl OpRawBranchCond {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::AL,
            base: OpBase::Unknown(Unknown { inst: InstructionBin::Thumb(self.inst_bin) }),
        }
    }
}

impl OpRawSwi {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::AL,
            base: OpBase::Unknown(Unknown { inst: InstructionBin::Thumb(self.inst_bin) }),
        }
    }
}

impl OpRawBranch {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::AL,
            base: OpBase::Unknown(Unknown { inst: InstructionBin::Thumb(self.inst_bin) }),
        }
    }
}

impl OpRawBranchLink {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::AL,
            base: OpBase::Unknown(Unknown { inst: InstructionBin::Thumb(self.inst_bin) }),
        }
    }
}

impl OpRawUnknown {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::from_u8(self.cond).unwrap(),
            base: OpBase::Unknown(Unknown { inst: InstructionBin::Thumb(self.inst_bin) }),
        }
    }
}
