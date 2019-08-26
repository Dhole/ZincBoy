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
                }),
            }),
        }
    }
}

impl OpRawAddSub {
    pub fn to_op(&self) -> Op {
        let op = match self.o {
            false => AluOp::ADD,
            true => AluOp::SUB,
        };
        let op2 = if self.i {
            AluOp2::Immediate(AluOp2Immediate {
                shift: 0,
                immediate: self.rn,
            })
        } else {
            AluOp2::Register(AluOp2Register {
                shift: AluOp2RegisterShift::Immediate(0),
                st: ShiftType::LSL,
                rm: self.rn,
            })
        };
        Op {
            cond: Cond::AL,
            base: OpBase::Alu(Alu {
                thumb: false,
                op: op,
                s: true,
                rn: self.rs,
                rd: self.rd,
                op2: op2,
            }),
        }
    }
}

impl OpRawImm {
    pub fn to_op(&self) -> Op {
        let op = match self.op {
            0b00 => AluOp::MOV,
            0b01 => AluOp::CMP,
            0b10 => AluOp::ADD,
            0b11 => AluOp::SUB,
            _ => unreachable!(),
        };
        Op {
            cond: Cond::AL,
            base: OpBase::Alu(Alu {
                thumb: true,
                op: op,
                s: if let AluOp::CMP = op { false } else { true },
                rn: self.rd,
                rd: self.rd,
                op2: AluOp2::Immediate(AluOp2Immediate {
                    shift: 0,
                    immediate: self.offset,
                }),
            }),
        }
    }
}

impl OpRawAluOp {
    pub fn to_op(&self) -> Op {
        let mut rn = 0;
        let mut op = AluOp::MOV;
        let mut op2 = AluOp2::Register(AluOp2Register{ 
                shift: AluOp2RegisterShift::Immediate(0),
                st: ShiftType::LSL,
                rm: self.rs,
             });
        match self.op {
            0x2 | 0x3 | 0x4 | 0x7 => {
                let st = match self.op {
                    0x2 => ShiftType::LSL,
                    0x3 => ShiftType::LSR,
                    0x4 => ShiftType::ASR,
                    0x7 => ShiftType::ROR,
                    _ => unreachable!(),
                };
                rn = 0;
                op2 = AluOp2::Register(AluOp2Register {
                    shift: AluOp2RegisterShift::Register(self.rs),
                    st: st,
                    rm: self.rd,
                });
            },
            0x9 => {
                op = AluOp::RSB;
            },
            0xd => {
                return Op {
                    cond: Cond::AL,
                    base: OpBase::Multiply(Multiply {
                        acc: None,
                        signed: false,
                        set_cond: true,
                        res: MultiplyReg::Reg(self.rd),
                        ops_reg: (self.rd, self.rs),
                    }),
                };
            },
            _ => {
                op = match self.op {
                    0x0 => AluOp::AND,
                    0x1 => AluOp::EOR,
                    0x5 => AluOp::ADC,
                    0x6 => AluOp::SBC,
                    0x8 => AluOp::TST,
                    0xa => AluOp::CMP,
                    0xb => AluOp::CMN,
                    0xc => AluOp::ORR,
                    0xe => AluOp::BIC,
                    0xf => AluOp::MVN,
                    _ => unreachable!(),
                };
                rn = self.rd;
            },
        }
        Op {
            cond: Cond::AL,
            base: OpBase::Alu(Alu {
                thumb: true,
                op: op,
                s: match op {
                    AluOp::TST | AluOp::CMP | AluOp::CMN => false,
                    _ => true,
                },
                rn: rn,
                rd: self.rd,
                op2: op2,
            }),
        }
    }
}

impl OpRawHiRegBx {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::AL,
            base: OpBase::Unknown(Unknown {
                inst: InstructionBin::Thumb(self.inst_bin),
            }),
        }
    }
}

impl OpRawLdrPc {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::AL,
            base: OpBase::Unknown(Unknown {
                inst: InstructionBin::Thumb(self.inst_bin),
            }),
        }
    }
}

impl OpRawLdrStr {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::AL,
            base: OpBase::Unknown(Unknown {
                inst: InstructionBin::Thumb(self.inst_bin),
            }),
        }
    }
}

impl OpRawXHSbSh {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::AL,
            base: OpBase::Unknown(Unknown {
                inst: InstructionBin::Thumb(self.inst_bin),
            }),
        }
    }
}

impl OpRawXB {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::AL,
            base: OpBase::Unknown(Unknown {
                inst: InstructionBin::Thumb(self.inst_bin),
            }),
        }
    }
}

impl OpRawXH {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::AL,
            base: OpBase::Unknown(Unknown {
                inst: InstructionBin::Thumb(self.inst_bin),
            }),
        }
    }
}

impl OpRawXSp {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::AL,
            base: OpBase::Unknown(Unknown {
                inst: InstructionBin::Thumb(self.inst_bin),
            }),
        }
    }
}

impl OpRawAddPcSp {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::AL,
            base: OpBase::Unknown(Unknown {
                inst: InstructionBin::Thumb(self.inst_bin),
            }),
        }
    }
}

impl OpRawAddSpNn {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::AL,
            base: OpBase::Unknown(Unknown {
                inst: InstructionBin::Thumb(self.inst_bin),
            }),
        }
    }
}

impl OpRawPushPop {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::AL,
            base: OpBase::Unknown(Unknown {
                inst: InstructionBin::Thumb(self.inst_bin),
            }),
        }
    }
}

impl OpRawStmLdm {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::AL,
            base: OpBase::Unknown(Unknown {
                inst: InstructionBin::Thumb(self.inst_bin),
            }),
        }
    }
}

impl OpRawBranchCond {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::AL,
            base: OpBase::Unknown(Unknown {
                inst: InstructionBin::Thumb(self.inst_bin),
            }),
        }
    }
}

impl OpRawSwi {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::AL,
            base: OpBase::Unknown(Unknown {
                inst: InstructionBin::Thumb(self.inst_bin),
            }),
        }
    }
}

impl OpRawBranch {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::AL,
            base: OpBase::Unknown(Unknown {
                inst: InstructionBin::Thumb(self.inst_bin),
            }),
        }
    }
}

impl OpRawBranchLink {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::AL,
            base: OpBase::Unknown(Unknown {
                inst: InstructionBin::Thumb(self.inst_bin),
            }),
        }
    }
}

impl OpRawUnknown {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::from_u8(self.cond).unwrap(),
            base: OpBase::Unknown(Unknown {
                inst: InstructionBin::Thumb(self.inst_bin),
            }),
        }
    }
}
