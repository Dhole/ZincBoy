use super::op::*;

use num_traits::FromPrimitive;

include!(concat!(env!("OUT_DIR"), "/op_raw_arm.rs"));

impl OpRaw {
    pub fn to_op(&self) -> Op {
        match self {
            OpRaw::DataProcA(o) => o.to_op(),
            OpRaw::DataProcB(o) => o.to_op(),
            OpRaw::DataProcC(o) => o.to_op(),
            OpRaw::BranchReg(o) => o.to_op(),
            OpRaw::BranchOff(o) => o.to_op(),
            OpRaw::Swi(o) => o.to_op(),
            OpRaw::Multiply(o) => o.to_op(),
            OpRaw::MultiplyLong(o) => o.to_op(),
            OpRaw::PsrImm(o) => o.to_op(),
            OpRaw::PsrReg(o) => o.to_op(),
            OpRaw::TransImm9(o) => o.to_op(),
            OpRaw::TransReg9(o) => o.to_op(),
            OpRaw::TransImm10(o) => o.to_op(),
            OpRaw::TransReg10(o) => o.to_op(),
            OpRaw::TransSwp12(o) => o.to_op(),
            OpRaw::BlockTrans(o) => o.to_op(),
            OpRaw::CoDataTrans(o) => o.to_op(),
            OpRaw::CoDataOp(o) => o.to_op(),
            OpRaw::CoRegTrans(o) => o.to_op(),
            OpRaw::Undefined(o) => o.to_op(),
            OpRaw::Unknown(o) => o.to_op(),
        }
    }
}

impl OpRawDataProcA {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::from_u8(self.cond).unwrap(),
            base: Alu {
            op: AluOp::from_u8(self.op).unwrap(),
            s: self.s,
            rn: self.rn,
            rd: self.rd,
            op2: AluOp2::Register(AluOp2Register {
                shift: AluOp2RegisterShift::Immediate(self.shift),
                st: ShiftType::from_u8(self.typ).unwrap(),
                rm: self.rm,
            }),
        }.validate(self.inst_bin),
        }
    }
}

impl OpRawDataProcB {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::from_u8(self.cond).unwrap(),
            base: Alu {
                op: AluOp::from_u8(self.op).unwrap(),
                s: self.s,
                rn: self.rn,
                rd: self.rd,
                op2: AluOp2::Register(AluOp2Register {
                    shift: AluOp2RegisterShift::Register(self.rs),
                    st: ShiftType::from_u8(self.typ).unwrap(),
                    rm: self.rm,
                }),
            }.validate(self.inst_bin),
        }
    }
}

impl OpRawDataProcC {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::from_u8(self.cond).unwrap(),
            base: Alu {
                op: AluOp::from_u8(self.op).unwrap(),
                s: self.s,
                rn: self.rn,
                rd: self.rd,
                op2: AluOp2::Immediate(AluOp2Immediate {
                    shift: self.shift,
                    immediate: self.immediate,
                }),
            }.validate(self.inst_bin),
        }
    }
}

impl OpRawBranchReg {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::from_u8(self.cond).unwrap(),
            base: Branch {
                link: self.l,
                exchange: true,
                addr: BranchAddr::Register(self.rn),
            }.validate(self.inst_bin),
        }
    }
}

impl OpRawBranchOff {
    pub fn to_op(&self) -> Op {
        let exchange = self.cond == 0b1111;
        let link = if exchange { true } else { self.l };
        let offset = if self.offset < 0b100000000000000000000000 {
            self.offset as i32
        } else {
            -((0b1000000000000000000000000 - self.offset) as i32)
        };
        Op {
            cond: Cond::from_u8(self.cond).unwrap(),
            base: Branch {
                link: link,
                exchange: exchange,
                addr: BranchAddr::Offset(offset, self.l),
            }.validate(self.inst_bin),
        }
    }
}

impl OpRawSwi {
    pub fn to_op(&self) -> Op {
        let cond = Cond::from_u8(self.cond).unwrap();
        // TODO
        // if cond != Cond::AL {
        //     return None;
        // }
        Op {
            cond: cond,
            base: SoftInt {
                imm: self.ignoredby_processor,
            }.validate(self.inst_bin),
        }
    }
}

impl OpRawMultiply {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::from_u8(self.cond).unwrap(),
            base: Multiply {
                acc: if self.a {
                    Some(MultiplyReg::Reg(self.rn))
                } else {
                    None
                },
                signed: false,
                set_cond: self.s,
                res: MultiplyReg::Reg(self.rd),
                ops_reg: (self.rm, self.rs),
            }.validate(self.inst_bin),
        }
    }
}

impl OpRawMultiplyLong {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::from_u8(self.cond).unwrap(),
            base: Multiply {
                acc: if self.a {
                    Some(MultiplyReg::RegHiLo(self.rd_hi, self.rd_lo))
                } else {
                    None
                },
                signed: self.u,
                set_cond: self.s,
                res: MultiplyReg::RegHiLo(self.rd_hi, self.rd_lo),
                ops_reg: (self.rm, self.rs),
            }.validate(self.inst_bin),
        }
    }
}

impl OpRawUndefined {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::from_u8(self.cond).unwrap(),
            base: OpBase::Undefined(Undefined {
                xxx: (self.xxx, self.yyy),
            }),
        }
    }
}

impl OpRawPsrImm {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::from_u8(self.cond).unwrap(),
            base: Psr {
                spsr: self.p,
                op: PsrOp::Msr(Msr {
                    f: self.field & 0b1000 != 0,
                    s: self.field & 0b0100 != 0,
                    x: self.field & 0b0010 != 0,
                    c: self.field & 0b0001 != 0,
                    src: MsrSrc::Immediate(MsrSrcImmediate {
                        shift: self.shift,
                        immediate: self.immediate as u32,
                    }),
                }),
            }.validate(self.inst_bin),
        }
    }
}

impl OpRawPsrReg {
    pub fn to_op(&self) -> Op {
        let psr = Psr {
            spsr: self.p,
            op: if self.l {
                PsrOp::Msr(Msr {
                    f: self.field & 0b1000 != 0,
                    s: self.field & 0b0100 != 0,
                    x: self.field & 0b0010 != 0,
                    c: self.field & 0b0001 != 0,
                    src: MsrSrc::Register(self.rm),
                })
            } else {
                PsrOp::Mrs(Mrs { rd: self.rd })
            },
        };
        Op {
            cond: Cond::from_u8(self.cond).unwrap(),
            base: match &psr.op {
                PsrOp::Mrs(_) if self.field != 0b1111 => OpBase::Invalid(Invalid::new(self.inst_bin)),
                _ => psr.validate(self.inst_bin),
            }
        }
    }
}

impl OpRawTransImm9 {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::from_u8(self.cond).unwrap(),
            base: Memory {
                add_offset: self.u,
                pre_post: if self.p {
                    MemoryPrePost::Pre(self.w)
                } else {
                    MemoryPrePost::Post(self.w)
                },
                op: if self.l {
                    MemoryOp::Load
                } else {
                    MemoryOp::Store
                },
                size: if self.b {
                    MemorySize::Byte
                } else {
                    MemorySize::Word
                },
                signed: false,
                addr: MemoryAddr::Immediate(self.offset),
                rn: self.rn,
                rd: self.rd,
            }.validate(self.inst_bin),
        }
    }
}

impl OpRawTransReg9 {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::from_u8(self.cond).unwrap(),
            base: Memory {
                add_offset: self.u,
                pre_post: if self.p {
                    MemoryPrePost::Pre(self.w)
                } else {
                    MemoryPrePost::Post(self.w)
                },
                op: if self.l {
                    MemoryOp::Load
                } else {
                    MemoryOp::Store
                },
                size: if self.b {
                    MemorySize::Byte
                } else {
                    MemorySize::Word
                },
                signed: false,
                addr: MemoryAddr::Register(MemoryAddrReg {
                    shift: self.shift,
                    st: ShiftType::from_u8(self.typ).unwrap(),
                    rm: self.rm,
                }),
                rn: self.rn,
                rd: self.rd,
            }.validate(self.inst_bin),
        }
    }
}

impl OpRawTransImm10 {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::from_u8(self.cond).unwrap(),
            base: Memory {
                add_offset: self.u,
                pre_post: if self.p {
                    MemoryPrePost::Pre(self.w)
                } else {
                    MemoryPrePost::Post(false)
                },
                op: if self.l {
                    MemoryOp::Load
                } else {
                    MemoryOp::Store
                },
                size: if self.h {
                    MemorySize::Half
                } else {
                    MemorySize::Byte
                },
                signed: self.s,
                addr: MemoryAddr::Immediate((self.offset_h << 4 | self.offset_l).into()),
                rn: self.rn,
                rd: self.rd,
            }.validate(self.inst_bin),
        }
    }
}

impl OpRawTransReg10 {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::from_u8(self.cond).unwrap(),
            base: Memory {
                add_offset: self.u,
                pre_post: if self.p {
                    MemoryPrePost::Pre(self.w)
                } else {
                    MemoryPrePost::Post(false)
                },
                op: if self.l {
                    MemoryOp::Load
                } else {
                    MemoryOp::Store
                },
                size: if self.h {
                    MemorySize::Half
                } else {
                    MemorySize::Byte
                },
                signed: self.s,
                addr: MemoryAddr::Register(MemoryAddrReg {
                    rm: self.rm,
                    st: ShiftType::LSL,
                    shift: 0,
                }),
                rn: self.rn,
                rd: self.rd,
            }.validate(self.inst_bin),
        }
    }
}

impl OpRawBlockTrans {
    pub fn to_op(&self) -> Op {
        let mut reg_list = [false; 16];
        (0..16).for_each(|i| reg_list[i] = { self.register_list & (1 << i) != 0 });
        Op {
            cond: Cond::from_u8(self.cond).unwrap(),
            base: MemoryBlock {
                pre: self.p,
                add_offset: self.u,
                psr_force_user_bit: self.s,
                write_back: self.w,
                op: if self.l {
                    MemoryOp::Load
                } else {
                    MemoryOp::Store
                },
                rn: self.rn,
                reg_list: reg_list,
            }.validate(self.inst_bin),
        }
        // TODO: Handle Strange Effects on Invalid Rlist's (gbatek.txt:50409)
    }
}

impl OpRawTransSwp12 {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::from_u8(self.cond).unwrap(),
            base: Swap {
                rn: self.rn,
                rd: self.rd,
                rm: self.rm,
                byte: self.b,
            }.validate(self.inst_bin),
        }
    }
}

impl OpRawCoDataTrans {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::from_u8(self.cond).unwrap(),
            base: CoOp::Todo(self.inst_bin).validate(self.inst_bin),
        }
    }
}

impl OpRawCoDataOp {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::from_u8(self.cond).unwrap(),
            base: CoOp::Todo(self.inst_bin).validate(self.inst_bin),
        }
    }
}

impl OpRawCoRegTrans {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::from_u8(self.cond).unwrap(),
            base: CoOp::Todo(self.inst_bin).validate(self.inst_bin),
        }
    }
}

impl OpRawUnknown {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::from_u8(self.cond).unwrap(),
            base: OpBase::Unknown(Unknown { inst: InstructionBin::ARM(self.inst_bin) }),
        }
    }
}
