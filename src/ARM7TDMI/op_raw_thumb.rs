use super::op::*;
//
// use num_traits::FromPrimitive;

include!(concat!(env!("OUT_DIR"), "/op_raw_thumb.rs"));

impl OpRawShifted {
    pub fn to_op(&self) -> Op {
        Op {
            cond: Cond::AL,
            base: OpBase::Unknown(Unknown { inst: InstructionBin::Thumb(self.inst_bin) }),
        }
    }
}
