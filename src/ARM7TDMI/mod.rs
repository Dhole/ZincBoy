use enum_map::EnumMap;
use std::fmt;
use std::ptr;

#[allow(dead_code)]
const REG_SP: usize = 13;
#[allow(dead_code)]
const REG_LR: usize = 14;
#[allow(dead_code)]
const REG_PC: usize = 15;

#[derive(Debug, PartialEq)]
// ARM7TDMI
pub struct Cpu {
    reg: [*mut u32; 16],
    reg_usr_0_7: [u32; 8],
    reg_usr_8_12: [u32; 5],
    reg_usr_15: u32,
    reg_fiq_8_12: [u32; 5],
    reg_mode_13_14: EnumMap<RegBank, [u32; 2]>,
    cpsr: Cpsr,
    spsr: EnumMap<RegBank, Cpsr>,
}

//pub struct Registers {}

impl Cpu {
    pub fn new() -> Self {
        let cpsr = Cpsr {
            status: 0,
            mode: Mode::Undefined,
        };

        let mut cpu = Cpu {
            reg: [ptr::null_mut(); 16],
            reg_usr_0_7: [0; 8],
            reg_usr_8_12: [0; 5],
            reg_usr_15: 0,
            reg_fiq_8_12: [0; 5],
            reg_mode_13_14: enum_map! {_ => [0; 2]},
            cpsr: cpsr,
            spsr: enum_map! {_ => cpsr},
        };
        for i in 0..8 {
            cpu.reg[i] = &mut cpu.reg_usr_0_7[i] as *mut u32;
        }
        for i in 8..13 {
            cpu.reg[i] = &mut cpu.reg_usr_8_12[i - 8] as *mut u32;
        }
        cpu.reg[13] = &mut cpu.reg_mode_13_14[RegBank::User][0] as *mut u32;
        cpu.reg[14] = &mut cpu.reg_mode_13_14[RegBank::User][1] as *mut u32;
        cpu.reg[15] = &mut cpu.reg_usr_15 as *mut u32;
        cpu.set_mode(Mode::User);
        cpu.cpsr.status |= FLAG_MASK_N;
        cpu
    }

    fn set_mode(&mut self, mode: Mode) {
        if mode == self.cpsr.mode {
            return;
        }
        if self.cpsr.mode == Mode::FIQ {
            // Leaving FIQ mode
            for i in 8..13 {
                self.reg[i] = &mut self.reg_usr_8_12[i - 8] as *mut u32;
            }
        } else if mode == Mode::FIQ {
            // Entering FIQ mode
            for i in 8..13 {
                self.reg[i] = &mut self.reg_fiq_8_12[i - 8] as *mut u32;
            }
        }
        let reg_bank = RegBank::from(mode);
        self.reg[13] = &mut self.reg_mode_13_14[reg_bank][0] as *mut u32;
        self.reg[14] = &mut self.reg_mode_13_14[reg_bank][1] as *mut u32;
        if mode != Mode::System && mode != Mode::User {
            self.spsr[reg_bank] = self.cpsr;
        }
        self.cpsr.set_mode(mode);
    }
}

impl fmt::Display for Cpu {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "\tSys/User   FIQ    Supervis  Abort     IRQ    Undefined\n"
        )?;
        for i in 0..8 {
            write!(f, "R{}\t{:08x}\n", i, self.reg_usr_0_7[i])?;
        }
        for i in 8..13 {
            write!(
                f,
                "R{}\t{:08x} {:08x}\n",
                i,
                self.reg_usr_8_12[i - 8],
                self.reg_fiq_8_12[i - 8]
            )?;
        }
        for i in 13..15 {
            write!(f, "R{}\t", i)?;
            for (_, r) in self.reg_mode_13_14 {
                write!(f, "{:08x} ", r[i - 13])?;
            }
            write!(f, "\n")?;
        }
        write!(f, "R{}\t{:08x}\n", 15, self.reg_usr_15)?;
        //write!(f, "CPSR\t{:032b}\n", self.cpsr.status)?;
        write!(f, "CPSR")?;
        for (name, mask) in FLAG_LIST.iter() {
            write!(f, "\t{}:{:01b}\n", name, (self.cpsr.status & mask != 0) as u32)?;
        }
        write!(f, "\tM:{:05b}\n", self.cpsr.status & FLAG_MASK_M4_M0)?;
        write!(f, "SPSR")?;
        for (name, mask) in FLAG_LIST.iter() {
            write!(f, "\t")?;
            for (bank, psr) in self.spsr {
                if bank == RegBank::User {
                    write!(f, "         ")?;
                } else {
                    write!(f, "{}:{:01b}      ", name, (psr.status & mask != 0) as u32)?;
                }
            }
            write!(f, "\n")?;
        }
        write!(f, "\t")?;
        for (bank, psr) in self.spsr {
            if bank == RegBank::User {
                write!(f, "         ")?;
            } else {
                write!(f, "M:{:05b}  ", psr.status & FLAG_MASK_M4_M0)?;
            }
        }
        write!(f, "\n")?;
        write!(f, "\n")?;
        Ok(())
    }
}

// CPU Mode
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Mode {
    //OldUser = 0x00,
    //OldFIQ = 0x01,
    //OldIRQ = 0x02,
    //OldSupervisor = 0x03,
    User = 0x10,
    FIQ = 0x11,
    IRQ = 0x12,
    Supervisor = 0x13,
    Abort = 0x17,
    Undefined = 0x1B,
    System = 0x1F,
}

#[derive(Debug, PartialEq, Enum, Clone, Copy)]
pub enum RegBank {
    User = 0,
    FIQ = 1,
    IRQ = 2,
    Supervisor = 3,
    Abort = 4,
    Undefined = 5,
}

impl From<Mode> for RegBank {
    fn from(mode: Mode) -> Self {
        match mode {
            Mode::User => RegBank::User,
            Mode::FIQ => RegBank::FIQ,
            Mode::IRQ => RegBank::IRQ,
            Mode::Supervisor => RegBank::Supervisor,
            Mode::Undefined => RegBank::Undefined,
            Mode::System => RegBank::User,
            _ => RegBank::User,
        }
    }
}

const FLAG_MASK_N: u32 = 1 << 31; // Sign Flag
const FLAG_MASK_Z: u32 = 1 << 30; // Zero Flag
const FLAG_MASK_C: u32 = 1 << 29; // Carry Flag
const FLAG_MASK_V: u32 = 1 << 28; // Overflow Flag
const FLAG_MASK_Q: u32 = 1 << 27; // Sticky Overflow
const FLAG_MASK_I: u32 = 1 << 7; // IRQ disable
const FLAG_MASK_F: u32 = 1 << 6; // FIQ disable
const FLAG_MASK_T: u32 = 1 << 5; // State Bit
const FLAG_MASK_M4_M0: u32 = 0b11111;

const FLAG_LIST: [(&str, u32); 8] = [("N", FLAG_MASK_N), ("Z", FLAG_MASK_Z), ("C", FLAG_MASK_C), ("V", FLAG_MASK_V), ("Q", FLAG_MASK_Q), ("I", FLAG_MASK_I), ("F", FLAG_MASK_F), ("T", FLAG_MASK_T)];

#[derive(Debug, PartialEq, Clone, Copy)]
// Current Program Status Register
pub struct Cpsr {
    status: u32,
    mode: Mode,
}

impl Cpsr {
    fn set_mode(&mut self, mode: Mode) {
        self.status &= !FLAG_MASK_M4_M0;
        self.status |= mode as u32;
        self.mode = mode;
    }
}

//  |..3 ..................2 ..................1 ..................0|
//  |1_0_9_8_7_6_5_4_3_2_1_0_9_8_7_6_5_4_3_2_1_0_9_8_7_6_5_4_3_2_1_0|
//  |_Cond__|0_0_0|___Op__|S|__Rn___|__Rd___|__Shift__|Typ|0|__Rm___| DataProc
//  |_Cond__|0_0_0|___Op__|S|__Rn___|__Rd___|__Rs___|0|Typ|1|__Rm___| DataProc
//  |_Cond__|0_0_1|___Op__|S|__Rn___|__Rd___|_Shift_|___Immediate___| DataProc
//  |_Cond__|0_0_1_1_0|P|1|0|_Field_|__Rd___|_Shift_|___Immediate___| PSR Imm
//  |_Cond__|0_0_0_1_0|P|L|0|_Field_|__Rd___|0_0_0_0|0_0_0_0|__Rm___| PSR Reg
//  |_Cond__|0_0_0_1_0_0_1_0_1_1_1_1_1_1_1_1_1_1_1_1|0_0|L|1|__Rn___| BX,BLX
//  |1_1_1_0|0_0_0_1_0_0_1_0|_____immediate_________|0_1_1_1|_immed_| BKPT ARM9
//  |_Cond__|0_0_0_1_0_1_1_0_1_1_1_1|__Rd___|1_1_1_1|0_0_0_1|__Rm___| CLZ  ARM9
//  |_Cond__|0_0_0_1_0|Op_|0|__Rn___|__Rd___|0_0_0_0|0_1_0_1|__Rm___| QALU ARM9
//  |_Cond__|0_0_0_0_0_0|A|S|__Rd___|__Rn___|__Rs___|1_0_0_1|__Rm___| Multiply
//  |_Cond__|0_0_0_0_1|U|A|S|_RdHi__|_RdLo__|__Rs___|1_0_0_1|__Rm___| MulLong
//  |_Cond__|0_0_0_1_0|Op_|0|Rd/RdHi|Rn/RdLo|__Rs___|1|y|x|0|__Rm___| MulHalfARM9
//  |_Cond__|0_0_0_1_0|B|0_0|__Rn___|__Rd___|0_0_0_0|1_0_0_1|__Rm___| TransSwp12
//  |_Cond__|0_0_0|P|U|0|W|L|__Rn___|__Rd___|0_0_0_0|1|S|H|1|__Rm___| TransReg10
//  |_Cond__|0_0_0|P|U|1|W|L|__Rn___|__Rd___|OffsetH|1|S|H|1|OffsetL| TransImm10
//  |_Cond__|0_1_0|P|U|B|W|L|__Rn___|__Rd___|_________Offset________| TransImm9
//  |_Cond__|0_1_1|P|U|B|W|L|__Rn___|__Rd___|__Shift__|Typ|0|__Rm___| TransReg9
//  |_Cond__|0_1_1|________________xxx____________________|1|__xxx__| Undefined
//  |_Cond__|1_0_0|P|U|S|W|L|__Rn___|__________Register_List________| BlockTrans
//  |_Cond__|1_0_1|L|___________________Offset______________________| B,BL,BLX
//  |_Cond__|1_1_0|P|U|N|W|L|__Rn___|__CRd__|__CP#__|____Offset_____| CoDataTrans
//  |_Cond__|1_1_0_0_0_1_0|L|__Rn___|__Rd___|__CP#__|_CPopc_|__CRm__| CoRR ARM9
//  |_Cond__|1_1_1_0|_CPopc_|__CRn__|__CRd__|__CP#__|_CP__|0|__CRm__| CoDataOp
//  |_Cond__|1_1_1_0|CPopc|L|__CRn__|__Rd___|__CP#__|_CP__|1|__CRm__| CoRegTrans
//  |_Cond__|1_1_1_1|_____________Ignored_by_Processor______________| SWI

fn test_bit(v: u32, bit: u8) -> bool {
    (v & (1 << bit)) != 0
}

fn decode_armv4_op(op: u32) {
    match op & 0b00001110000000000000000000000000 {
    0b0000000000000000000000000000 => {
        // Multiply
        // Multiply long
        // Signel data swap
        // Branch and Exchange
        // Halfword data transfer, register offset
        // Halfword data transfer, immediate offset
    },
    0b0010000000000000000000000000 => {
        // Data processing (DataProc)
        // FSR transfer (TransFSR)
    },
    0b0100000000000000000000000000 => {
        // TransImm9
    },
    0b0110000000000000000000000000 => {
        // Single data transfer (TransReg9)
        // Undefined
    },
    0b1000000000000000000000000000 => {
        // Data block transfer (BlockTrans)
    },
    0b1010000000000000000000000000 => {
        // Branch (B,BL,BLX)
    },
    0b1100000000000000000000000000 => {
        // CoDataTrans
    },
    0b1110000000000000000000000000 => {
        // CoDataOp
        // CoRegTrans
        // SWI
    },
    _ => unreachable!(),
    }
}

#[allow(dead_code)]
const OP_MASK_COND: u32 = 0b11110000000000000000000000000000;

const OP_MASK_PREFIX_DATAPROC: u32 =            0b00000000000000000000000000000000;
const OP_MASK_PREFIX_MASK_DATAPROC: u32 =       0b00001100000000000000000000000000;
const OP_MASK_PREFIX_LOADSTORE: u32 =           0b00000100000000000000000000000000;
const OP_MASK_PREFIX_MASK_LOADSTORE: u32 =      0b00001100000000000000000000000000;
const OP_MASK_PREFIX_MULTILOADSTORE: u32 =      0b00001000000000000000000000000000;
const OP_MASK_PREFIX_MASK_MULTILOADSTORE: u32 = 0b00001110000000000000000000000000;
const OP_MASK_PREFIX_BRANCH: u32 =              0b00001010000000000000000000000000;
const OP_MASK_PREFIX_MASK_BRANCH: u32 =         0b00001110000000000000000000000000;
const OP_MASK_PREFIX_SWI: u32 =                 0b00001111000000000000000000000000;
const OP_MASK_PREFIX_MASK_SWI: u32 =            0b00001111000000000000000000000000;
//const OP_MASK_PREFIX_ PSR Imm
//const OP_MASK_PREFIX_ PSR Reg
//const OP_MASK_PREFIX_ BX,BLX
//const OP_MASK_PREFIX_ BKPT ARM9
//const OP_MASK_PREFIX_ CLZ  ARM9
//const OP_MASK_PREFIX_ QALU ARM9
//const OP_MASK_PREFIX_ Multiply
//const OP_MASK_PREFIX_ MulLong
//const OP_MASK_PREFIX_ MulHalfARM9
//const OP_MASK_PREFIX_ TransSwp12
//const OP_MASK_PREFIX_ TransReg10
//const OP_MASK_PREFIX_ TransImm10
//const OP_MASK_PREFIX_ TransImm9
//const OP_MASK_PREFIX_ TransReg9
//const OP_MASK_PREFIX_ Undefined
//const OP_MASK_PREFIX_ BlockTrans
//const OP_MASK_PREFIX_ B,BL,BLX
//const OP_MASK_PREFIX_ CoDataTrans
//const OP_MASK_PREFIX_ CoRR ARM9
//const OP_MASK_PREFIX_ CoDataOp
//const OP_MASK_PREFIX_ CoRegTrans
//const OP_MASK_PREFIX_ SWI

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
