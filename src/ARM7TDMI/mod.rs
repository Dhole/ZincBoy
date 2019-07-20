#![allow(dead_code)]

pub mod op;
pub mod op_raw_arm;
pub mod op_raw_thumb;

use enum_map::EnumMap;
use std::fmt;
use std::ptr;

const REG_SP: usize = 13;
const REG_LR: usize = 14;
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
            write!(
                f,
                "\t{}:{:01b}\n",
                name,
                (self.cpsr.status & mask != 0) as u32
            )?;
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

const FLAG_LIST: [(&str, u32); 8] = [
    ("N", FLAG_MASK_N),
    ("Z", FLAG_MASK_Z),
    ("C", FLAG_MASK_C),
    ("V", FLAG_MASK_V),
    ("Q", FLAG_MASK_Q),
    ("I", FLAG_MASK_I),
    ("F", FLAG_MASK_F),
    ("T", FLAG_MASK_T),
];

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
