use enum_map::EnumMap;
use std::fmt;
use std::ptr;

#[allow(dead_code)]
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
    spsr: EnumMap<RegBank, Cpsr>, //spsr_fiq: Cpsr,
                                  //spsr_svc: Cpsr,
                                  //spsr_abt: Cpsr,
                                  //spsr_irq: Cpsr,
                                  //spsr_und: Cpsr
}

//pub struct Registers {}

#[allow(dead_code)]
impl Cpu {
    pub fn new() -> Self {
        let cpsr = Cpsr {
            status: 0,
            mode: Mode::User,
        };
        Cpu {
            reg: [ptr::null_mut(); 16],
            reg_usr_0_7: [0; 8],
            reg_usr_8_12: [0; 5],
            reg_usr_15: 0,
            reg_fiq_8_12: [0; 5],
            reg_mode_13_14: enum_map! {_ => [0; 2]},
            cpsr: cpsr,
            spsr: enum_map! {_ => cpsr},
        }
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
        self.reg[13] = &mut self.reg_mode_13_14[RegBank::from(mode)][0] as *mut u32;
        self.reg[14] = &mut self.reg_mode_13_14[RegBank::from(mode)][1] as *mut u32;
        self.cpsr.mode = mode;
    }
}

impl fmt::Display for Cpu {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "    Sys/User   FIQ    Supervis  Abort     IRQ    Undefined\n"
        )?;
        Ok(())
    }
    //    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    //        write!(
    //            f,
    //            "    Sys/User   FIQ    Supervis  Abort     IRQ    Undefined\n"
    //        )?;
    //        for i in 0..8 {
    //            write!(f, "R{}  {:08x}\n", i, self.r[i])?;
    //        }
    //        for i in 8..10 {
    //            write!(f, "R{}  {:08x} {:08x}\n", i, self.r[i], self.r_fiq[i - 8])?;
    //        }
    //        for i in 10..13 {
    //            write!(f, "R{} {:08x} {:08x}\n", i, self.r[i], self.r_fiq[i - 8])?;
    //        }
    //        for i in 13..15 {
    //            write!(
    //                f,
    //                "R{} {:08x} {:08x} {:08x} {:08x} {:08x} {:08x}\n",
    //                i,
    //                self.r[i],
    //                self.r_fiq[i - 8],
    //                self.r_svc[i - 13],
    //                self.r_abt[i - 13],
    //                self.r_irq[i - 13],
    //                self.r_und[i - 13]
    //            )?;
    //        }
    //        write!(f, "R{} {:08x}\n", 15, self.r[15])?;
    //        write!(f, "CPSR {:032b}\n", self.cpsr.status)?;
    //        write!(f, "SPSR {:032b}\n", self.cpsr.status)?;
    //        Ok(())
    //    }
}

// CPU Mode
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum Mode {
    OldUser = 0x00,
    OldFIQ = 0x01,
    OldIRQ = 0x02,
    OldSupervisor = 0x03,
    User = 0x10,
    FIQ = 0x11,
    IRQ = 0x12,
    Supervisor = 0x13,
    Abort = 0x17,
    Undefined = 0x1B,
    System = 0x1F,
}

#[derive(Debug, Enum)]
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

#[allow(dead_code)]
#[derive(Debug, PartialEq, Clone, Copy)]
// Current Program Status Register
pub struct Cpsr {
    status: u32,
    mode: Mode,
}
