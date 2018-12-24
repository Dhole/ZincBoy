use std::fmt;

#[allow(dead_code)]
#[derive(Debug, PartialEq)]
// ARM7TDMI
pub struct Cpu {
    r: [u32; 16],
    r_usr: [u32; 7],
    r_fiq: [u32; 7],
    r_svc: [u32; 2],
    r_abt: [u32; 2],
    r_irq: [u32; 2],
    r_und: [u32; 2],
    cpsr: Cpsr,
    spsr_fiq: Cpsr,
    spsr_svc: Cpsr,
    spsr_abt: Cpsr,
    spsr_irq: Cpsr,
    spsr_und: Cpsr,
}

pub struct Registers {}

#[allow(dead_code)]
impl Cpu {
    pub fn new() -> Self {
        let cpsr = Cpsr {
            status: 0,
            mode: Mode::User,
        };
        Cpu {
            r: [0; 16],
            r_usr: [0; 7],
            r_fiq: [0; 7],
            r_svc: [0; 2],
            r_abt: [0; 2],
            r_irq: [0; 2],
            r_und: [0; 2],
            cpsr: cpsr.clone(),
            spsr_fiq: cpsr.clone(),
            spsr_svc: cpsr.clone(),
            spsr_abt: cpsr.clone(),
            spsr_irq: cpsr.clone(),
            spsr_und: cpsr.clone(),
        }
    }

    fn set_mode(&mut self, mode: Mode) {
        if mode == self.cpsr.mode {
            return;
        }
        // Leaving FIQ mode
        if self.cpsr.mode == Mode::FIQ {
            self.r_fiq[0] = self.r[8];
            self.r_fiq[1] = self.r[9];
            self.r_fiq[2] = self.r[10];
            self.r_fiq[4] = self.r[11];
            self.r_fiq[5] = self.r[12];

            self.r[8] = self.r_usr[0];
            self.r[9] = self.r_usr[1];
            self.r[10] = self.r_usr[2];
            self.r[11] = self.r_usr[3];
            self.r[12] = self.r_usr[4];
        }
        // TODO: Save old registers
        match mode {
            Mode::User => {
                self.r[13] = self.r_usr[5];
                self.r[14] = self.r_usr[6];
            }
            Mode::FIQ => {
                self.r[8] = self.r_fiq[0];
                self.r[9] = self.r_fiq[1];
                self.r[10] = self.r_fiq[2];
                self.r[11] = self.r_fiq[3];
                self.r[12] = self.r_fiq[4];
                self.r[13] = self.r_fiq[5];
                self.r[14] = self.r_fiq[6];
            }
            Mode::Supervisor => {
                self.r[13] = self.r_svc[0];
                self.r[14] = self.r_svc[1];
            }
            Mode::Abort => {
                self.r[13] = self.r_abt[0];
                self.r[14] = self.r_abt[1];
            }
            Mode::Undefined => {
                self.r[13] = self.r_und[0];
                self.r[14] = self.r_und[1];
            }
            Mode::System => {
                self.r[13] = self.r_usr[5];
                self.r[14] = self.r_usr[6];
            }
            m => panic!(format!("Mode {:?} not implemented", m)),
        }
        self.cpsr.mode = mode;
    }
}

impl fmt::Display for Cpu {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "    Sys/User   FIQ    Supervis  Abort     IRQ    Undefined\n"
        )?;
        for i in 0..8 {
            write!(f, "R{}  {:08x}\n", i, self.r[i])?;
        }
        for i in 8..10 {
            write!(f, "R{}  {:08x} {:08x}\n", i, self.r[i], self.r_fiq[i - 8])?;
        }
        for i in 10..13 {
            write!(f, "R{} {:08x} {:08x}\n", i, self.r[i], self.r_fiq[i - 8])?;
        }
        for i in 13..15 {
            write!(
                f,
                "R{} {:08x} {:08x} {:08x} {:08x} {:08x} {:08x}\n",
                i,
                self.r[i],
                self.r_fiq[i - 8],
                self.r_svc[i - 13],
                self.r_abt[i - 13],
                self.r_irq[i - 13],
                self.r_und[i - 13]
            )?;
        }
        write!(f, "R{} {:08x}\n", 15, self.r[15])?;
        write!(f, "CPSR {:032b}\n", self.cpsr.status)?;
        write!(f, "SPSR {:032b}\n", self.cpsr.status)?;
        Ok(())
    }
}

// CPU Mode
#[derive(Debug, PartialEq, Clone)]
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

#[allow(dead_code)]
#[derive(Debug, PartialEq, Clone)]
// Current Program Status Register
pub struct Cpsr {
    status: u32,
    mode: Mode,
}
