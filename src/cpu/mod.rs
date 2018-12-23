// ARM7TDMI
pub struct Cpu {
    R: [u32; 16],
    R_fiq: [u32; 7],
    R_svc: [u32; 7],
    R_abt: [u32; 2],
    R_irq: [u32; 2],
    R_und: [u32; 2],
    cpsr: cpsr,
}

// CPU Mode
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

// Current Program Status Register
pub struct cpsr {
    Status: u32,
    Mode: Mode,
}
