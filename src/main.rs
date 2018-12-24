#[allow(unused_imports)]
use zincboy::ARM7TDMI;

fn main() {
    let cpu = ARM7TDMI::Cpu::new();
    print!("{}", cpu);
}
