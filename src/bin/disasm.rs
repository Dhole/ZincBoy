#[macro_use]
extern crate arrayref;

use std::env;
use std::fs::File;
use std::io;
use std::io::Read;

use zincboy::ARM7TDMI::op_raw::OpRaw;

fn main() -> Result<(), io::Error> {
    let filename = env::args().nth(1).unwrap();
    println!("Filename: {}", filename);
    let mut file = File::open(filename)?;
    let mut data = Vec::new();
    file.read_to_end(&mut data)?;
    let mut i = 0;
    loop {
        if i + 4 >= data.len() {
            break;
        }
        let word = u32::from_le_bytes(*array_ref![data, i, 4]);
        let op = OpRaw::new(word);
        println!("{:08x}: {:08x} {:?}", i, word.to_be(), op.to_op());
        i += 4;
    }
    Ok(())
}
