# CPU

ARM7TDMI: 32-bit 16.78 MHz ARM (RISC) processor, implements the ARMv4T ISA.
- ARM7 processor
- **T**humb 16-bit compressed instruction set
- on-chip **D**ebug support
- enhanced 32-bit x 8 **M**ultiplier, with 64-bit result
- Embedded**I**CE hardware that supports on-chip breakpoints and watchpoints


Three stage pipeline:
- Fetch: fetch instruction from memory.
- Decode: decode instruction in the pipeline.
- Execute: one or more registers are read from register bank, shift and ALU
  operations occur, results are written to one or more registers.

# Sources

- http://www.kernelthread.com/publications/gbaunix/
- https://problemkaputt.de/gbatek.htm#armcpuoverview
- https://static.docs.arm.com/dvi0027/b/DVI_0027A_ARM7TDMI_PO.pdf
- https://static.docs.arm.com/ddi0029/g/DDI0029.pdf
