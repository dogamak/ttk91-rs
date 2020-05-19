use ttk91::{
    bytecode,
    symbolic,
    emulator::{Emulator, StdIo, TestIo, Memory, BalloonMemory},
    instruction::{Mode, OpCode, Instruction, Register},
};

use slog::{Logger, Discard, Drain, o};
use slog_term::{TermDecorator, FullFormat, CompactFormat};

fn compile_program() -> bytecode::Program {
    let source_code = include_str!("procb.k91");

    let program = symbolic::Program::parse(source_code)
        .expect("could not parse the source code");

    println!("{:?}", program);

    program.compile()
}

#[test]
fn test_procb() {
    let program = compile_program();

    let decorator = TermDecorator::new().build();
    let drain = FullFormat::new(decorator).build().fuse();
    let drain = slog_async::Async::new(drain).build().fuse();
    let logger = Logger::root(drain, o!());

    let mut io = TestIo::new();
    let mut memory = BalloonMemory::new(program);
    let mut emulator = Emulator::with_logger(memory, &mut io, logger)
        .expect("could not initialize the emulator");

    while !emulator.halted {
        println!("{:?}", emulator.get_current_instruction());
        emulator.step();
    }
}
