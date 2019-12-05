use ttk91::{
    symbolic,
    bytecode,
    emulator::{Emulator, Memory, StdIo},
};

use std::env::args;

fn main() {
    let args: Vec<_> = args().collect();

    if args.len() == 1 ||
        args.iter().find(|arg| *arg == "--help").is_some() ||
        args.iter().find(|arg| *arg == "-h").is_some()
    {
        println!("ttk91run: Compile and run TTK91 programs");
        println!("");
        println!("Usage: ttk91run [--help] <program>");
        println!("");
        println!(" --help, -h  Display this help text.");
        println!("  <program>  The .b91 or .k91 program file.");
        return;
    }

    let file_path = args.iter().skip(1).find(|arg| *arg != "--help" && *arg != "-h")
        .unwrap();

    let file = std::fs::read_to_string(file_path).unwrap();
    let program;

    if file_path.ends_with(".k91") {
        let sym_prog = symbolic::Program::parse(&*file).unwrap();

        program = sym_prog.compile();
    } else {
        program = bytecode::Program::parse(&*file).unwrap();
    }

    let mut emulator = Emulator::new(program.to_words(), StdIo);
    emulator.run().unwrap();
}
