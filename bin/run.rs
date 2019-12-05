use ttk91::{
    symbolic,
    bytecode,
    emulator::{Emulator, Memory, StdIo},
};

use std::env::args;

enum Error {
    Parse,
    Execution,
    IO(std::io::Error),
    Argument,
}

impl From<std::io::Error> for Error {
    fn from(e: std::io::Error) -> Error {
        Error::IO(e)
    }
}

impl<T> From<nom::Err<T>> for Error {
    fn from(e: nom::Err<T>) -> Error {
        Error::Parse
    }
}

fn print_usage() {
    println!("ttk91run: Compile and run TTK91 programs");
    println!("");
    println!("Usage: ttk91run [--help] <program>");
    println!("");
    println!(" --help, -h  Display this help text.");
    println!("  <program>  The .b91 or .k91 program file.");
}

fn main() {
    let args: Vec<_> = args().collect();

    if args.len() == 1 ||
        args.iter().find(|arg| *arg == "--help").is_some() ||
        args.iter().find(|arg| *arg == "-h").is_some()
    {
        print_usage();
        return;
    }

    let file_path = args.iter().skip(1).find(|arg| *arg != "--help" && *arg != "-h")
        .unwrap();

    match run(file_path) {
        Ok(()) => (),
        Err(Error::IO(io)) => eprintln!("IO error: {}", io),
        Err(Error::Execution) => eprintln!("Execution error"),
        Err(Error::Argument) => print_usage(),
        Err(Error::Parse) => eprintln!("Parse error"),
    }
}

fn run(file_path: &str) -> Result<(), Error> {
    let file = std::fs::read_to_string(file_path)?;
    let program;

    if file_path.ends_with(".k91") {
        let sym_prog = symbolic::Program::parse(&*file)?;

        program = sym_prog.compile();
    } else {
        program = bytecode::Program::parse(&*file)?;
    }

    let mut emulator = Emulator::new(program.to_words(), StdIo);

    emulator.run()
        .map_err(|_| Error::Execution)?;

    Ok(())
}
