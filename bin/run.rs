use ttk91::{
    symbolic,
    bytecode,
    error::ParseError,
    emulator::{Emulator, Memory, StdIo},
};
use std::env::args;

use clap::{App, Arg, ArgMatches};

enum Error {
    Parse,
    Execution,
    IO(std::io::Error),
}

impl From<std::io::Error> for Error {
    fn from(e: std::io::Error) -> Error {
        Error::IO(e)
    }
}

impl<K> From<ParseError<K>> for Error {
    fn from(e: ParseError<K>) -> Error {
        Error::Parse
    }
}

fn parse_arguments() -> ArgMatches<'static> {
    App::new("ttk91run")
        .version(env!("CARGO_PKG_VERSION"))
        .author("Mitja Karhusaari <mitja@karhusaari.me>")
        .about("Utility for compiling and executing TTK91 programs")
        .arg(Arg::with_name("source")
             .help("File containing assemby source or bytecode")
             .value_name("SOURCE")
             .required(true)
             .index(1))
        .get_matches()
}

fn main() {
    let args = parse_arguments();

    let file_path = args.value_of("source").unwrap();

    match run(file_path) {
        Ok(()) => (),
        Err(Error::IO(io)) => eprintln!("IO error: {}", io),
        Err(Error::Execution) => eprintln!("Execution error"),
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
