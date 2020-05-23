use ttk91::{
    bytecode,
    emulator::{Emulator, StdIo},
    symbolic,
};

use clap::{App, Arg, ArgMatches};
use slog::{o, Drain, Logger};
use slog_term::{FullFormat, TermDecorator};

enum Error {
    Parse,
    Execution,
    IO(std::io::Error),
}

impl<'a> From<ttk91::bytecode::parser::Error<'a>> for Error {
    fn from(_: ttk91::bytecode::parser::Error<'a>) -> Error {
        Error::Parse
    }
}

impl From<std::io::Error> for Error {
    fn from(e: std::io::Error) -> Error {
        Error::IO(e)
    }
}

impl<'a> From<ttk91::symbolic::parser::ParseError<'a>> for Error {
    fn from(_: ttk91::symbolic::parser::ParseError<'a>) -> Error {
        Error::Parse
    }
}

fn parse_arguments() -> ArgMatches<'static> {
    App::new("ttk91run")
        .version(env!("CARGO_PKG_VERSION"))
        .author("Mitja Karhusaari <mitja@karhusaari.me>")
        .about("Utility for compiling and executing TTK91 programs")
        .arg(
            Arg::with_name("source")
                .help("File containing assembly source or bytecode")
                .value_name("SOURCE")
                .required(true)
                .index(1),
        )
        .arg(
            Arg::with_name("verbose")
                .help("Enables verbose logging")
                .long("verbose")
                .short("v"),
        )
        .get_matches()
}

fn main() {
    let args = parse_arguments();

    let file_path = args.value_of("source").unwrap();

    let mut logger = None;

    if args.is_present("verbose") {
        let decorator = TermDecorator::new().build();
        let drain = FullFormat::new(decorator).build().fuse();
        let drain = slog_async::Async::new(drain).build().fuse();
        logger = Some(Logger::root(drain, o!()));
    }

    match run(file_path, logger) {
        Ok(()) => (),
        Err(Error::IO(io)) => eprintln!("IO error: {}", io),
        Err(Error::Execution) => eprintln!("Execution error"),
        Err(Error::Parse) => eprintln!("Parse error"),
    }
}

fn run(file_path: &str, logger: Option<Logger>) -> Result<(), Error> {
    let file = std::fs::read_to_string(file_path)?;
    let program;

    let is_symbolic = file_path.ends_with(".k91");

    if is_symbolic {
        let res = symbolic::Program::parse(&*file);

        if let Ok(prog) = res {
            program = ttk91::compiler::compile_with_logger(prog, logger.clone());
        } else {
            program = bytecode::Program::parse(&*file)?;
        }
    } else {
        let res = bytecode::Program::parse(&*file);

        if let Ok(prog) = res {
            program = prog;
        } else {
            let parsed = symbolic::Program::parse(&*file)?;
            program = ttk91::compiler::compile_with_logger(parsed, logger.clone());
        }
    }

    let mut emulator =
        Emulator::with_logger(program.to_words(), StdIo, logger).map_err(|_| Error::Execution)?;

    emulator.run().map_err(|_| Error::Execution)?;

    Ok(())
}
