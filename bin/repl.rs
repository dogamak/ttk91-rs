use std::convert::TryFrom;
use std::io::Write;
use std::ops::RangeInclusive;
use std::str::FromStr;
use std::sync::{Arc, Mutex, PoisonError};

use clap::{App, Arg, ArgMatches};
use slog::{o, Discard, Drain, Logger};
use slog_term::{FullFormat, TermDecorator};

use ttk91::{
    emulator::{Emulator, Memory, StdIo},
    instruction::{Instruction as BytecodeInstruction, Register},
    symbol_table::{Label, SymbolTable, Value},
    symbolic::{
        parser::{ParseError, Parser},
        program::{validate_instruction, RelocationKind, Instruction as SymbolicInstruction},
    },
};

#[derive(Debug)]
enum MemoryOperation {
    Read,
    Write,
}

#[derive(Debug)]
enum MemoryError {
    InvalidAddress {
        address: u16,
    },
    OperationNotAllwed {
        address: u16,
        operation: MemoryOperation,
    },
    ConcurrencyError,
    InvalidInstruction,
}

impl<'a, T> From<PoisonError<T>> for MemoryError {
    fn from(_: PoisonError<T>) -> MemoryError {
        MemoryError::ConcurrencyError
    }
}

impl std::fmt::Display for MemoryError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            MemoryError::InvalidAddress { address } => {
                write!(f, "invalid address: 0x{:x}", address)
            }
            MemoryError::OperationNotAllwed { address, operation } => {
                let operation = match operation {
                    MemoryOperation::Read => "readable",
                    MemoryOperation::Write => "writable",
                };

                write!(f, "address 0x{:x} not {}", address, operation)
            }
            MemoryError::ConcurrencyError => write!(f, "concurrency error"),
            MemoryError::InvalidInstruction => write!(f, "invalid instruciton"),
        }
    }
}

#[derive(Clone)]
struct SharedMemory {
    instructions: Arc<Mutex<Vec<u32>>>,
    data: Arc<Mutex<Vec<i32>>>,
    stack: Arc<Mutex<Vec<i32>>>,
}

impl SharedMemory {
    fn new() -> SharedMemory {
        SharedMemory {
            instructions: Arc::new(Mutex::new(Vec::new())),
            data: Arc::new(Mutex::new(Vec::new())),
            stack: Arc::new(Mutex::new(vec![0; 16])),
        }
    }

    fn code_tail(&self) -> Result<u16, MemoryError> {
        let guard = self.instructions.lock()?;

        Ok((guard.len() as u16) | 0x8000)
    }

    fn push_instruction(&self, ins: BytecodeInstruction) -> Result<u16, MemoryError> {
        let mut guard = self.instructions.lock()?;

        guard.push(ins.into());

        let mut addr = (guard.len() - 1) as u16;
        addr |= 0x8000;

        Ok(addr)
    }

    fn push_data(&self, value: i32) -> Result<u16, MemoryError> {
        let mut guard = self
            .data
            .lock()
            .map_err(|_| MemoryError::ConcurrencyError)?;

        guard.push(value);

        Ok((guard.len() - 1) as u16)
    }
}

const STACK_BASE_ADDRESS: u16 = 0x7FFF;

impl Memory for SharedMemory {
    type Error = MemoryError;

    fn stack_address_range(&self) -> Result<RangeInclusive<u16>, Self::Error> {
        let size = self.stack.lock()?.len() as u16;
        Ok((STACK_BASE_ADDRESS - size)..=(STACK_BASE_ADDRESS))
    }

    fn grow_stack(&mut self, amount: u16) -> Result<(), Self::Error> {
        self.stack
            .lock()?
            .extend(std::iter::repeat(0).take(amount as usize));

        Ok(())
    }

    fn get_instruction(&mut self, addr: u16) -> Result<BytecodeInstruction, Self::Error> {
        if addr & 0x8000 == 0 {
            return Err(MemoryError::OperationNotAllwed {
                address: addr,
                operation: MemoryOperation::Read,
            });
        }

        let addr = addr & 0x7FFF;

        match self.instructions.lock() {
            Err(_) => Err(MemoryError::ConcurrencyError),
            Ok(guard) => match guard.get(addr as usize) {
                None => Err(MemoryError::InvalidAddress { address: addr }),
                Some(word) => match BytecodeInstruction::try_from(*word) {
                    Err(_) => Err(MemoryError::InvalidInstruction),
                    Ok(ins) => Ok(ins),
                },
            },
        }
    }

    fn get_data(&mut self, addr: u16) -> Result<i32, Self::Error> {
        if addr & 0x8000 != 0 {
            return Err(MemoryError::OperationNotAllwed {
                address: addr,
                operation: MemoryOperation::Read,
            });
        }

        let stack = self.stack_address_range()?;

        if stack.contains(&addr) {
            let address = stack.end() - (addr & 0x7FFF);
            let guard = self.stack.lock()?;
            guard
                .get(address as usize)
                .copied()
                .ok_or(MemoryError::InvalidAddress { address })
        } else {
            let address = addr & 0x7FFF;
            let guard = self.data.lock()?;
            guard
                .get(address as usize)
                .copied()
                .ok_or(MemoryError::InvalidAddress { address })
        }
    }

    fn set_data(&mut self, addr: u16, data: i32) -> Result<(), Self::Error> {
        if addr & 0x8000 != 0 {
            return Err(MemoryError::OperationNotAllwed {
                address: addr,
                operation: MemoryOperation::Write,
            });
        }

        let stack = self.stack_address_range()?;

        if stack.contains(&addr) {
            let addr = stack.end() - (addr & 0x7FFF);
            let mut guard = self.stack.lock()?;
            guard[addr as usize] = data;
        } else {
            let addr = addr & 0x7FFF;
            let mut guard = self.data.lock()?;
            println!("Addr: {}", addr);
            guard[addr as usize] = data;
        }

        Ok(())
    }
}

#[derive(Debug)]
enum CommandError {
    InvalidFormat,
}

impl ::std::fmt::Display for CommandError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            CommandError::InvalidFormat => write!(f, "invalid format"),
        }
    }
}

#[derive(Debug)]
enum Error<'a> {
    MemoryError(MemoryError),
    CommandError(CommandError),
    ParseError(ParseError<'a>),
    UnknownSymbol(String),
}

impl<'a> ::std::fmt::Display for Error<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Error::CommandError(ce) => write!(f, "command error: {}", ce),
            Error::MemoryError(me) => write!(f, "memory error: {}", me),
            Error::ParseError(e) => write!(f, "parse error: {}", e),
            Error::UnknownSymbol(sym) => write!(f, "unknown symbol: {}", sym),
        }
    }
}

impl<'a> From<MemoryError> for Error<'a> {
    fn from(me: MemoryError) -> Error<'a> {
        Error::MemoryError(me)
    }
}

impl<'a> From<ParseError<'a>> for Error<'a> {
    fn from(e: ParseError<'a>) -> Error<'a> {
        Error::ParseError(e)
    }
}

impl<'a> From<CommandError> for Error<'a> {
    fn from(ce: CommandError) -> Error<'a> {
        Error::CommandError(ce)
    }
}

struct REPL {
    memory: SharedMemory,
    symbol_table: SymbolTable,
    emulator: Emulator<SharedMemory, StdIo>,
    logger: Logger,
}

impl REPL {
    fn new() -> Result<REPL, MemoryError> {
        let memory = SharedMemory::new();

        let mut symbol_table = SymbolTable::new();

        let crt = symbol_table.get_or_create("CRT".into());
        let crt = symbol_table.symbol_mut(crt);
        crt.set::<Value>(Some(0));
        crt.set::<Label>(Some("CRT".into()));

        let crt = symbol_table.get_or_create("HALT".into());
        let crt = symbol_table.symbol_mut(crt);
        crt.set::<Value>(Some(11));
        crt.set::<Label>(Some("HALT".into()));

        let mut emulator = Emulator::new(memory.clone(), StdIo)?;
        emulator.context.pc = 0x8000;

        Ok(REPL {
            memory,
            symbol_table,
            emulator,
            logger: Logger::root(Discard, o!()),
        })
    }

    fn set_logger(&mut self, logger: Logger) {
        self.logger = logger.clone();
        self.emulator.set_logger(logger);
    }

    fn handle_command<'a>(&mut self, command: &'a str) -> Result<(), Error<'a>> {
        let command = &command[..command.len() - 1];

        let cmd = command
            .split(char::is_whitespace)
            .next()
            .ok_or(CommandError::InvalidFormat)?;

        let rest = command[cmd.len()..].trim();
        let args: Vec<_> = rest.split(char::is_whitespace).collect();

        match (cmd, args.as_slice()) {
            ("help", _) => {
                println!("Available commands:");
                println!("  .symbols                             List all symbols and their values and addresses");
                println!("  .s <symbol>, .symbol <symbol>        Print the address and value of a symbol");
                println!(
                    "  .regs, .registers                    List all registers and their values"
                );
                println!("  .pi <ins>, .print_instruction <ins>  Print the parsed instruction");
            }
            ("s", [symbol]) | ("symbol", [symbol]) => {
                let addr = self
                    .symbol_table
                    .symbol_by_label(symbol)
                    .and_then(|sym| sym.get::<Value>().into_owned())
                    .ok_or(Error::UnknownSymbol(symbol.to_string()))?;

                let value = self.memory.get_data(addr as u16)?;

                println!("Symbol '{}' @ {:x} = {}", symbol, addr, value);
            }
            ("symbols", _) => {
                for symbol in self.symbol_table.iter() {
                    let addr = symbol.get::<Value>().into_owned();

                    if let Some(addr) = addr {
                        let label = symbol
                            .get::<Label>()
                            .into_owned()
                            .unwrap_or("<UNKNOWN>".to_string());

                        let value = match self.memory.get_data(addr as u16) {
                            Ok(value) => value.to_string(),
                            Err(_) => "#ERROR#".to_string(),
                        };

                        println!("Symbol '{}' @ {:x} = {}", label, addr, value);
                    }
                }
            }
            ("regs", _) | ("registers", _) => {
                for i in 0..8 {
                    println!("Register R{} = {}", i, self.emulator.context.r[i]);
                }
            }
            ("reg", [register]) | ("register", [register]) => {
                let register = match Register::from_str(register) {
                    Ok(register) => register,
                    Err(_err) => {
                        println!("Invalid register {}", register);
                        return Ok(());
                    }
                };

                let value = self.emulator.context.r[register.index() as usize];

                println!("Register {} = {}", register, value);
            }
            ("print_instruction", _) | ("pi", _) => {
                let ins = Parser::parse_instruction(rest)?;
                let ins = validate_instruction(ins)?;

                match ins {
                    SymbolicInstruction::Pseudo(ins) => {
                        println!("{:?}", SymbolicInstruction::Pseudo(ins));
                    }
                    SymbolicInstruction::Real(sins) => {
                        let mut ins: BytecodeInstruction = sins.clone().into();

                        match sins.relocation_symbol() {
                            None => {}
                            Some(entry) => {
                                let addr = self
                                    .symbol_table
                                    .symbol(entry.symbol)
                                    .get::<Value>()
                                    .into_owned();

                                if let Some(addr) = addr {
                                    let imm = match entry.kind {
                                        RelocationKind::Address => addr,
                                        RelocationKind::Value => {
                                            self.memory.get_data(addr as u16)?
                                        }
                                    };

                                    ins.immediate = imm as u16;
                                } else {
                                    println!("NOTE: Unknown symbol");
                                }
                            }
                        }

                        println!("{:?}", ins);
                    }
                }
            }
            _ => (),
        }

        Ok(())
    }

    fn run(&mut self) {
        println!("Type .help for a list of all available commands or start typing instruciton");

        loop {
            print!(
                "0x{:x}> ",
                (self.memory.instructions.lock().unwrap().len() as u16) | 0x8000
            );
            let _ = ::std::io::stdout().flush();

            let mut input = String::new();
            let _ = ::std::io::stdin().read_line(&mut input);

            match self.handle_line(&input) {
                Ok(()) => {}
                Err(err) => {
                    if let Error::ParseError(err) = err {
                        eprintln!("Error: {}", err);
                    } else {
                        eprintln!("Error: {}", err);
                    }
                }
            }
        }
    }

    fn handle_line<'a>(&mut self, input: &'a str) -> Result<(), Error<'a>> {
        if input.chars().next() == Some('.') {
            self.handle_command(&input[1..])?;
            return Ok(());
        }

        let (label, ins) = Parser::from_str(&input[..input.len() - 1])
            .with_symbol_table(&mut self.symbol_table)
            .parse_line()?;

        let ins = validate_instruction(ins)?;

        match ins {
            SymbolicInstruction::Pseudo(ins) => {
                let addr = self.memory.push_data(ins.value)?;

                if let Some(symbol) = label {
                    let symbol = self.symbol_table.symbol_mut(symbol);
                    symbol.set::<Value>(Some(addr as i32));
                    let label = symbol
                        .get::<Label>()
                        .into_owned()
                        .unwrap_or("UNKNOWN".into());
                    println!("Symbol {} at address {}", label, addr);
                }
            }
            SymbolicInstruction::Real(sins) => {
                let mut ins: BytecodeInstruction = sins.clone().into();

                match sins.relocation_symbol() {
                    None => {}
                    Some(entry) => {
                        let symbol = self
                            .symbol_table
                            .symbol(entry.symbol);

                        let label = symbol.get::<Label>().into_owned().unwrap_or_default();
                        
                        let addr = symbol.get::<Value>()
                            .ok_or(Error::UnknownSymbol(label))?;

                        let imm = match entry.kind {
                            RelocationKind::Address => addr as u16,
                            RelocationKind::Value => self.memory.get_data(addr as u16)? as u16,
                        };

                        ins.immediate = imm;
                    }
                }

                let addr = self.memory.push_instruction(ins.clone())?;

                if let Some(symbol) = label {
                    let symbol = self.symbol_table.symbol_mut(symbol);
                    symbol.set::<Value>(Some(addr as i32));
                    let label = symbol
                        .get::<Label>()
                        .into_owned()
                        .unwrap_or("UNKNOWN".into());
                    println!("Symbol {} at address {}", label, addr);
                }

                while self.emulator.context.pc < self.memory.code_tail()? {
                    let ins = self.memory.get_instruction(self.emulator.context.pc)?;
                    self.emulator.context.pc += 1;

                    self.emulator.emulate_instruction(&ins)?;
                }
            }
        }

        Ok(())
    }
}

fn parse_args() -> ArgMatches<'static> {
    App::new("ttk91repl")
        .version(env!("CARGO_PKG_VERSION"))
        .author("Mitja Karhusaari <mitja@karhusaari>")
        .about("Read-Evaluate-Print-Loop utility for TTK91")
        .arg(
            Arg::with_name("verbose")
                .help("Enables verbose logging")
                .long("verbose")
                .short("v"),
        )
        .get_matches()
}

fn main() {
    let args = parse_args();

    let mut repl = REPL::new().unwrap();

    if args.is_present("verbose") {
        let decorator = TermDecorator::new().build();
        let drain = FullFormat::new(decorator).build().fuse();
        let drain = slog_async::Async::new(drain).build().fuse();
        repl.set_logger(Logger::root(drain, o!()));
    }

    repl.run();
}
