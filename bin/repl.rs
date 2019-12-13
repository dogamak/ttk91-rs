use std::sync::{Arc, RwLock, Mutex, MutexGuard, PoisonError};
use std::rc::Rc;
use std::convert::TryFrom;
use std::collections::HashMap;
use std::io::Write;
use std::str::FromStr;
use std::ops::RangeInclusive;

use clap::{App, ArgMatches, Arg};
use slog::{Drain, Logger, Discard, o};
use slog_term::{TermDecorator, FullFormat};

use ttk91::{
    emulator::{Memory, InputOutput, Emulator, StdIo},
    instruction::{Instruction, Register},
    symbolic::{
        parser::{
            ParseError,
            parse_line,
        },
        program::{
            SymbolicInstruction,
            RelocationKind,
        }
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

impl<'a,T> From<PoisonError<T>> for MemoryError {
    fn from(e: PoisonError<T>) -> MemoryError {
        MemoryError::ConcurrencyError
    }
}

impl std::fmt::Display for MemoryError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            MemoryError::InvalidAddress { address } =>
                write!(f, "invalid address: 0x{:x}", address),
            MemoryError::OperationNotAllwed { address, operation } => {
                let operation = match operation {
                    MemoryOperation::Read => "readable",
                    MemoryOperation::Write => "writable",
                };

                write!(f, "address 0x{:x} not {}", address, operation)
            },
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

    fn push_instruction(&self, ins: Instruction) -> Result<u16, MemoryError> {
        let mut guard = self.instructions.lock()?;

        guard.push(ins.into());

        let mut addr = (guard.len()-1) as u16;
        addr |= 0x8000;

        Ok(addr)
    }

    fn push_data(&self, value: i32) -> Result<u16, MemoryError> {
        let mut guard = self.data.lock()
            .map_err(|_| MemoryError::ConcurrencyError)?;

        guard.push(value);

        Ok((guard.len()-1) as u16)
    }
}

const STACK_BASE_ADDRESS: u16 = 0x7FFF;

impl Memory for SharedMemory {
    type Error = MemoryError;

    fn stack_address_range(&self) -> Result<RangeInclusive<u16>, Self::Error> {
        let size = self.stack.lock()?.len() as u16;
        Ok((STACK_BASE_ADDRESS-size)..=(STACK_BASE_ADDRESS))
    }

    fn grow_stack(&mut self, amount: u16) -> Result<(), Self::Error> {
        self.stack.lock()?
            .extend(std::iter::repeat(0).take(amount as usize));

        Ok(())
    }

    fn get_instruction(&mut self, addr: u16) -> Result<Instruction, Self::Error> {
        if addr & 0x8000 == 0 {
            return Err(MemoryError::OperationNotAllwed {
                address: addr,
                operation: MemoryOperation::Read,
            });
        }

        let addr = addr & 0x7FFF;

        match self.instructions.lock() {
            Err(e) => Err(MemoryError::ConcurrencyError),
            Ok(guard) => {
                match guard.get(addr as usize) {
                    None => Err(MemoryError::InvalidAddress { address: addr }),
                    Some(word) => {
                        match Instruction::try_from(*word) {
                            Err(e) => Err(MemoryError::InvalidInstruction),
                            Ok(ins) => Ok(ins),
                        }
                    },
                }
            },
        }
    }

    fn get_data(&mut self, addr: u16) -> Result<u16, Self::Error> {
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
            guard.get(address as usize)
                .map(|w| *w as u16)
                .ok_or(MemoryError::InvalidAddress { address })
        } else {
            let address = addr & 0x7FFF;
            let guard = self.data.lock()?;
            guard.get(address as usize)
                .map(|w| *w as u16)
                .ok_or(MemoryError::InvalidAddress { address })
        }
    }

    fn set_data(&mut self, addr: u16, data: u16) -> Result<(), Self::Error> {
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
            guard[addr as usize] = data as i32;
        } else {
            let addr = addr & 0x7FFF;
            let mut guard = self.data.lock()?;
            println!("Addr: {}", addr);
            guard[addr as usize] = data as i32;
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
enum Error {
    MemoryError(MemoryError),
    CommandError(CommandError),
    ParseError(ParseError),
    Incomplete,
    UnknownSymbol(String),
}

impl ::std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Error::CommandError(ce) => write!(f, "command error: {}", ce),
            Error::MemoryError(me) => write!(f, "memory error: {}", me),
            Error::ParseError(e) => write!(f, "parse error: {}", e),
            Error::Incomplete => write!(f, "incomplete input"),
            Error::UnknownSymbol(sym) => write!(f, "unknown symbol: {}", sym),
        }
    }
}

impl From<MemoryError> for Error {
    fn from(me: MemoryError) -> Error {
        Error::MemoryError(me)
    }
}

impl From<ParseError> for Error {
    fn from(e: ParseError) -> Error {
        Error::ParseError(e)
    }
}

impl From<CommandError> for Error {
    fn from(ce: CommandError) -> Error {
        Error::CommandError(ce)
    }
}

struct REPL {
    memory: SharedMemory,
    symbol_table: HashMap<String, u16>,
    emulator: Emulator<SharedMemory, StdIo>,
    logger: Logger,
}

impl REPL {
    fn new() -> Result<REPL, MemoryError> {
        let memory = SharedMemory::new();

        let mut symbol_table = HashMap::new();

        symbol_table.insert("CRT".into(), 0);
        symbol_table.insert("HALT".into(), 11);

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

    fn handle_command(&mut self, command: &str) -> Result<(), Error> {
        let command = &command[..command.len()-1];

        let args: Vec<_> = command
            .split(char::is_whitespace)
            .collect();

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
                println!("  .regs, .registers                    List all registers and their values");
                println!("  .pi <ins>, .print_instruction <ins>  Print the parsed instruction");
            },
            ("s", [symbol]) | ("symbol", [symbol]) => {
                let addr = self.symbol_table.get(&symbol.to_string())
                    .ok_or(Error::UnknownSymbol(symbol.to_string()))?;

                let value = self.memory.get_data(*addr as u16)?;

                println!("Symbol '{}' @ {:x} = {}", symbol, addr, value);
            },
            ("symbols", _) => {
                for (symbol, addr) in &self.symbol_table {
                    let value = match self.memory.get_data(*addr as u16) {
                        Ok(value) => value,
                        Err(_) => continue,
                    };

                    println!("Symbol '{}' @ {:x} = {}", symbol, addr, value);
                }
            },
            ("regs", _) | ("registers", _) => {
                for i in 0..8 {
                    println!("Register R{} = {}", i, self.emulator.context.r[i]);
                }
            },
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
            },
            ("print_instruction", _) | ("pi", _) => {
                let ins = match parse_line(rest)? {
                    None => return Ok(()),
                    Some((_, ins)) => ins,
                };

                match ins {
                    SymbolicInstruction::Pseudo(ins) => {
                        println!("{:?}", SymbolicInstruction::Pseudo(ins));
                    },
                    SymbolicInstruction::Concrete(sins) => {
                        let mut ins: Instruction = sins.clone().into();

                        match sins.relocation_symbol() {
                            None => {},
                            Some(entry) => {
                                if let Some(addr) = self.symbol_table.get(&entry.symbol) {
                                    let imm = match entry.kind {
                                        RelocationKind::Address => *addr as u16,
                                        RelocationKind::Value => self.memory.get_data(*addr as u16)?,
                                    };

                                    ins.immediate = imm;
                                } else {
                                    println!("NOTE: Unknown symbol");
                                }
                            },
                        }

                        println!("{:?}", ins);
                    },
                }
            },
            _ => (),
        }
        
        Ok(())
    }

    fn run(&mut self) {
        println!("Type .help for a list of all available commands or start typing instruciton");

        loop {
            print!("0x{:x}> ", (self.memory.instructions.lock().unwrap().len() as u16) | 0x8000);
            ::std::io::stdout().flush();
            
            let mut input = String::new();
            ::std::io::stdin().read_line(&mut input);

            match self.handle_line(&input) {
                Ok(()) => {},
                Err(err) => {
                    if let Error::ParseError(err) = err {
                        eprintln!("Error: {}", err.verbose(&input));
                    } else {
                        eprintln!("Error: {}", err);
                    }
                },
            }
        }
    }

    fn handle_line(&mut self, input: &str) -> Result<(), Error> {
        if input.chars().next() == Some('.') {
            self.handle_command(&input[1..])?;
            return Ok(());
        }

        let (label, ins) = match parse_line(&input[..input.len()-1])? {
            None => return Ok(()),
            Some((label, ins)) => (label, ins),
        };

        match ins {
            SymbolicInstruction::Pseudo(ins) => {
                let addr = self.memory.push_data(ins.value)?;

                if let Some(label) = label {
                    self.symbol_table.insert(label.to_string(), addr);
                    println!("Symbol {} at address {}", label, addr);
                }
            },
            SymbolicInstruction::Concrete(sins) => {
                let mut ins: Instruction = sins.clone().into();

                match sins.relocation_symbol() {
                    None => {},
                    Some(entry) => {
                        let addr = self.symbol_table.get(&entry.symbol)
                            .ok_or(Error::UnknownSymbol(entry.symbol))?;

                        let imm = match entry.kind {
                            RelocationKind::Address => *addr as u16,
                            RelocationKind::Value => self.memory.get_data(*addr as u16)?,
                        };

                        ins.immediate = imm;
                    },
                }

                let _addr = self.memory.push_instruction(ins.clone())?;

                while self.emulator.context.pc < self.memory.code_tail()?  {
                    let ins = self.memory.get_instruction(self.emulator.context.pc)?;
                    self.emulator.context.pc += 1;

                    self.emulator.emulate_instruction(&ins)?;
                }
            },
        }

        Ok(())
    }
}

fn parse_args() -> ArgMatches<'static> {
    App::new("ttk91repl")
        .version(env!("CARGO_PKG_VERSION"))
        .author("Mitja Karhusaari <mitja@karhusaari>")
        .about("Read-Evaluate-Print-Loop utility for TTK91")
        .arg(Arg::with_name("verbose")
             .help("Enables verbose logging")
             .long("verbose")
             .short("v"))
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
