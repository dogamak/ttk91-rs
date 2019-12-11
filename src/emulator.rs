//! [Emulator] for executing [bytecode programs](crate::bytecode::program::Program).

use std::convert::TryInto;
use std::cmp::Ordering;
use std::io::Read;

use crate::instruction::{Instruction, OpCode, Mode, JumpCondition, Register};

/// Contains the execution environment of the TTK91 processor.
#[derive(Debug, Clone, Default)]
pub struct Context {
    /// The Program Counter stores the address of the next instruction to be executed.
    pub pc: u16,

    /// Array containing values for all the eight work registers.
    pub r: [u16; 8],

    /// The comparison result flags stored in the State register.
    pub flags: Flags,
}

/// Represents the State register.
///
/// Holds the results of the latest COMP instruction.
/// Used to determine if JEQU, JLES, JGRE, JNEQU, JNLES and JNGRE instructions
/// result in a jump.
#[derive(Debug, Clone, Default)]
pub struct Flags {
    greater: bool,
    equal: bool,
    less: bool,
}

impl Flags {
    /// Clears all flags.
    fn zero(&mut self) {
        self.greater = false;
        self.equal = false;
        self.less = false;
    }

    fn as_word(&self) -> i32 {
        let mut word = 0;

        if self.greater {
            word |= 1 << 0;
        }

        if self.equal {
            word |= 1 << 1;
        }

        if self.less {
            word |= 1 << 2;
        }

        word
    }

    fn from_word(&mut self, word: i32) {
        if word & (1 << 0) != 0 {
            self.greater = true;
        }

        if word & (1 << 1) != 0 {
            self.equal = true;
        }

        if word & (1 << 2) != 0 {
            self.less = true;
        }
    }
}

/// Interface to the input and output devices as well as the supervisor.
pub trait InputOutput {
    /// Called when an IN instruction is executed.
    ///
    /// # Parameters
    /// - `device`: The device number specified in the address part of the instruction.
    ///
    /// # Returns
    /// A value received from the peripheral device or the user.
    fn input(&mut self, device: u16) -> u16;

    /// Called when an OUT instruciton is executed.
    ///
    /// # Parameters
    /// - `device`: The device number specified in the address part of the instruction.
    /// - `data`: The value of the register specified in the instruction.
    fn output(&mut self, device: u16, data: u16);

    /// Called when an SVC instruction is executed.
    ///
    /// # Parameters
    /// - `code`: The supervisor call code specified in the address part of the instruction.
    fn supervisor_call(&mut self, code: u16);
}

/// Trait for implementing the memory for a TTK91 processor.
pub trait Memory {
    /// Error type returned by all methods of this trait.
    type Error;

    /// Fetch the instruction from the specified address.
    ///
    /// # Parameters
    /// - `addr`: The address of the instruction.
    ///
    /// # Returns
    /// The instruction fetched from `addr` or a memory error.
    fn get_instruction(&mut self, addr: u16) -> Result<Instruction, Self::Error>;

    /// Fetch the data word from the specified address.
    ///
    /// # Parameters
    /// - `addr`: The address of the data word.
    ///
    /// # Returns
    /// The data word from address `addr` or a memory error.
    fn get_data(&mut self, addr: u16) -> Result<u16, Self::Error>;

    /// Overwrite the data word in the specified address.
    ///
    /// # Parameters
    /// - `addr`: The address of the data word.
    /// - `data`: The data word to be written to the location specified by `addr`.
    ///
    /// # Returns
    /// A memory error if the operation cannot be performed.
    fn set_data(&mut self, addr: u16, data: u16) -> Result<(), Self::Error>;

    fn stack_address_range(&self) -> Result<std::ops::RangeInclusive<u16>, Self::Error>;

    fn grow_stack(&mut self, amount: u16) -> Result<(), Self::Error>;
}

impl Memory for Vec<u32> {
    type Error = ();

    fn get_instruction(&mut self, addr: u16) -> Result<Instruction, ()> {
        self[addr as usize].try_into()
    }

    fn get_data(&mut self, addr: u16) -> Result<u16, Self::Error> {
        self.get(addr as usize)
            .map(|x| *x as u16)
            .ok_or(())
    }

    fn set_data(&mut self, addr: u16, data: u16) -> Result<(), ()> {
        self[addr as usize] = data as u32;
        Ok(())
    }

    fn grow_stack(&mut self, _amount: u16) -> Result<(), Self::Error> {
        panic!("Vec<u32> doesn't support growing as a memory")
    }

    fn stack_address_range(&self) -> Result<std::ops::RangeInclusive<u16>, Self::Error> {
        Ok(1..=0)
    }
}

/// Utility struct for implementing methods in the context of emulating a single instruction.
struct InstructionEmulationContext<'e, 'i, M, IO> {
    /// The emulator in whose context the instruction is being emulated.
    emulator: &'e mut Emulator<M, IO>,

    /// The instruction that we are currently emulating.
    instruction: &'i Instruction,
}

impl<'e,'i,M,IO> InstructionEmulationContext<'e, 'i, M, IO>
    where M: Memory,
          IO: InputOutput,
{
    /// Returns value of the first operand.
    fn first_operand(&self) -> u16 {
        self.emulator.context.r[self.instruction.register.index() as usize]
    }

    /// Sets the value of the first operand.
    fn set_first_operand(&mut self, value: u16) {
        self.emulator.context.r[self.instruction.register.index() as usize] = value;
    }

    /// Resolves the second operand and returns it's value.
    fn second_operand(&mut self) -> Result<u16, M::Error> {
        if self.instruction.immediate == 0 && self.instruction.index_register != Register::R0 {
            return Ok(self.emulator.context.r[self.instruction.index_register.index() as usize]);
        }

        let indirection = match self.instruction.mode {
            Mode::Immediate => 0,
            Mode::Direct => 1,
            Mode::Indirect => 2,
        };

        let mut value = self.instruction.immediate;

        if self.instruction.index_register != Register::R0 {
            value += self.emulator.context.r[self.instruction.index_register.index() as usize];
        }

        for _ in 0..indirection {
            value = self.emulator.memory.get_data(value)?;
        }

        Ok(value)
    }

    fn set_second_operand(&mut self, value: i32) -> Result<(), M::Error> {
        use Mode::*;
        use Register::*;

        match (self.instruction.mode, self.instruction.immediate, self.instruction.index_register) {
            (Mode::Immediate, _, _) => panic!("No such thing as a store to an immediate value!"),
            (Mode::Direct, 0, reg) if reg != R0 => {
                self.emulator.context.r[reg.index()] = value as u16;
            },
            (Mode::Indirect, 0, reg) if reg != R0 => {
                let addr = self.emulator.context.r[reg.index()];
                self.emulator.memory.set_data(addr, value as u16)?;
            },
            (Mode::Direct, mut addr, reg) => {
                if reg != R0 {
                    addr += self.emulator.context.r[reg.index()];
                }

                self.emulator.memory.set_data(addr, value as u16)?;
            },
            (Mode::Indirect, addr, reg) => {
                let mut addr = self.emulator.memory.get_data(addr)?;

                if reg != R0 {
                    addr += self.emulator.context.r[reg.index()];
                }


                self.emulator.memory.set_data(addr, value as u16)?;
            },
        }

        Ok(())
    }

    fn pop_stack(&mut self) -> Result<i32, M::Error> {
        let addr = self.first_operand();
        let value = self.emulator.memory.get_data(addr + 1)?;
        self.set_first_operand(addr + 1);

        Ok(value as i32)
    }

    fn push_stack(&mut self, value: i32) -> Result<(), M::Error> {
        let addr = self.first_operand();

        if !self.emulator.memory.stack_address_range()?.contains(&addr) {
            let range = self.emulator.memory.stack_address_range()?;
            let stack_head = range.start();
            let amount = std::cmp::max(stack_head - addr, range.len() as u16);
            self.emulator.memory.grow_stack(amount)?;
        }

        self.emulator.memory.set_data(addr, value as u16)?;
        self.set_first_operand(addr - 1);

        Ok(())
    }

    /// Execute the instruction.
    ///
    /// # Returns
    /// A memory error if the instruction tries to make and illegal memory access.
    fn emulate(&mut self) -> Result<(), M::Error> {
        match self.instruction.opcode {
            OpCode::Load => {
                let op2 = self.second_operand()?;
                self.set_first_operand(op2);
            },
            OpCode::Store => {
                // Ignore addressing modes, STORE is a special case.
                let op1 = self.first_operand();
                self.emulator.memory.set_data(self.instruction.immediate, op1)?;
            },
            OpCode::In => {
                let device = self.second_operand()?;
                let input = self.emulator.io.input(device);
                self.set_first_operand(input);
            },
            OpCode::Out => {
                let output = self.first_operand();
                let device = self.second_operand()?;
                self.emulator.io.output(device, output);
            },

            OpCode::Compare => {
                self.emulator.context.flags.zero();

                let op1 = self.first_operand();
                let op2 = self.second_operand()?;

                match op1.cmp(&op2) {
                    Ordering::Less    => self.emulator.context.flags.less = true,
                    Ordering::Equal   => self.emulator.context.flags.equal = true,
                    Ordering::Greater => self.emulator.context.flags.greater = true,
                }
            },

            OpCode::Jump { condition, negated } => {
                let op1 = self.first_operand();

                let result = match condition {
                    JumpCondition::Unconditional => !negated,
                    JumpCondition::Zero => op1 == 0,
                    JumpCondition::Positive => op1 > 0,
                    JumpCondition::Negative => op1 < 0,
                    JumpCondition::Less => self.emulator.context.flags.less,
                    JumpCondition::Greater => self.emulator.context.flags.greater,
                    JumpCondition::Equal => self.emulator.context.flags.equal,
                };

                if result ^ negated {
                    self.emulator.context.pc = self.instruction.immediate;
                }
            },

            OpCode::SupervisorCall => {
                // XXX: Maybe we should give the implementor of InputOutput easy access to the
                //      emulator and have them decide what to do.
                if self.instruction.immediate == 11 {
                    self.emulator.halted = true;
                }

                self.emulator.io.supervisor_call(self.instruction.immediate);
            },

            OpCode::Push => {
                let op2 = self.second_operand()?;
                self.push_stack(op2 as i32)?;
            },

            OpCode::Pop => {
                let value = self.pop_stack()?;
                self.set_second_operand(value)?;
            },

            OpCode::PushRegisters => {
                for i in 0..8 {
                    self.push_stack(self.emulator.context.r[i] as i32)?;
                }
                self.push_stack(self.emulator.context.flags.as_word())?;
            },

            OpCode::PopRegisters => {
                let flags = self.pop_stack()?;
                self.emulator.context.flags.from_word(flags);

                for i in (0..8).into_iter().rev() {
                    let value = self.pop_stack()?;
                    self.emulator.context.r[i] = value as u16;
                }
            },
            
            OpCode::Call => {
                //let addr = self.pop_stack()?;
                self.push_stack(self.emulator.context.pc as i32)?;
                self.emulator.context.pc = self.second_operand()?;
            },

            OpCode::Exit => {
                let addr = self.pop_stack()?;
                self.emulator.context.pc = addr as u16;
            },

            OpCode::NoOperation => (),

            arithmetic_instruction => {
                let mut op1 = self.first_operand();
                let op2 = self.second_operand()?;

                match arithmetic_instruction {
                    OpCode::Add =>      op1 += op2,
                    OpCode::Subtract => op1 -= op2,
                    OpCode::Multiply => op1 *= op2,
                    OpCode::Divide =>   op1 /= op2,
                    OpCode::Modulo =>   op1 %= op2,

                    OpCode::And =>                  op1  &= op2,
                    OpCode::Or =>                   op1  |= op2,
                    OpCode::Xor =>                  op1  ^= op2,
                    OpCode::Not =>                  op1   = !op1,
                    OpCode::ShiftLeft =>            op1 <<= op2,
                    OpCode::ShiftRight =>           op1 >>= op2,
                    OpCode::ArithmeticShiftRight => unimplemented!(),

                    op => unimplemented!("Instruction {:?}", op),
                }

                self.set_first_operand(op1);
            }
        }

        Ok(())
    }
}

/// The emulator contains all neccessary context for executing a TTK91 program
/// and interfaces for doing IO.
#[derive(Clone, Debug)]
pub struct Emulator<Mem, IO> {
    /// The memory of the emulated machine.
    /// Contains all the instructions and data required by the program.
    /// Implements [Memory].
    pub memory: Mem,

    /// The execution context, which includes the registers and flags of the CPU.
    pub context: Context,

    /// Interface for doing IO operations and supervisor calls.
    pub io: IO,

    /// True if the execution has been halted.
    pub halted: bool,
}

impl<Mem, IO> Emulator<Mem, IO> where Mem: Memory, IO: InputOutput {
    /// Create a new emulator.
    ///
    /// # Parameters
    /// - `memory`: A [Memory](Memory) object which has the program.
    /// - `io`: An [IO handler](InputOutput).
    ///
    /// # Returns
    /// A new [Emulator] instance.
    pub fn new(memory: Mem, io: IO) -> Result<Emulator<Mem, IO>, Mem::Error> {
        let stack_base_address = *memory.stack_address_range()?.end();

        Ok(Emulator {
            context: Context {
                r: [0, 0, 0, 0, 0, 0, 0, stack_base_address],
                pc: 0,
                flags: Default::default(),
            },
            memory,
            io,
            halted: false,
        })
    }

    /// Fetches the instruction from the address pointed by the Program Counter register.
    pub fn get_current_instruction(&mut self) -> Result<Instruction, Mem::Error> {
        self.memory.get_instruction(self.context.pc)
    }

    /// Executes a single instruction.
    ///
    /// Does not increment the `PC` register or do anything else related to the instruction
    /// fetching.
    ///
    /// # Errors
    /// Returns a memory error if the instruction tries to execute an illegal memory operation.
    pub fn emulate_instruction(&mut self, ins: &Instruction) -> Result<(), Mem::Error> {
        //let mut first_operand = self.context.r[ins.register.index()];
        //let second_operand = self.resolve_operand(&ins)?;

        let mut ctx = InstructionEmulationContext {
            emulator: self,
            instruction: ins,
        };

        return ctx.emulate();
    }

    /// Fetches the next instruction, increments the program counter and executes the instruction.
    ///
    /// # Errors
    /// Returns a memory error if the instruction tries to execute an illegal memory operation.
    pub fn step(&mut self) -> Result<(), Mem::Error> {
        if self.halted {
            return Ok(());
        }

        let ins = self.get_current_instruction()?;
        self.context.pc += 1;

        self.emulate_instruction(&ins)
    }

    /// Executes the program until it halts the execution or .
    ///
    /// # Errors
    /// Returns a memory error if the instruction tries to execute an illegal memory operation.
    pub fn run(&mut self) -> Result<(), Mem::Error> {
        while !self.halted {
            self.step()?;
        }

        Ok(())
    }
}

/// An IO handler for testing purposes.
///
/// Reads input values from a pre-determined input buffer and
/// appends printed values to an output buffer.
pub struct TestIo {
    input_buffer: Vec<u16>,
    output_buffer: Vec<u16>,
}

impl TestIo {
    pub fn new() -> TestIo {
        TestIo {
            input_buffer: Vec::new(),
            output_buffer: Vec::new(),
        }
    }

    pub fn with_input<I: IntoIterator<Item=u16>>(input: I) -> TestIo {
        TestIo {
            input_buffer: input.into_iter().collect(),
            output_buffer: Vec::new(),
        }
    }

    pub fn input(&mut self, value: u16) {
        self.input_buffer.push(value);
    }

    pub fn output(&self) -> &[u16] {
        &self.output_buffer[..]
    }

    pub fn into_output(self) -> Vec<u16> {
        self.output_buffer
    }
}

impl InputOutput for TestIo {
    fn input(&mut self, _device: u16) -> u16 {
        self.input_buffer.remove(0)
    }

    fn output(&mut self, _device: u16, value: u16) {
        self.output_buffer.push(value);
    }

    fn supervisor_call(&mut self, _code: u16) {}
}

impl InputOutput for &mut TestIo {
    fn input(&mut self, _device: u16) -> u16 {
        self.input_buffer.remove(0)
    }

    fn output(&mut self, _device: u16, value: u16) {
        self.output_buffer.push(value);
    }

    fn supervisor_call(&mut self, _code: u16) {}
}

/// An IO handler that defines two output devices:
/// - `0`, which prints the data as numbers to the terminal standard output.
/// - `1`, which prints the data as an unicode character to the terminal standard ourput.
///
/// And two input devices:
/// - `0`, which reads an integer from the terminal.
/// - `1`, which reads a single byte from the terminal.
///
/// All other input deivices return 0.
/// If an error occurs while reading from an input device, the device will return 0xFFFF.
///
/// A supervisor call is a no-op.
pub struct StdIo;

impl InputOutput for StdIo {
    fn input(&mut self, device: u16) -> u16 {
        match device {
            0 => {
                let mut line = String::new();

                std::io::stdin().read_line(&mut line)
                    .expect("could not read from standard input");

                line[..line.len()-1]
                    .parse()
                    .unwrap_or(0xFFFF)
            },
            1 => {
                std::io::stdin()
                    .bytes()
                    .next()
                    .transpose()
                    .unwrap_or(None)
                    .map(|byte| byte as u16)
                    .unwrap_or(0xFFFF)
            },
            _ => 0,
        }
    }

    fn output(&mut self, device: u16, data: u16) {
        match device {
            0 => println!("{}", data),
            1 => print!("{}", std::char::from_u32(data as u32)
                          .map(|c| format!("{}", c))
                          .unwrap_or("<Invalid Character>".to_string())),
            _ => (),
        }
        println!("{:?}", data);
    }

    fn supervisor_call(&mut self, _code: u16) {}
}

#[derive(Clone, Debug)]
struct MemoryError {
    address: u16,
    kind: MemoryErrorKind,
}

#[derive(Debug, Clone, Copy)]
enum MemoryErrorKind {
    InvalidAddress,
    IllegalAccess,
}

struct FixedMemory {
    inner: Vec<i32>,
    stack_start: u16,
}

use std::convert::TryFrom;

impl Memory for FixedMemory {
    type Error = MemoryError;

    fn get_instruction(&mut self, address: u16) -> Result<Instruction, Self::Error> {
        self.inner.get(address as usize)
            .map(|w| *w as u32)
            .ok_or(MemoryError { address, kind: MemoryErrorKind::InvalidAddress })
            .and_then(|word| TryFrom::try_from(word)
                .map_err(|_| MemoryError { address, kind: MemoryErrorKind::IllegalAccess }))
    }

    fn get_data(&mut self, address: u16) -> Result<u16, Self::Error> {
        self.inner.get(address as usize)
            .map(|w| *w as u16)
            .ok_or(MemoryError { address, kind: MemoryErrorKind::InvalidAddress })
    }

    fn set_data(&mut self, address: u16, value: u16) -> Result<(), Self::Error> {
        if self.inner.len() < address as usize {
            return Err(MemoryError { address, kind: MemoryErrorKind::InvalidAddress });
        }

        self.inner[address as usize] = value as i32;

        Ok(())
    }

    fn grow_stack(&mut self, _amount: u16) -> Result<(), Self::Error> {
        panic!("FixedMemory cannot grow it's stack");
    }

    fn stack_address_range(&self) -> Result<std::ops::RangeInclusive<u16>, Self::Error> {
        Ok(self.stack_start..=(self.inner.len() as u16 - 1))
    }
}

impl FixedMemory {
    fn new(size: u16, stack: u16) -> FixedMemory {
        FixedMemory {
            inner: vec![0; size as usize],
            stack_start: size - stack,
        }
    }

    fn load(&mut self, program: crate::bytecode::Program) {
        for (addr, word) in program.to_words().into_iter().enumerate() {
            self.inner[addr] = word as i32;
        }
    }
}

struct BalloonMemory {
    program: Vec<i32>,
    stack: Vec<i32>,
}

impl BalloonMemory {
    fn new(program: crate::bytecode::Program) -> BalloonMemory {
        BalloonMemory {
            program: program
                .to_words()
                .into_iter()
                .map(|w| w as i32)
                .collect(),
            stack: vec![0; 8],
        }
    }
}

impl Memory for BalloonMemory {
    type Error = MemoryError;

    fn get_instruction(&mut self, address: u16) -> Result<Instruction, Self::Error> {
        self.program.get(address as usize)
            .map(|w| *w as u32)
            .ok_or(MemoryError { address, kind: MemoryErrorKind::InvalidAddress })
            .and_then(|word| TryFrom::try_from(word)
                .map_err(|_| MemoryError { address, kind: MemoryErrorKind::InvalidAddress }))
    }

    fn get_data(&mut self, address: u16) -> Result<u16, Self::Error> {
        let stack_range = self.stack_address_range()?;

        if address < self.program.len() as u16 {
            Ok(self.program[address as usize] as u16)
        } else if stack_range.contains(&address) {
            Ok(self.stack[address as usize - *stack_range.start() as usize] as u16)
        } else {
            Err(MemoryError {
                address,
                kind: MemoryErrorKind::InvalidAddress,
            })
        }
    }

    fn set_data(&mut self, address: u16, value: u16) -> Result<(), Self::Error> {
        let stack_range = self.stack_address_range()?;

        if address < self.program.len() as u16 {
            self.program[address as usize] = value as i32;
        } else if stack_range.contains(&address) {
            self.stack[address as usize - *stack_range.start() as usize] = value as i32;
        } else {
            return Err(MemoryError {
                address,
                kind: MemoryErrorKind::InvalidAddress,
            });
        }

        Ok(())
    }

    fn grow_stack(&mut self, amount: u16) -> Result<(), Self::Error> {
        self.stack.extend(std::iter::repeat(0).take(amount as usize));
        Ok(())
    }

    fn stack_address_range(&self) -> Result<std::ops::RangeInclusive<u16>, Self::Error> {
        Ok((0xFFFF-self.stack.len() as u16)+1..=0xFFFF)
    }
}

macro_rules! assert_register {
    ($emulator:expr, $register:expr, $value:expr) => {
        assert_eq!($emulator.context.r[$register], $value, "Register {} != {}", $register, $value);
    };
}

macro_rules! assert_symbol {
    ($emulator:expr, $program:expr, $symbol:expr, $value:expr) => {
        let addr = $program.symbol_table.get($symbol)
            .expect("no such symbol");
        let value = $emulator.memory.get_data(*addr)
            .expect("symbol points to invalid memory");
        assert_eq!(value, $value, "Symbol '{}' at {} != {}", $symbol, addr, $value);
    };
}

#[test]
fn test_stack_basic() {
    let program = crate::symbolic::Program::parse(r#"
        var1 DC 1234
        var2 DC 0
        var3 DC 0

        LOAD R1, =4321
        LOAD R2, =var2

        PUSH SP, var1
        PUSH SP, =777
        PUSH SP, R1

        POP  SP, var1
        POP  SP, R1
        POP  SP, @R2

        SVC  SP, =11
    "#).unwrap();
    println!("{:?}", program);

    let program = program.compile();

    let mut memory = FixedMemory::new(1024, 128);
    memory.load(program.clone());

    let mut emulator = Emulator::new(memory, TestIo::new()).unwrap();

    while !emulator.halted {
        println!("{:?}", emulator.get_current_instruction());
        emulator.step().unwrap();
        println!("{:?}", emulator.context);
    }

    assert_register!(emulator, 1, 777);
    assert_symbol!(emulator, program, "var3", 0);
    assert_symbol!(emulator, program, "var1", 4321);
    assert_symbol!(emulator, program, "var2", 1234);
}

#[test]
fn test_stack_procedures() {
    let program = crate::symbolic::Program::parse(r#"
    var1    DC 0

    main    CALL  SP, =proc
            SVC   SP, =HALT

    proc    LOAD  R1, =1234
            STORE R1, =var1
            EXIT  SP, =0xABCD
    "#).unwrap();
    println!("{:?}", program);

    let program = program.compile();

    let mut memory = FixedMemory::new(1024, 128);
    memory.load(program.clone());

    let mut emulator = Emulator::new(memory, TestIo::new()).unwrap();
    let mut cycles = 0;

    while !emulator.halted && cycles < 100 {
        println!("{:?}", emulator.get_current_instruction());
        emulator.step().unwrap();
        println!("{:?}", emulator.context);
        cycles += 1;
    }

    assert_symbol!(emulator, program, "var1", 1234);
}

#[test]
fn test_stack_grow() {
    let program = crate::symbolic::Program::parse(r#"
        LOAD  R1, =100
        PUSH  SP, R1
        SUB   R1, =1
        JNZER R1, =0x0001
        SVC   SP, =HALT
    "#).unwrap();
    println!("{:?}", program);

    let program = program.compile();

    let mut memory = BalloonMemory::new(program.clone());

    let mut emulator = Emulator::new(memory, TestIo::new()).unwrap();
    let mut cycles = 0;

    while !emulator.halted && cycles < 1000 {
        println!("{:?}", emulator.get_current_instruction());
        emulator.step().unwrap();
        println!("{:?}", emulator.context);
        cycles += 1;
    }
}

#[test]
fn test_stack_push_pop_registers() {
    let program = crate::symbolic::Program::parse(r#"
        PUSHR SP, =0
        COMP  R1, =0
        LOAD  R2, =0
        LOAD  R3, =0
        LOAD  R4, =0
        LOAD  R5, =0
        LOAD  R6, =0
        POPR  SP, =0
        SVC   SP, =HALT
    "#).expect("could not parse program");

    let program = program.compile();
    let mut memory = FixedMemory::new(128, 32);
    memory.load(program);

    let mut emulator = Emulator::new(memory, TestIo::new())
        .expect("could not initialize emulator");

    // Register R7 is the stack pointer and canot be changed if we want to keep the stack
    // functional.
    for i in 0..7 {
        emulator.context.r[i] = i as u16;
    }

    emulator.context.flags.from_word(0b111);
    
    while !emulator.halted {
        println!("{:?}", emulator.get_current_instruction());
        emulator.step()
            .expect("error while executing the program");
        println!("{:?}", emulator.context);
    }

    for i in 0..7 {
        assert_eq!(emulator.context.r[i], i as u16);
    }
    assert_eq!(emulator.context.flags.as_word(), 0b111);
}
