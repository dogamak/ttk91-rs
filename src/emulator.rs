//! [Emulator] for executing [bytecode programs](crate::bytecode::program::Program).

use std::convert::TryInto;
use std::cmp::Ordering;

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
    io: IO,

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
    pub fn new(memory: Mem, io: IO) -> Emulator<Mem, IO> {
        Emulator {
            context: Default::default(),
            memory,
            io,
            halted: false,
        }
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
/// All input operations return 0 for now.
///
/// A supervisor call is a no-op.
pub struct StdIo;

impl InputOutput for StdIo {
    fn input(&mut self, _device: u16) -> u16 {
        0
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
