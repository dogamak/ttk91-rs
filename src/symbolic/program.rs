//! Validated representation of a program written in the symbolic format.
//!
//! This module contains types that represent the various parts of an program in a way that makes
//! representing invalid programs impossible (or at least tries).
use super::parser::ParseError;
use crate::instruction::{Instruction as BytecodeInstruction, Mode, OpCode, Register};
use crate::parsing::Span;
use crate::symbol_table::{SymbolId, SymbolTable};
use crate::symbolic::parser::{ErrorKind, Parser};
use crate::compiler::{compile, IrBackend};

use std::fmt;

/// An instruction for the preprocessor or the compiler.
///
/// This type can only represent valid instructions.
#[derive(Debug, Clone)]
pub struct PseudoInstruction {
    pub size: u16,
    pub value: i32,
}

/// An instruction, which can be either a pseudo instruction or a real instruction.
#[derive(Debug, Clone)]
pub enum Instruction {
    Real(RealInstruction),
    Pseudo(PseudoInstruction),
}

/// Opcode of a pseudo instruction.
#[derive(Debug, Clone, PartialEq)]
pub enum PseudoOpCode {
    /// Data Constant. Reserves a single word of data and sets it to the provided value.
    DC,

    /// Data Segment. Reserves the specified number of words of memory. Initializes the words to
    /// zero.
    DS,

    /// Equals. Defines a symbol with the specified value.
    EQU,
}

impl fmt::Display for PseudoOpCode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            PseudoOpCode::DC => write!(f, "DC"),
            PseudoOpCode::DS => write!(f, "DS"),
            PseudoOpCode::EQU => write!(f, "EQU"),
        }
    }
}

/// A single instruction and any number of associated labels.
#[derive(Clone, Debug)]
pub struct InstructionEntry {
    pub labels: Vec<SymbolId>,
    pub instruction: Instruction,
    pub span: Option<Span>,
}

/// An entire program parsed from a symbolic format.
///
/// This type represents a validated program, whose all instructions are quaranteed to be valid.
#[derive(Debug, Default, Clone)]
pub struct Program {
    /// List of instructions and labels assigned to them.
    pub instructions: Vec<InstructionEntry>,

    /// The symbol table created during parsing.
    ///
    /// At this stage the symbol table contains no information about the symbols, besides locations
    /// of their definitions and references in the input file.
    pub symbol_table: SymbolTable,
}

/// A real instruction that can be executed by the [Emulator](crate::emulator::Emulator) and has a
/// bytecode representation.
#[derive(Debug, Clone)]
pub struct RealInstruction {
    /// Opcode specifying the type of the instruction.
    pub opcode: OpCode,

    /// First operand of the instruction.
    ///
    /// This operand is always an register, but is set to the special register [R0](Register::R0)
    /// for instruction that do not utilize it.
    pub operand1: Register,

    /// The second operand of the instruction.
    ///
    /// For instructions that do not utilize the second operand, this is set to the [Default] value
    /// of [SecondOperand].
    pub operand2: SecondOperand,
}

impl RealInstruction {
    pub fn relocation_symbol(&self) -> Option<RelocationEntry> {
        let symbol = match self.operand2.value {
            Value::Symbol(ref symbol) => symbol.clone(),
            _ => return None,
        };

        Some(RelocationEntry {
            kind: RelocationKind::Address,
            symbol,
        })
    }
}

impl Into<BytecodeInstruction> for RealInstruction {
    fn into(self) -> BytecodeInstruction {
        let mut index_register = Register::R0;

        let immediate = match self.operand2.value {
            Value::Register(reg) => {
                index_register = reg;
                0
            }
            Value::Symbol(_sym) => u16::max_value(),
            Value::Immediate(value) => value,
        };

        BytecodeInstruction {
            opcode: self.opcode,
            register: self.operand1,
            index_register,
            mode: self.operand2.mode,
            immediate,
        }
    }
}

#[derive(Clone, Debug)]
pub enum RelocationKind {
    Address,
    Value,
}

#[derive(Clone, Debug)]
pub struct RelocationEntry {
    pub symbol: SymbolId,
    pub kind: RelocationKind,
}

/// A base value that can be passed to an instruction as it's second operand.
#[derive(Clone, Debug)]
pub enum Value {
    Symbol(SymbolId),
    Immediate(u16),
    Register(Register),
}

impl Value {
    /// Return true if self represents the [Value::Immediate] variant.
    pub fn is_immediate(&self) -> bool {
        match self {
            Value::Immediate(_) => true,
            _ => false,
        }
    }

    /// Return true if self represents the [Value::Register] variant.
    pub fn is_register(&self) -> bool {
        match self {
            Value::Register(_) => true,
            _ => false,
        }
    }

    /// If self represents the [Value::Register] variant, returns the wrapped register.
    /// Otherwise returns `None`.
    pub fn register(&self) -> Option<Register> {
        match self {
            Value::Register(reg) => Some(*reg),
            _ => None,
        }
    }
}

/// The second operand of an instruction.
#[derive(Clone, Debug)]
pub struct SecondOperand {
    /// The addressing mode used for this operand.
    pub mode: Mode,

    /// The base value for this operand.
    pub value: Value,

    /// An optional index register whose value is added to the base value before address
    /// resolution.
    pub index: Option<Register>,
}

impl From<super::ast::Operand> for SecondOperand {
    fn from(operand: super::ast::Operand) -> SecondOperand {
        SecondOperand {
            mode: operand.mode.unwrap_or(Mode::Direct),
            value: operand.base,
            index: operand.index,
        }
    }
}

impl<'a> From<&'a super::ast::Operand> for SecondOperand {
    fn from(operand: &'a super::ast::Operand) -> SecondOperand {
        SecondOperand {
            mode: operand.mode.unwrap_or(Mode::Direct),
            value: operand.base.clone(),
            index: operand.index,
        }
    }
}

impl Default for SecondOperand {
    fn default() -> SecondOperand {
        SecondOperand {
            mode: Mode::Immediate,
            value: Value::Immediate(0),
            index: None,
        }
    }
}

/// Validates the provided [ast::Instruction](super::ast::Instruction) and converts it to an
/// [Instruction].
///
/// This function mainly makes sure that the instruction has been provided with the right amount of
/// operands and that the operands are of the correct type.
pub fn validate_instruction(
    instruction: super::ast::Instruction,
) -> Result<Instruction, ParseError<'static>> {
    use super::ast::{JumpCondition, OpCode, RealOpCode};

    match instruction.opcode {
        OpCode::Pseudo(op) => {
            if instruction.operands.len() != 1 {
                let error = ParseError::other(
                    instruction.span.clone(),
                    ErrorKind::OperandCount {
                        span: instruction.span,
                        got: instruction.operands.len(),
                        expected: 1,
                    },
                )
                .context("pseudo instructions take exactly one operand");

                return Err(error);
            }

            let operand = &instruction.operands[0];

            if operand.index.is_some() || operand.mode.is_some() || !operand.base.is_immediate() {
                let kind = ErrorKind::InvalidOperand {
                    span: operand.span.clone(),
                    index: 0,
                };

                let error = ParseError::other(operand.span.clone(), kind)
                    .context("the operand should be a number literal for pseudo instructions");

                return Err(error);
            }

            let operand = match operand.base {
                Value::Immediate(imm) => imm,
                _ => unreachable!(),
            };

            let instruction = match op {
                PseudoOpCode::EQU | PseudoOpCode::DC => PseudoInstruction {
                    size: 1,
                    value: operand as i32,
                },
                PseudoOpCode::DS => PseudoInstruction {
                    size: operand,
                    value: 0,
                },
            };

            Ok(Instruction::Pseudo(instruction))
        }
        OpCode::Real(RealOpCode::NoOperation) => {
            if !instruction.operands.is_empty() {
                let kind = ErrorKind::OperandCount {
                    span: instruction.span.clone(),
                    expected: 0,
                    got: instruction.operands.len(),
                };

                let error = ParseError::other(instruction.span, kind)
                    .context("the NOP instruction takes no operands");

                return Err(error);
            }

            Ok(Instruction::Real(RealInstruction {
                opcode: RealOpCode::NoOperation,
                operand1: Register::R0,
                operand2: Default::default(),
            }))
        }
        OpCode::Real(opcode @ RealOpCode::PopRegisters)
        | OpCode::Real(opcode @ RealOpCode::PushRegisters)
        | OpCode::Real(opcode @ RealOpCode::Not) => {
            if instruction.operands.len() != 1 {
                let kind = ErrorKind::OperandCount {
                    span: instruction.span.clone(),
                    expected: 1,
                    got: instruction.operands.len(),
                };

                let error = ParseError::other(instruction.span, kind)
                    .context("this instruction expects a single register operand");

                return Err(error);
            }

            let operand = &instruction.operands[0];

            if operand.index.is_some() || operand.mode.is_some() || !operand.base.is_register() {
                let kind = ErrorKind::InvalidOperand {
                    span: operand.span.clone(),
                    index: 0,
                };

                let error = ParseError::other(instruction.span, kind)
                    .context("this operand must be a register");

                return Err(error);
            }

            Ok(Instruction::Real(RealInstruction {
                opcode,
                operand1: operand.base.register().unwrap(),
                operand2: Default::default(),
            }))
        }
        OpCode::Real(
            opcode
            @
            RealOpCode::Jump {
                condition: JumpCondition::Unconditional,
                ..
            },
        ) => {
            if instruction.operands.len() != 1 {
                let kind = ErrorKind::OperandCount {
                    span: instruction.span.clone(),
                    expected: 1,
                    got: instruction.operands.len(),
                };

                let error = ParseError::other(instruction.span, kind).context(
                    "jump instructions that examine the state register take only a single operand",
                );

                return Err(error);
            }

            let operand = &instruction.operands[0];

            Ok(Instruction::Real(RealInstruction {
                opcode,
                operand1: Register::R0,
                operand2: operand.into(),
            }))
        }
        OpCode::Real(opcode) => {
            if instruction.operands.len() != 2 {
                let kind = ErrorKind::OperandCount {
                    span: instruction.span.clone(),
                    expected: 2,
                    got: instruction.operands.len(),
                };

                let error = ParseError::other(instruction.span, kind)
                    .context("this instruction expects two operands");

                return Err(error);
            }

            let operand1 = &instruction.operands[0];
            let operand2 = &instruction.operands[1];

            if operand1.index.is_some() || operand1.mode.is_some() || !operand1.base.is_register() {
                let kind = ErrorKind::InvalidOperand {
                    span: operand1.span.clone(),
                    index: 0,
                };

                let error = ParseError::other(operand1.span.clone(), kind)
                    .context("this operand must be a register");

                return Err(error);
            }

            Ok(Instruction::Real(RealInstruction {
                opcode,
                operand1: operand1.base.register().unwrap(),
                operand2: operand2.into(),
            }))
        }
    }
}

impl Program {
    /// Reads, parses and validates an program from a string slice. Returns immediately on the
    /// first encountered parsing error.
    pub fn parse(input: &str) -> Result<Program, ParseError> {
        let mut parser = Parser::from_str(input);
        let ast = parser.parse()?;

        let instructions = ast
            .parts
            .into_iter()
            .map(|part| {
                Ok(InstructionEntry {
                    labels: part.labels,
                    span: Some(part.instruction.span.clone()),
                    instruction: validate_instruction(part.instruction)?,
                })
            })
            .collect::<Result<_, _>>()?;

        Ok(Program {
            symbol_table: parser.state.symbol_table,
            instructions,
        })
    }

    /// Reads, parses and validates an program from a string slice. Tries to produce the best
    /// possible error messages and spends extra time on this if the parsing fails.
    pub fn parse_verbose(input: &str) -> Result<Program, Vec<ParseError>> {
        let mut parser = Parser::from_str(input);

        let (ast, mut errors) = match parser.parse_verbose() {
            Ok(ast) => (ast, Vec::new()),
            Err((None, errors)) => return Err(errors),
            Err((Some(ast), errors)) => (ast, errors),
        };

        let mut instructions = Vec::new();

        for part in ast.parts {
            let span = part.instruction.span.clone();

            match validate_instruction(part.instruction) {
                Ok(instruction) => instructions.push(InstructionEntry {
                    labels: part.labels,
                    span: Some(span),
                    instruction,
                }),
                Err(err) => errors.push(err),
            }
        }

        if !errors.is_empty() {
            return Err(errors);
        }

        Ok(Program {
            symbol_table: parser.state.symbol_table,
            instructions,
        })
    }

    /// Compiles the program into internal representation of bytecode that is ready to be emulated.
    pub fn compile(self) -> crate::bytecode::Program {
        compile(IrBackend::default(), self).unwrap()
    }
}
