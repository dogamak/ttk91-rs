//! Types defining the Abstract Syntax Tree of a program written in the symbolic format.
//!
//! This AST can represent invalid programs as no validation of the number and type of operands has
//! been done. For a representation of a validated program, see [crate::symbolic::program::Program].

pub use crate::{
    symbol_table::SymbolId,
    parsing::Span,
    instruction::{JumpCondition, Mode, OpCode as RealOpCode, Register},
    symbolic::program::{PseudoOpCode, Value},
};

/// The AST of an entire program.
#[derive(Debug, Clone)]
pub struct Program {
    pub parts: Vec<Part>,
}

/// A symbolic instruction and any associated labels. Generally a single line of input.
#[derive(Debug, Clone)]
pub struct Part {
    /// Any labels defined before the instruction.
    pub labels: Vec<SymbolId>,
    pub instruction: Instruction,
}

/// Any valid opcode, including both real opcodes and pseudo opcodes.
#[derive(Debug, Clone)]
pub enum OpCode {
    Pseudo(PseudoOpCode),
    Real(RealOpCode),
}

/// An instruction that is composed of an opcode and any number of operands.
///
/// Different instructions have different requirements from the opcodes they are provided.
/// At this stage of the compilation, no validation has been done to the operands.
#[derive(Debug, Clone)]
pub struct Instruction {
    /// The opcode specifying the type of this instruction.
    pub opcode: OpCode,

    /// A list of any number of operands.
    pub operands: Vec<Operand>,

    /// The location of this instruction in the input stream.
    pub span: Span,
}

/// A single operand. Eg. `=ARRAY(R2)`, `R2` or `-123`.
#[derive(Debug, Clone)]
pub struct Operand {
    /// Optionally specified addressing mode.
    pub mode: Option<Mode>,

    /// The base of this operand.
    pub base: Value,

    /// An optional index register, whose value is added to the base value.
    pub index: Option<Register>,

    /// Location of this operand in the input stream.
    pub span: Span,
}
