use crate::symbol_table::SymbolId;

use crate::parsing::Span;

pub use crate::instruction::{
    Register,
    OpCode as RealOpCode,
    JumpCondition,
    Mode,
};

pub use crate::symbolic::program::{
    PseudoOpCode,
    Value,
    RealInstruction,
    PseudoInstruction,
    SymbolicInstruction,
    SecondOperand,
};

#[derive(Debug, Clone)]
pub struct Program {
    pub parts: Vec<Part>,
}

#[derive(Debug, Clone)]
pub struct Part {
    pub labels: Vec<SymbolId>,
    pub instruction: Instruction,
}

#[derive(Debug, Clone)]
pub enum OpCode {
    Pseudo(PseudoOpCode),
    Real(RealOpCode),
}

#[derive(Debug, Clone)]
pub struct Instruction {
    pub opcode: OpCode,
    pub operands: Vec<Operand>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Operand {
    pub mode: Option<Mode>,
    pub base: Value,
    pub index: Option<Register>,
    pub span: Span,
}
