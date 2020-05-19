use crate::instruction::{OpCode, Register, Mode, Instruction};
use crate::parsing::{Error as ParseError, Span};
use crate::compiler::SourceMap;
use std::collections::HashMap;
use crate::symbol_table::{SymbolId, SymbolTable};

#[derive(Debug, Clone)]
pub struct InitializationTableEntry {
    pub symbol: String,
    pub size: u16,
    pub value: i32,
}

#[derive(Debug, Clone)]
pub struct PseudoInstruction {
    pub size: u16,
    pub value: i32,
}

#[derive(Debug, Clone)]
pub enum SymbolicInstruction {
    Concrete(ConcreteInstruction),
    Pseudo(PseudoInstruction),
}

#[derive(Debug, Clone, PartialEq)]
pub enum PseudoOpCode {
    DC,
    DS,
    EQU,
}

#[derive(Clone, Debug)]
pub struct InstructionEntry {
    pub labels: Vec<SymbolId>,
    pub instruction: SymbolicInstruction,
    pub span: Option<Span>,
}

#[derive(Debug, Default, Clone)]
pub struct Program {
    //pub init_table: Vec<(Option<String>, PseudoInstruction)>,
    pub instructions: Vec<InstructionEntry>,
    pub symbol_table: SymbolTable,
}

#[derive(Debug, Clone)]
pub struct ConcreteInstruction {
    pub label: Option<String>,
    pub opcode: OpCode,
    pub operand1: Register,
    pub operand2: SecondOperand,
}

impl ConcreteInstruction {
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

impl Into<Instruction> for ConcreteInstruction {
    fn into(self) -> Instruction {
        let mut index_register = Register::R0;

        let immediate = match self.operand2.value {
            Value::Register(reg) => {
                index_register = reg;
                0
            },
            Value::Symbol(_sym) => u16::max_value(),
            Value::Immediate(value) => value,
        };

        Instruction {
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

#[derive(Clone, Debug)]
pub enum Value {
    Symbol(SymbolId),
    Immediate(u16),
    Register(Register),
}

#[derive(Clone, Debug)]
pub struct SecondOperand {
    pub(crate) mode: Mode,
    pub(crate) value: Value,
    pub(crate) index: Option<Register>,
}

impl Program {
    pub fn parse(s: &str) -> Result<Program, ParseError<String>> {
        super::parser::parse_symbolic_file(s)
    }

    pub fn compile(self) -> crate::bytecode::Program {
        use crate::compiler::compile;
        compile(self)
    }

    pub fn compile_sourcemap(self) -> SourceMap<crate::bytecode::Program> {
        crate::compiler::compile(self)
    }
}
