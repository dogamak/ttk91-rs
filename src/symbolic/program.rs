use crate::instruction::{OpCode, Register, Mode, Instruction};
use crate::parsing::{Error as ParseError, Span};
use crate::symbolic::parser::{Parser, Context};
use crate::compiler::SourceMap;
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
    Real(RealInstruction),
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
    pub instructions: Vec<InstructionEntry>,
    pub symbol_table: SymbolTable,
}

#[derive(Debug, Clone)]
pub struct RealInstruction {
    pub opcode: OpCode,
    pub operand1: Register,
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

impl Into<Instruction> for RealInstruction {
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

impl Value {
    pub fn is_immediate(&self) -> bool {
        match self {
            Value::Immediate(_) => true,
            _ => false,
        }
    }

    pub fn is_register(&self) -> bool {
        match self {
            Value::Register(_) => true,
            _ => false,
        }
    }

    pub fn register(&self) -> Option<Register> {
        match self {
            Value::Register(reg) => Some(*reg),
            _ => None,
        }
    }
}

#[derive(Clone, Debug)]
pub struct SecondOperand {
    pub(crate) mode: Mode,
    pub(crate) value: Value,
    pub(crate) index: Option<Register>,
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

pub fn validate_instruction(instruction: super::ast::Instruction)
    -> Result<SymbolicInstruction, ParseError<Context>>
{
    use super::ast::{OpCode, RealOpCode, JumpCondition};

    match instruction.opcode {
        OpCode::Pseudo(op) => {
            if instruction.operands.len() != 1 {
                return Err(ParseError::new(instruction.span, "pseudo instructions take exactly one operand"));
            }

            let operand = &instruction.operands[0];

            if operand.index.is_some() || operand.mode.is_some() || !operand.base.is_immediate() {
                return Err(ParseError::new(
                    operand.span.clone(),
                    "the operand should be a number literal for pseudo instructions",
                ));
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

            Ok(SymbolicInstruction::Pseudo(instruction))
        },
        OpCode::Real(RealOpCode::NoOperation) => {
            if !instruction.operands.is_empty() {
                return Err(ParseError::new(instruction.span, "the NOP instruction takes no operands"));
            }

            Ok(SymbolicInstruction::Real(RealInstruction {
                opcode: RealOpCode::NoOperation,
                operand1: Register::R0,
                operand2: Default::default(),
            }))
        },
        OpCode::Real(opcode @ RealOpCode::PopRegisters)
            | OpCode::Real(opcode @ RealOpCode::PushRegisters)
            | OpCode::Real(opcode @ RealOpCode::Not) =>
        {
            if instruction.operands.len() != 1 {
                return Err(ParseError::new(
                    instruction.span,
                    "this instruction expects a single register operand",
                ));
            }

            let operand = &instruction.operands[0];

            if operand.index.is_some() || operand.mode.is_some() || !operand.base.is_register() {
                return Err(ParseError::new(
                    operand.span.clone(),
                    "the operand must be a register",
                ));
            }

            Ok(SymbolicInstruction::Real(RealInstruction {
                opcode,
                operand1: operand.base.register().unwrap(),
                operand2: Default::default(),
            }))
        },
        OpCode::Real(opcode @ RealOpCode::Jump { condition: JumpCondition::Unconditional, .. }) => {
            if instruction.operands.len() != 1 {
                return Err(ParseError::new(
                    instruction.span,
                    "jump instructions that examine the state register take only a single operand",
                ));
            }

            let operand = &instruction.operands[0];

            Ok(SymbolicInstruction::Real(RealInstruction {
                opcode,
                operand1: Register::R0,
                operand2: operand.into(),
            }))
        },
        OpCode::Real(opcode) => {
            if instruction.operands.len() != 2 {
                return Err(ParseError::new(
                    instruction.span,
                    "this instruction expects two operands",
                ));
            }

            let operand1 = &instruction.operands[0];
            let operand2 = &instruction.operands[1];

            if operand1.index.is_some() || operand1.mode.is_some() || !operand1.base.is_register() {
                return Err(ParseError::new(
                    operand1.span.clone(),
                    "the first operand to an instruction must be a register",
                ));
            }

            Ok(SymbolicInstruction::Real(RealInstruction {
                opcode,
                operand1: operand1.base.register().unwrap(),
                operand2: operand2.into(),
            }))
        },
    }
}


impl Program {
    pub fn parse(input: &str) -> Result<Program, ParseError<Context>> {
        let mut parser = Parser::from_str(input);
        let ast = parser.parse()?; 

        let instructions = ast.parts.into_iter()
            .map(|part| Ok(InstructionEntry {
                labels: part.labels,
                span: Some(part.instruction.span.clone()),
                instruction: validate_instruction(part.instruction)?,
            }))
            .collect::<Result<_, _>>()?;

        Ok(Program {
            symbol_table: parser.state.symbol_table,
            instructions,
        })
    }

    pub fn parse_verbose(input: &str) -> Result<Program, Vec<ParseError<Context>>> {
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

    pub fn compile(self) -> crate::bytecode::Program {
        use crate::compiler::compile;
        compile(self)
    }

    pub fn compile_sourcemap(self) -> SourceMap<crate::bytecode::Program> {
        crate::compiler::compile(self)
    }
}
