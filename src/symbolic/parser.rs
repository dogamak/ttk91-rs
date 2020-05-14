//! Functions for parsing symbolic assembly programs from strings.
//!
//! The only function you problaly are interested in here is [parse_symbolic_file], which
//! you probably want to use via [Program::parse](crate::symbolic::Program::parse).

use logos::{Logos, Lexer};

use nom::IResult;

use crate::instruction::{
    JumpCondition,
    Mode,
    OpCode,
    Register,
};

use super::program::{
    ConcreteInstruction,
    PseudoInstruction,
    PseudoOpCode,
    InstructionEntry,
    Program,
    SecondOperand,
    SymbolicInstruction,
    Value,
};

use std::fmt;
use std::result::Result as StdResult;

/// Represents error conditions specific to symbolic assembly parsing.
#[derive(Debug, Clone)]
pub enum ErrorKind {
    OpCode(String),
}

type Span<'a> = nom_locate::LocatedSpan<&'a str>;

/// An error which has prevented the input from being parsed successfully.
pub type ParseError = crate::error::ParseError<ErrorKind>;
type Result<'a,R> = IResult<Span<'a>, R, ParseError>;

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ErrorKind::OpCode(op) => write!(f, "invalid opcode '{}'", op),
        }
    }
}

#[derive(Logos, Debug, PartialEq)]
pub enum Token<'a> {
    #[error]
    #[regex(r"[ \t\n\f]", logos::skip)]
    #[regex(r";.*\n", logos::skip)]
    Error,

    #[regex("R[1-7]|SP|FP", register_callback)]
    Register(Register),

    #[regex("[A-Za-z][A-Za-z0-9_]*", Lexer::slice)]
    Symbol(&'a str),

    #[regex("(?i)load|store|in|jzer|add|jump|out|svc", operator_callback)]
    Operator(OpCode),

    #[regex("(?i)dc|ds|equ", pseudo_operator_callback)]
    PseudoOperator(PseudoOpCode),

    #[token("@")]
    IndirectModifier,

    #[token("=")]
    ImmediateModifier,

    #[token(",")]
    ParameterSeparator,

    #[token("(")]
    IndexBegin,

    #[token(")")]
    IndexEnd,

    #[regex("-?[0-9]+", literal_callback)]
    Literal(i32),
}

fn pseudo_operator_callback<'a>(lex: &mut Lexer<'a, Token<'a>>) -> std::result::Result<PseudoOpCode, ()> {
    match lex.slice().to_uppercase().as_ref() {
        "DC" => Ok(PseudoOpCode::DC),
        "DS" => Ok(PseudoOpCode::DS),
        "EQU" => Ok(PseudoOpCode::EQU),
        _ => Err(()),
    }
}

fn operator_callback<'a>(lex: &mut Lexer<'a, Token<'a>>) -> std::result::Result<OpCode, ()> {
    let opcode = match lex.slice().to_uppercase().as_ref() {
        "NOP"   => OpCode::NoOperation,
        "STORE" => OpCode::Store,
        "LOAD"  => OpCode::Load,
        "IN"    => OpCode::In,
        "OUT"   => OpCode::Out,
        "ADD"   => OpCode::Add,
        "SUB"   => OpCode::Subtract,
        "MUL"   => OpCode::Multiply,
        "DIV"   => OpCode::Divide,
        "MOD"   => OpCode::Modulo,
        "AND"   => OpCode::And,
        "OR"    => OpCode::Or,
        "XOR"   => OpCode::Xor,
        "SHL"   => OpCode::ShiftLeft,
        "SHR"   => OpCode::ShiftRight,
        "NOT"   => OpCode::Not,
        "COMP"  => OpCode::Compare,
        "CALL"  => OpCode::Call,
        "EXIT"  => OpCode::Exit,
        "PUSH"  => OpCode::Push,
        "POP"   => OpCode::Pop,
        "PUSHR" => OpCode::PushRegisters,
        "POPR"  => OpCode::PopRegisters,
        "SVC"   => OpCode::SupervisorCall,
        "JUMP"  => OpCode::Jump { negated: false, condition: JumpCondition::Unconditional },
        "JZER"  => OpCode::Jump { negated: false, condition: JumpCondition::Zero },
        "JNZER" => OpCode::Jump { negated: true,  condition: JumpCondition::Zero },
        "JPOS"  => OpCode::Jump { negated: false, condition: JumpCondition::Positive },
        "JNPOS" => OpCode::Jump { negated: true,  condition: JumpCondition::Positive },
        "JNEG"  => OpCode::Jump { negated: false, condition: JumpCondition::Negative },
        "JNNEG" => OpCode::Jump { negated: true,  condition: JumpCondition::Negative },
        "JEQU"  => OpCode::Jump { negated: false, condition: JumpCondition::Equal },
        "JNEQU" => OpCode::Jump { negated: true,  condition: JumpCondition::Equal },
        "JLES"  => OpCode::Jump { negated: false, condition: JumpCondition::Less },
        "JNLES" => OpCode::Jump { negated: true,  condition: JumpCondition::Less },
        "JGRE"  => OpCode::Jump { negated: false, condition: JumpCondition::Greater },
        "JNGRE" => OpCode::Jump { negated: true,  condition: JumpCondition::Greater },
        _ => return Err(()),
    };

    Ok(opcode)
}

fn register_callback<'a>(lex: &mut Lexer<'a, Token<'a>>) -> std::result::Result<Register, ()> {
    match lex.slice() {
        "R1" => Ok(Register::R1),
        "R2" => Ok(Register::R2),
        "R3" => Ok(Register::R3),
        "R4" => Ok(Register::R4),
        "R5" => Ok(Register::R5),
        "R6" => Ok(Register::R6),
        "R7" | "SP" => Ok(Register::R7),
        _ => Err(()),
    } 
}

fn literal_callback<'a>(lex: &mut Lexer<'a, Token<'a>>) -> std::result::Result<i32, std::num::ParseIntError> {
    lex.slice().parse()
}

/// Parse a single line of assembly.
pub fn parse_line(input: &str)
    -> StdResult<Option<(Option<&str>, SymbolicInstruction)>, ParseError>
{
    unimplemented!()
}

/// Parse an entire assembly program.
fn take_symbolic_file(input: Span) -> Result<Program> {
    unimplemented!()
}

/// Parse an entier assembly program.
///
/// You propably want to use this via [Program::parse](crate::symbolic::Program::parse).
pub fn parse_symbolic_file(input: &str) -> StdResult<Program, ParseError> {
    unimplemented!()
}
