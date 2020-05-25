//! Tokens and a tokenizer for the symbolic formats.

use logos::{Lexer, Logos};

use std::fmt;

use super::ast::{JumpCondition, PseudoOpCode, RealOpCode, Register};

/// Enumeration of all tokens of the symbolic format.
#[derive(Logos, Debug, PartialEq, Clone)]
pub enum Token<'a> {
    /// Errorneous token that could not be interpreted as any of the other variants.
    #[error]
    #[regex(r"[ \n\t\r\f]", logos::skip)]
    #[regex(r";[^\n]*", logos::skip)]
    Error,

    /// A register. `R1`-`R7`, `SP` or `FP`.
    #[regex("R[1-7]|SP|FP", |lex| lex.slice().parse())]
    Register(Register),

    /// A symbol which begins with a letter and can contain the characters `A-Za-z0-9_`.
    #[regex("[A-Za-z][A-Za-z0-9_]*", Lexer::slice)]
    Symbol(&'a str),

    /// A real operator that has a bytecode representation.
    #[regex("(?i)nop|store|load|in|out|add|sub|mul|div|mod|and|or|xor|shl|shr|not|comp|call|exit|push|pop|pushr|popr|svc|jump|jzer|jnzer|jpos|jnpos|jneg|jnneg|jequ|jnequ|jles|jnles|jgre|jngre", operator_callback)]
    RealOperator(RealOpCode),

    /// A pseudo operator that is handled by the preprocessor or the compiler.
    #[regex("(?i)dc|ds|equ", pseudo_operator_callback)]
    PseudoOperator(PseudoOpCode),

    /// Token (`@`) that is used to specify that an operand uses the
    /// [Indirect](crate::instruction::Mode::Indirect) addressing mode.
    #[token("@")]
    IndirectModifier,

    /// Token (`=`) that is used to specify that an operand uses the
    /// [Immediate](crate::instruction::Mode::Immediate) addressing mode.
    #[token("=")]
    ImmediateModifier,

    /// Token (`,`) that is used to separate operands of a single instruction.
    #[token(",")]
    ParameterSeparator,

    /// Token (`(`) that is used in the index register construct that is part of an operand. (Eg.
    /// `ARR(R3)`).
    #[token("(")]
    IndexBegin,

    /// Token (`)`) that is used in the index register construct that is part of an operand. (Eg.
    /// `ARR(R3)`).
    #[token(")")]
    IndexEnd,

    /// A signed number literal.
    #[regex("-?[0-9]+", literal_callback)]
    Literal(i32),
}

fn pseudo_operator_callback<'a>(
    lex: &mut Lexer<'a, Token<'a>>,
) -> std::result::Result<PseudoOpCode, ()> {
    match lex.slice().to_uppercase().as_ref() {
        "DC" => Ok(PseudoOpCode::DC),
        "DS" => Ok(PseudoOpCode::DS),
        "EQU" => Ok(PseudoOpCode::EQU),
        _ => Err(()),
    }
}

fn operator_callback<'a>(lex: &mut Lexer<'a, Token<'a>>) -> std::result::Result<RealOpCode, ()> {
    let opcode = match lex.slice().to_uppercase().as_ref() {
        "NOP" => RealOpCode::NoOperation,
        "STORE" => RealOpCode::Store,
        "LOAD" => RealOpCode::Load,
        "IN" => RealOpCode::In,
        "OUT" => RealOpCode::Out,
        "ADD" => RealOpCode::Add,
        "SUB" => RealOpCode::Subtract,
        "MUL" => RealOpCode::Multiply,
        "DIV" => RealOpCode::Divide,
        "MOD" => RealOpCode::Modulo,
        "AND" => RealOpCode::And,
        "OR" => RealOpCode::Or,
        "XOR" => RealOpCode::Xor,
        "SHL" => RealOpCode::ShiftLeft,
        "SHR" => RealOpCode::ShiftRight,
        "NOT" => RealOpCode::Not,
        "COMP" => RealOpCode::Compare,
        "CALL" => RealOpCode::Call,
        "EXIT" => RealOpCode::Exit,
        "PUSH" => RealOpCode::Push,
        "POP" => RealOpCode::Pop,
        "PUSHR" => RealOpCode::PushRegisters,
        "POPR" => RealOpCode::PopRegisters,
        "SVC" => RealOpCode::SupervisorCall,
        "JUMP" => RealOpCode::Jump {
            negated: false,
            condition: JumpCondition::Unconditional,
        },
        "JZER" => RealOpCode::Jump {
            negated: false,
            condition: JumpCondition::Zero,
        },
        "JNZER" => RealOpCode::Jump {
            negated: true,
            condition: JumpCondition::Zero,
        },
        "JPOS" => RealOpCode::Jump {
            negated: false,
            condition: JumpCondition::Positive,
        },
        "JNPOS" => RealOpCode::Jump {
            negated: true,
            condition: JumpCondition::Positive,
        },
        "JNEG" => RealOpCode::Jump {
            negated: false,
            condition: JumpCondition::Negative,
        },
        "JNNEG" => RealOpCode::Jump {
            negated: true,
            condition: JumpCondition::Negative,
        },
        "JEQU" => RealOpCode::Jump {
            negated: false,
            condition: JumpCondition::Equal,
        },
        "JNEQU" => RealOpCode::Jump {
            negated: true,
            condition: JumpCondition::Equal,
        },
        "JLES" => RealOpCode::Jump {
            negated: false,
            condition: JumpCondition::Less,
        },
        "JNLES" => RealOpCode::Jump {
            negated: true,
            condition: JumpCondition::Less,
        },
        "JGRE" => RealOpCode::Jump {
            negated: false,
            condition: JumpCondition::Greater,
        },
        "JNGRE" => RealOpCode::Jump {
            negated: true,
            condition: JumpCondition::Greater,
        },
        _ => return Err(()),
    };

    Ok(opcode)
}

fn literal_callback<'a>(
    lex: &mut Lexer<'a, Token<'a>>,
) -> std::result::Result<i32, std::num::ParseIntError> {
    lex.slice().parse()
}

impl<'t> fmt::Display for Token<'t> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Token::Error => write!(f, "<error>"),
            Token::Literal(num) => write!(f, "{}", num),
            Token::Symbol(label) => write!(f, "{}", label),
            Token::IndexBegin => write!(f, "("),
            Token::IndexEnd => write!(f, ")"),
            Token::ParameterSeparator => write!(f, ","),
            Token::ImmediateModifier => write!(f, "="),
            Token::IndirectModifier => write!(f, "@"),
            Token::Register(reg) => write!(f, "{}", reg),
            Token::RealOperator(op) => write!(f, "{}", op),
            Token::PseudoOperator(op) => write!(f, "{}", op),
        }
    }
}
