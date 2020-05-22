use logos::{Logos, Lexer};

use super::ast::{
    Register,
    OpCode,
    PseudoOpCode,
    JumpCondition,
};

#[derive(Logos, Debug, PartialEq, Clone)]
pub enum Token<'a> {
    #[error]
    #[regex(r"[ \n\t\r\f]", logos::skip)]
    #[regex(r";[^\n]*", logos::skip)]
    Error,

    #[regex("R[1-7]|SP|FP", |lex| lex.slice().parse())]
    Register(Register),

    #[regex("[A-Za-z][A-Za-z0-9_]*", Lexer::slice)]
    Symbol(&'a str),

    #[regex("(?i)nop|store|load|in|out|add|sub|mul|div|mod|and|or|xor|shl|shr|not|comp|call|exit|push|pop|pushr|popr|svc|jump|jzer|jnzer|jpos|jnpos|jneg|jnneg|jequ|jnequ|jles|jnles|jgre|jngre", operator_callback)]
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

fn literal_callback<'a>(lex: &mut Lexer<'a, Token<'a>>) -> std::result::Result<i32, std::num::ParseIntError> {
    lex.slice().parse()
}
