use logos::{Logos, Lexer};

use super::ast::{
    Register,
    RealOpCode,
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
    RealOperator(RealOpCode),

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

fn operator_callback<'a>(lex: &mut Lexer<'a, Token<'a>>) -> std::result::Result<RealOpCode, ()> {
    let opcode = match lex.slice().to_uppercase().as_ref() {
        "NOP"   => RealOpCode::NoOperation,
        "STORE" => RealOpCode::Store,
        "LOAD"  => RealOpCode::Load,
        "IN"    => RealOpCode::In,
        "OUT"   => RealOpCode::Out,
        "ADD"   => RealOpCode::Add,
        "SUB"   => RealOpCode::Subtract,
        "MUL"   => RealOpCode::Multiply,
        "DIV"   => RealOpCode::Divide,
        "MOD"   => RealOpCode::Modulo,
        "AND"   => RealOpCode::And,
        "OR"    => RealOpCode::Or,
        "XOR"   => RealOpCode::Xor,
        "SHL"   => RealOpCode::ShiftLeft,
        "SHR"   => RealOpCode::ShiftRight,
        "NOT"   => RealOpCode::Not,
        "COMP"  => RealOpCode::Compare,
        "CALL"  => RealOpCode::Call,
        "EXIT"  => RealOpCode::Exit,
        "PUSH"  => RealOpCode::Push,
        "POP"   => RealOpCode::Pop,
        "PUSHR" => RealOpCode::PushRegisters,
        "POPR"  => RealOpCode::PopRegisters,
        "SVC"   => RealOpCode::SupervisorCall,
        "JUMP"  => RealOpCode::Jump { negated: false, condition: JumpCondition::Unconditional },
        "JZER"  => RealOpCode::Jump { negated: false, condition: JumpCondition::Zero },
        "JNZER" => RealOpCode::Jump { negated: true,  condition: JumpCondition::Zero },
        "JPOS"  => RealOpCode::Jump { negated: false, condition: JumpCondition::Positive },
        "JNPOS" => RealOpCode::Jump { negated: true,  condition: JumpCondition::Positive },
        "JNEG"  => RealOpCode::Jump { negated: false, condition: JumpCondition::Negative },
        "JNNEG" => RealOpCode::Jump { negated: true,  condition: JumpCondition::Negative },
        "JEQU"  => RealOpCode::Jump { negated: false, condition: JumpCondition::Equal },
        "JNEQU" => RealOpCode::Jump { negated: true,  condition: JumpCondition::Equal },
        "JLES"  => RealOpCode::Jump { negated: false, condition: JumpCondition::Less },
        "JNLES" => RealOpCode::Jump { negated: true,  condition: JumpCondition::Less },
        "JGRE"  => RealOpCode::Jump { negated: false, condition: JumpCondition::Greater },
        "JNGRE" => RealOpCode::Jump { negated: true,  condition: JumpCondition::Greater },
        _ => return Err(()),
    };

    Ok(opcode)
}

fn literal_callback<'a>(lex: &mut Lexer<'a, Token<'a>>) -> std::result::Result<i32, std::num::ParseIntError> {
    lex.slice().parse()
}
