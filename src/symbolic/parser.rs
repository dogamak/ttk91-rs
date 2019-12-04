use nom::{
    IResult,
    bytes::complete::{take_while, take_until, tag},
    branch::alt,
    combinator::{value, map, opt, map_res},
    multi::{fold_many0},
    sequence::{preceded, tuple, separated_pair, delimited},
    alt,
};

use crate::instruction::{
    Mode,
    Register,
    OpCode,
    JumpCondition,
};

use super::program::{
    ConcreteInstruction,
    InitializationTableEntry,
    Program,
    SecondOperand,
    SymbolicInstruction,
    Value,
};

fn take_i32(input: &str) -> IResult<&str, i32> {
    map(
        tuple((
            opt(alt((tag("+"), tag("-")))),
            alt((
                map_res(
                    preceded(
                        tag("0x"),
                        take_while(|c: char| c.is_digit(16)),
                    ),
                    |n| i32::from_str_radix(n, 16)
                ),
                map_res(
                    take_while(|c: char| c.is_digit(10)),
                    |n| i32::from_str_radix(n, 10)
                ),
            )),
        )),
        |(sign, number)| match sign {
            Some("-") => -number,
            Some(_) | None => number,
        }
    )(input)
}

const SPACE_CHARACTERS: &'static str = " \t";
const NEWLINE_CHARACTERS: &'static str = "\r\t";

fn sp(input: &str) -> IResult<&str, &str> {
    take_while(|c| SPACE_CHARACTERS.contains(c))(input)
}

fn newline(input: &str) -> IResult<&str, &str> {
    take_while(|c| NEWLINE_CHARACTERS.contains(c))(input)
}

fn take_label(input: &str) -> IResult<&str, &str> {
    preceded(sp, take_while(char::is_alphanumeric))(input)
}

#[derive(Debug, Clone)]
pub struct PseudoInstruction {
    label: String,
    kind: PseudoInstructionKind,
    value: i32,
}

#[derive(Debug, Clone, Copy)]
pub enum PseudoInstructionKind {
    EQU,
    DC,
}

fn pseudo_opcode(input: &str) -> IResult<&str, PseudoInstructionKind> {
    preceded(
        sp,
        alt((
            value(PseudoInstructionKind::EQU, tag("EQU")),
            value(PseudoInstructionKind::DC,  tag("DC"))
        )),
    )(input)
}

fn take_pseudo_instruction(input: &str) -> IResult<&str, InitializationTableEntry> {
    let (input, label) = take_label(input)?;

    let (input, _) = sp(input)?;

    let parse_value = map(take_i32, |x| (1, x));
    let parse_size  = map(take_i32, |x| (x as u16, 0));

    let (input, (_kind, (size, value))) = alt((
            separated_pair(tag("EQU"), sp, &parse_value),
            separated_pair(tag("DC"),  sp, &parse_value),
            separated_pair(tag("DS"),  sp, &parse_size),
    ))(input)?;

    Ok((input, InitializationTableEntry {
        symbol: label.to_string(),
        size,
        value: value as i32,
    }))
}



macro_rules! alt {
    ( $($parser:expr),* $(,)* ) => {
        |input: &str| -> IResult<&str, OpCode> {
            let mut err;

            $(match $parser(input) {
                Ok((i, o)) => return Ok((i, o)),
                Err(e) => err = e,
            })*

            Err(err)
        }
    };
}

fn jump_instruction(input: &str) -> IResult<&str, OpCode> {
    let (input, _) = tag("J")(input)?;
    let (input, negated) = map(opt(tag("N")), |o| o.is_some())(input)?;

    use JumpCondition::*;

    let (input, condition) = alt((
            value(Zero,     tag("ZER")),
            value(Negative, tag("NEG")),
            value(Positive, tag("POS")),
            value(Less,     tag("LES")),
            value(Greater,  tag("GRE")),
            value(Equal,    tag("EQU")),
    ))(input)?;

    Ok((input, OpCode::Jump { negated, condition }))
}

fn take_concrete_opcode(input: &str) -> IResult<&str, OpCode> {
    let (input, _) = sp(input)?;

    preceded(
        sp,
        alt!(
            value(OpCode::NoOperation,    tag("NOP")),
            value(OpCode::Store,          tag("STORE")),
            value(OpCode::Load,           tag("LOAD")),
            value(OpCode::In,             tag("IN")),
            value(OpCode::Out,            tag("OUT")),
            value(OpCode::Add,            tag("ADD")),
            value(OpCode::Subtract,       tag("SUB")),
            value(OpCode::Multiply,       tag("MUL")),
            value(OpCode::Divide,         tag("DIV")),
            value(OpCode::Modulo,         tag("MOD")),
            value(OpCode::And,            tag("AND")),
            value(OpCode::Or,             tag("OR")),
            value(OpCode::Xor,            tag("XOR")),
            value(OpCode::ShiftLeft,      tag("SHL")),
            value(OpCode::ShiftRight,     tag("SHR")),
            value(OpCode::Not,            tag("NOT")),
            value(OpCode::Compare,        tag("COMP")),
            value(OpCode::Call,           tag("CALL")),
            value(OpCode::Exit,           tag("EXIT")),
            value(OpCode::Push,           tag("PUSH")),
            value(OpCode::Pop,            tag("POP")),
            value(OpCode::PushRegisters,  tag("PUSHR")),
            value(OpCode::PopRegisters,   tag("POPR")),
            value(OpCode::SupervisorCall, tag("SVC")),
            value(OpCode::ArithmeticShiftRight, tag("ASHR")),
            jump_instruction,
        )
    )(input)
}

pub fn register(input: &str) -> IResult<&str, Register> {
    alt((
        value(Register::R1, tag("R1")),
        value(Register::R2, tag("R2")),
        value(Register::R3, tag("R3")),
        value(Register::R4, tag("R4")),
        value(Register::R5, tag("R5")),
        value(Register::R6, tag("R6")),
        value(Register::R7, tag("R7")),
        value(Register::R7, tag("SP")),
    ))(input)
}

fn operand1(input: &str) -> IResult<&str, Register> {
    preceded(
        sp,
        register,
    )(input)
}


fn operand_value(input: &str) -> IResult<&str, Value> {
    alt((
        map(take_i32, |n| Value::Immediate(n as u16)),
        map(register, Value::Register),
        map(take_label, |s| Value::Symbol(s.to_string())),
    ))(input)
}

fn with_mode(mode: Mode) -> impl Fn(Value) -> SecondOperand {
    move |value| SecondOperand { mode, value, index: None }
}

fn immediate_operand(input: &str) -> IResult<&str, SecondOperand> {
    map(preceded(tag("="), operand_value), with_mode(Mode::Immediate))(input)
}

fn indirect_operand(input: &str) -> IResult<&str, SecondOperand> {
    map(preceded(tag("@"), operand_value), with_mode(Mode::Indirect))(input)
}

fn direct_operand(input: &str) -> IResult<&str, SecondOperand> {
    map(operand_value, with_mode(Mode::Direct))(input)
}

fn operand2(input: &str) -> IResult<&str, SecondOperand> {
    map(
        separated_pair(
            alt((
                immediate_operand,
                indirect_operand,
                direct_operand,
            )),
            sp,
            opt(delimited(
                tag("("),
                register,
                tag(")"),
            )),
        ),
        |(mut operand, index)| {
            operand.index = index;
            operand
        }
    )(input)
}

fn _take_concrete_instruction(input: &str) -> IResult<&str, ConcreteInstruction> {
    let (input, opcode) = take_concrete_opcode(input)?;

    let (input, operand1) = operand1(input)?;
    let (input, _) = preceded(sp, tag(","))(input)?;
    let (input, operand2) = preceded(sp, operand2)(input)?;

    let (input, _) = preceded(sp, newline)(input)?;

    Ok((input, ConcreteInstruction {
        label: None,
        opcode: opcode,
        operand1,
        operand2,
    }))
}

fn take_concrete_instruction(input: &str) -> IResult<&str, (Option<&str>, ConcreteInstruction)> {
    alt((
        map(tuple((take_label, _take_concrete_instruction)), |(l,i)| (Some(l), i)),
        map(_take_concrete_instruction, |i| (None, i)),
    ))(input)
}

pub fn parse_line(input: &str) -> IResult<&str, Option<SymbolicInstruction>> {
    let (input, ins) = alt((
        map(take_pseudo_instruction,   |i|      Some(SymbolicInstruction::Pseudo(i))),
        map(take_concrete_instruction, |(_l,i)| Some(SymbolicInstruction::Concrete(i))),
        value(None, tuple((
                take_while(char::is_whitespace),
                tag(";"),
                take_until("\n"),
        ))),
        value(None, sp),
    ))(input)?;

    let (input, _) = tag("\n")(input)?;

    Ok((input, ins))
}

pub fn parse_symbolic_file(input: &str) -> IResult<&str, Program> {
    fold_many0(
        parse_line,
        Program::default(),
        |mut p, ins| {
            match ins {
                Some(SymbolicInstruction::Pseudo(ins)) => p.init_table.push(ins),
                Some(SymbolicInstruction::Concrete(ins)) => p.instructions.push(ins),
                None => (),
            }

            p
        },
    )(input)
}
