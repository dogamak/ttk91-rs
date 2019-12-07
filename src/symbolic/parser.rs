use nom::{
    alt,
    branch::alt,
    bytes::complete::{take_while, take_until, tag},
    combinator::{value, map, opt, map_res, all_consuming},
    error::context,
    IResult,
    multi::{fold_many0},
    sequence::{preceded, tuple, separated_pair, delimited, terminated},
};

use crate::instruction::{
    JumpCondition,
    Mode,
    OpCode,
    Register,
};

use super::program::{
    ConcreteInstruction,
    InitializationTableEntry,
    Program,
    SecondOperand,
    SymbolicInstruction,
    Value,
};

use std::fmt;
use std::result::Result as StdResult;

#[derive(Debug, Clone)]
pub enum ErrorKind {
    OpCode(String),
}

pub type ParseError = crate::error::ParseError<ErrorKind>;
pub type Result<'a,R> = IResult<&'a str, R, ParseError>;

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ErrorKind::OpCode(op) => write!(f, "invalid opcode '{}'", op),
        }
    }
}


fn take_i32(input: &str) -> Result<i32> {
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

fn sp(input: &str) -> Result<&str> {
    take_while(|c| SPACE_CHARACTERS.contains(c))(input)
}

fn newline(input: &str) -> Result<&str> {
    take_while(|c| NEWLINE_CHARACTERS.contains(c))(input)
}

fn take_label(input: &str) -> Result<&str> {
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

fn pseudo_opcode(input: &str) -> Result<PseudoInstructionKind> {
    preceded(
        sp,
        alt((
            value(PseudoInstructionKind::EQU, tag("EQU")),
            value(PseudoInstructionKind::DC,  tag("DC"))
        )),
    )(input)
}

fn take_pseudo_instruction(input: &str) -> Result<InitializationTableEntry> {
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
        |input: &str| -> Result<OpCode> {
            let mut err;

            $(match $parser(input) {
                Ok((i, o)) => return Ok((i, o)),
                Err(e) => err = e,
            })*

            Err(err)
        }
    };
}

fn jump_instruction(input: &str) -> Result<OpCode> {
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

fn _take_opcode(input: &str) -> Result<OpCode> {
    let orig_input = input;

    let (input, opcode) = take_while(|c: char| !c.is_whitespace())(input)?;

    let opcode = match opcode {
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

        _ => {
            let kind = ErrorKind::OpCode(opcode.to_string());
            let err = ParseError::from_kind(orig_input.to_string(), kind);
            return Err(nom::Err::Error(err));
        },
    };

    Ok((input, opcode))
}

fn take_concrete_opcode(input: &str) -> Result<OpCode> {
    let (input, _) = sp(input)?;

    preceded(sp, context("opcode", _take_opcode))(input)

    /*
                value(OpCode::ArithmeticShiftRight, tag("ASHR")),
                jump_instruction,
            )
        ))(input)*/
}

pub fn register(input: &str) -> Result<Register> {
    context("register",
        alt((
            value(Register::R1, tag("R1")),
            value(Register::R2, tag("R2")),
            value(Register::R3, tag("R3")),
            value(Register::R4, tag("R4")),
            value(Register::R5, tag("R5")),
            value(Register::R6, tag("R6")),
            value(Register::R7, tag("R7")),
            value(Register::R7, tag("SP")),
        )))(input)
}

fn operand1(input: &str) -> Result<Register> {
    preceded(
        sp,
        register,
    )(input)
}


fn operand_value(input: &str) -> Result<Value> {
    alt((
        map(take_i32, |n| Value::Immediate(n as u16)),
        map(register, Value::Register),
        map(take_label, |s| Value::Symbol(s.to_string())),
    ))(input)
}

fn with_mode(mode: Mode) -> impl Fn(Value) -> SecondOperand {
    move |value| SecondOperand { mode, value, index: None }
}

fn immediate_operand(input: &str) -> Result<SecondOperand> {
    map(preceded(tag("="), operand_value), with_mode(Mode::Immediate))(input)
}

fn indirect_operand(input: &str) -> Result<SecondOperand> {
    map(preceded(tag("@"), operand_value), with_mode(Mode::Indirect))(input)
}

fn direct_operand(input: &str) -> Result<SecondOperand> {
    map(operand_value, with_mode(Mode::Direct))(input)
}

fn operand2(input: &str) -> Result<SecondOperand> {
    context("second operand",
        map(
            separated_pair(
                alt((
                    immediate_operand,
                    indirect_operand,
                    direct_operand,
                )),
                sp,
                context("index part of the second operand", opt(delimited(
                    tag("("),
                    register,
                    tag(")"),
                ))),
            ),
            |(mut operand, index)| {
                operand.index = index;
                operand
            }
        ))(input)
}

fn take_concrete_instruction(input: &str) -> Result<ConcreteInstruction> {
    let (input, opcode) = take_concrete_opcode(input)?;

    let (input, operand1) = operand1(input)?;
    let (input, _) = preceded(sp, tag(","))(input)?;
    let (input, operand2) = preceded(sp, operand2)(input)?;

    //let (input, _) = preceded(sp, newline)(input)?;

    Ok((input, ConcreteInstruction {
        label: None,
        opcode: opcode,
        operand1,
        operand2,
    }))
}

fn take_instruction(input: &str) -> Result<SymbolicInstruction> {
    alt((
        map(take_concrete_instruction, SymbolicInstruction::Concrete),
        map(take_pseudo_instruction, SymbolicInstruction::Pseudo),
    ))(input)
}

fn take_comment(input: &str) -> Result<&str> {
    preceded(
        tag(";"),
        take_while(|c| !NEWLINE_CHARACTERS.contains(c)),
    )(input)
}

pub fn take_line(input: &str) -> Result<Option<(Option<&str>, SymbolicInstruction)>> {
    preceded(
        sp,
        terminated(
            opt(alt((
                map(separated_pair(take_label, sp, take_instruction), |(label, ins)| (Some(label), ins)),
                map(take_instruction, |ins| (None, ins)),
            ))),
            opt(take_comment),
        ),
    )(input)
}

fn fold_program(
    mut program: Program,
    line: Option<(Option<&str>, SymbolicInstruction)>,
) -> Program { 
    match line {
        Some((_label, SymbolicInstruction::Pseudo(ins))) => {
            program.init_table.push(ins);
        },
        Some((label, SymbolicInstruction::Concrete(ins))) => {
            let label = label.map(str::to_string);
            program.instructions.push((label, ins));
        },
        None => (),
    }

    program
}

fn flatten_error(err: nom::Err<ParseError>) -> ParseError {
    match err {
        nom::Err::Failure(err) => err,
        nom::Err::Error(err) => err,
        nom::Err::Incomplete(_) => ParseError::incomplete(),
    }
}

pub fn parse_line(input: &str)
    -> StdResult<Option<(Option<&str>, SymbolicInstruction)>, ParseError>
{
    all_consuming(take_line)(input)
        .map(|(_input, result)| result)
        .map_err(flatten_error)
}

pub fn take_symbolic_file(input: &str) -> Result<Program> {
    map(
        tuple((
            fold_many0(
                take_line,
                Program::default(),
                fold_program,
            ),
            opt(take_line),
        )),
        |(prog, line)| match line {
            None => prog,
            Some(line) => fold_program(prog, line),
        },
    )(input)
}

pub fn parse_symbolic_file(input: &str) -> StdResult<Program, ParseError> {
    all_consuming(take_symbolic_file)(input)
        .map(|(_input, result)| result)
        .map_err(flatten_error)
}
