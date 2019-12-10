//! Functions for parsing symbolic assembly programs from strings.
//!
//! The only function you problaly are interested in here is [parse_symbolic_file], which
//! you probably want to use via [Program::parse](crate::symbolic::Program::parse).

use nom::{
    branch::alt,
    bytes::complete::{take_while1, take_while, take_till, tag},
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
    PseudoInstruction,
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

/// An error which has prevented the input from being parsed successfully.
pub type ParseError = crate::error::ParseError<ErrorKind>;
type Result<'a,R> = IResult<&'a str, R, ParseError>;

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
                        take_while1(|c: char| c.is_digit(16)),
                    ),
                    |n| i32::from_str_radix(n, 16)
                ),
                map_res(
                    take_while1(|c: char| c.is_digit(10)),
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
const NEWLINE_CHARACTERS: &'static str = "\r\n";

fn sp(input: &str) -> Result<&str> {
    take_while1(|c| SPACE_CHARACTERS.contains(c))(input)
}

fn newline(input: &str) -> Result<&str> {
    take_while1(|c| NEWLINE_CHARACTERS.contains(c))(input)
}

fn take_label(input: &str) -> Result<&str> {
    take_while(char::is_alphanumeric)(input)
}

/*fn pseudo_opcode(input: &str) -> Result<PseudoInstructionKind> {
    preceded(
        sp,
        alt((
            value(PseudoInstructionKind::EQU, tag("EQU")),
            value(PseudoInstructionKind::DC,  tag("DC"))
        )),
    )(input)
}*/

fn take_pseudo_instruction(input: &str) -> Result<PseudoInstruction> {
    //let (input, label) = take_label(input)?;
    //let (input, _) = opt(sp)(input)?;

    let parse_value = map(take_i32, |x| (1, x));
    let parse_size  = map(take_i32, |x| (x as u16, 0));

    println!("TPI>> {}", input);

    let (input, (_kind, (size, value))) = alt((
            separated_pair(tag("EQU"), sp, &parse_value),
            separated_pair(tag("DC"),  sp, &parse_value),
            separated_pair(tag("DS"),  sp, &parse_size),
    ))(input)?;

    Ok((input, PseudoInstruction {
        size,
        value,
    }))
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

fn take_concrete_opcode(input: &str) -> Result<OpCode> {
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

/// Parse a register keyword.
fn register(input: &str) -> Result<Register> {
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

impl std::str::FromStr for Register {
    type Err = ();

    fn from_str(input: &str) -> StdResult<Register, ()> {
        match input {
            "R1" => Ok(Register::R1),
            "R2" => Ok(Register::R2),
            "R3" => Ok(Register::R3),
            "R4" => Ok(Register::R4),
            "R5" => Ok(Register::R5),
            "R6" => Ok(Register::R6),
            "R7" => Ok(Register::R7),
            "SP" => Ok(Register::R7),
            _ => Err(()),
        }
    }
}

fn operand1(input: &str) -> Result<Register> {
    register(input)
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
                opt(sp),
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
    map(
        tuple((
            take_concrete_opcode,
            sp,
            opt(terminated(
                operand1,
                tuple((
                    opt(sp),
                    tag(","),
                    opt(sp),
                )),
            )),
            operand2,
        )),
        |tuple| {
            ConcreteInstruction {
                label: None,
                opcode: tuple.0,
                operand1: tuple.2.unwrap_or(Register::R0),
                operand2: tuple.3,
            }
        }
    )(input)
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
        take_till(|c| NEWLINE_CHARACTERS.contains(c)),
    )(input)
}

/// Parse a single line of assembly.
fn take_line(input: &str) -> Result<Option<(Option<&str>, SymbolicInstruction)>> {
    preceded(
        opt(sp),
        terminated(
            opt(alt((
                map(
                    separated_pair(take_label, sp, take_instruction),
                    |(label, ins)| (Some(label), ins),
                ),
                map(take_instruction, |ins| (None, ins)),
            ))),
            opt(preceded(opt(sp), take_comment)),
        ),
    )(input)
}

fn fold_program(
    mut program: Program,
    line: Option<(Option<&str>, SymbolicInstruction)>,
) -> Program { 
    match line {
        Some((label, SymbolicInstruction::Pseudo(ins))) => {
            let label = label.map(str::to_string);
            program.init_table.push((label, ins));
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

/// Parse a single line of assembly.
pub fn parse_line(input: &str)
    -> StdResult<Option<(Option<&str>, SymbolicInstruction)>, ParseError>
{
    all_consuming(take_line)(input)
        .map(|(_input, result)| result)
        .map_err(flatten_error)
}

/// Parse an entire assembly program.
fn take_symbolic_file(input: &str) -> Result<Program> {
    map(
        tuple((
            fold_many0(
                terminated(take_line, newline),
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

/// Parse an entier assembly program.
///
/// You propably want to use this via [Program::parse](crate::symbolic::Program::parse).
pub fn parse_symbolic_file(input: &str) -> StdResult<Program, ParseError> {
    all_consuming(take_symbolic_file)(input)
        .map(|(_input, result)| result)
        .map_err(flatten_error)
}
