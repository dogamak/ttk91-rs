use nom::{
    alt,
    branch::alt,
    bytes::complete::{take_while, take_until, tag},
    combinator::{value, map, opt, map_res},
    error::{context, ErrorKind},
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

#[derive(Debug, Clone)]
pub enum Kind {
    Context(&'static str),
    Nom(ErrorKind),
    OpCode(String),
    Incomplete,
}

impl fmt::Display for Kind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Kind::Context(ctx) => write!(f, "invalid {}", ctx),
            Kind::Nom(ctx) => write!(f, "unexpected input"),
            Kind::OpCode(op) => write!(f, "invalid opcode '{}'", op),
            Kind::Incomplete => write!(f, "expected more input"),
        }
    }
}

#[derive(Clone, Debug)]
pub struct ParseError {
    stack: Vec<(String, Kind)>,
}

impl ParseError {
    pub(crate) fn incomplete() -> ParseError {
        ParseError {
            stack: vec![(String::new(), Kind::Incomplete)],
        }
    }
}

#[derive(Clone, Debug)]
pub struct VerboseParseError<'a> {
    pub line: usize,
    pub column: usize,
    kind: Kind,
    rest: &'a str,
}

impl<'a> fmt::Display for VerboseParseError<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "at line {} col {}: {}, at '{}'", self.line, self.column, self.kind, self.rest)
    }
}

impl ParseError {
    pub fn verbose(self, input: &str) -> VerboseParseError {
        for (rest, kind) in self.stack {
            let mut line = 1;
            let mut column = 1;

            for ch in input[..rest.len()].chars() {
                if ch == '\n' {
                    line += 1;
                    column = 0;
                }

                column += 1;
            }

            let start = input.len() - rest.len();
            let mut end = start;

            //while end < input.len() && end - start < 20 && &input[end] != '\n' {
            for ch in input[start..].chars() {
                if ch == '\n' {
                    break;
                }

                if end - start > 20 {
                    break;
                }

                end += 1;
            }

            let rest = &input[start..end];

            return VerboseParseError {
                line,
                column,
                kind,
                rest,
            };
            //eprintln!(" at line {} col {}: {}", line, col, error);
        }

        unreachable!();
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (input, kind) = &self.stack[0];

        let end = input
            .chars()
            .enumerate()
            .find_map(|(i, c)| match c {
                '\n' => Some(i),
                _ => None,
            })
            .unwrap_or(20);

        let end = std::cmp::min(end, 20);

        write!(f, "{} at: {}", kind, &input[..end])
    }
}

impl nom::error::ParseError<&str> for ParseError {
    fn from_error_kind(input: &str, kind: ErrorKind) -> ParseError {
        ParseError {
            stack: vec![(input.to_string(), Kind::Nom(kind))],
        }
    }

    fn append(input: &str, kind: ErrorKind, mut other: ParseError) -> ParseError {
        other.stack.push((input.to_string(), Kind::Nom(kind)));
        other
    }

    fn add_context(input: &str, ctx: &'static str, mut other: ParseError) -> ParseError {
        other.stack.push((input.to_string(), Kind::Context(ctx)));
        other
    }
}

pub type Result<'a,R> = IResult<&'a str, R, ParseError>;

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

        _ => return Err(nom::Err::Error(ParseError {
            stack: vec![(orig_input.to_string(), Kind::OpCode(opcode.to_string()))],
        })),
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

fn _take_concrete_instruction(input: &str) -> Result<ConcreteInstruction> {
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

fn take_concrete_instruction(input: &str) -> Result<(Option<&str>, ConcreteInstruction)> {
    alt((
        map(tuple((take_label, _take_concrete_instruction)), |(l,i)| (Some(l), i)),
        map(_take_concrete_instruction, |i| (None, i)),
    ))(input)
}

pub fn parse_line(input: &str) -> Result<Option<SymbolicInstruction>> {
    let (input, _) = sp(input)?;

    map(
        terminated(
            opt(
                alt((
                    value(None, tuple((
                            tag(";"),
                            take_until("\n"),
                    ))),
                    map(
                        context("pseudo instruction", take_pseudo_instruction),
                        |i| Some(SymbolicInstruction::Pseudo(i)),
                    ),
                    map(
                        context("instruction", take_concrete_instruction),
                        |(_l,i)| Some(SymbolicInstruction::Concrete(i)),
                    ),
                ),
            )),
            tag("\n"),
        ),
        |opt| opt.and_then(|i| i),
    )(input)
}

pub fn parse_symbolic_file(input: &str) -> Result<Program> {
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
