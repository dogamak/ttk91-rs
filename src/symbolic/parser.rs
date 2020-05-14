//! Functions for parsing symbolic assembly programs from strings.
//!
//! The only function you problaly are interested in here is [parse_symbolic_file], which
//! you probably want to use via [Program::parse](crate::symbolic::Program::parse).

use logos::{Logos, Lexer, Span};

use nom::IResult;

use crate::instruction::{
    JumpCondition,
    Mode,
    OpCode,
    Register,
};

use crate::symbol_table::SymbolTable;

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

use std::collections::HashMap;
use std::fmt;
use std::result::Result as StdResult;

/// Represents error conditions specific to symbolic assembly parsing.
#[derive(Debug, Clone)]
pub enum ErrorKind<'a> {
    Expected {
        expected: &'static str,
        got: Token<'a>,
    },
    UnexpectedEOF,
}

type Result<'a,T> = std::result::Result<T, ParseError<'a>>;

#[derive(Debug)]
pub struct ParseError<'a> {
    span: Span,
    kind: ErrorKind<'a>,
}

impl<'a> fmt::Display for ErrorKind<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ErrorKind::Expected { expected, got } => write!(f, "expected token {:?} got {:?}", expected, got),
            ErrorKind::UnexpectedEOF => write!(f, "unexpected EOF"),
        }
    }
}

#[derive(Logos, Debug, PartialEq, Clone)]
pub enum Token<'a> {
    #[error]
    #[regex(r"[ \t\n\f]", logos::skip)]
    #[regex(r";.*\n", logos::skip)]
    Error,

    #[regex("R[1-7]|SP|FP", register_callback)]
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

struct TokenStream<'a> {
    lexer: Lexer<'a, Token<'a>>,
    prev_span: Option<logos::Span>,
    peek_buffer: Option<Token<'a>>,
}

impl<'a> TokenStream<'a> {
    fn new(lexer: Lexer<'a, Token<'a>>) -> TokenStream<'a> {
        TokenStream {
            lexer,
            prev_span: None,
            peek_buffer: None,
        }
    }

    fn from_str(input: &'a str) -> TokenStream<'a> {
        TokenStream::new(Token::lexer(input))
    }

    fn span(&self) -> Span {
        self.lexer.span()
    }

    fn peek(&mut self) -> Option<&Token<'a>> {
        if let Some(ref t) = self.peek_buffer {
            return Some(t);
        }

        if let Some(t) = self.lexer.next() {
            println!("Peek Advance: {:?}", t);
            self.peek_buffer = Some(t);
            return self.peek_buffer.as_ref();
        }

        None
    }

    fn advance(&mut self) -> Option<Token<'a>> {
        self.prev_span = Some(self.lexer.span());

        if let Some(t) = std::mem::take(&mut self.peek_buffer) {
            println!("Advance: {:?} (from peek buffer)", t);
            return Some(t);
        }

        let res = self.lexer.next();
        println!("Advance: {:?} (from lexer)", res);
        res
    }
}

macro_rules! match_token {
    ( $stream:expr, { $( $pattern:pat => $code:expr, )* $(@peek $token:ident => $peek_arm:expr, )* @eof => $eof_arm:expr $(,)* } ) => {
        match $stream.peek() {
            $(Some($pattern) => {
                if let Some($pattern) = $stream.advance() {
                    $code
                } else {
                    unreachable!()
                }
            },)*
            $(Some($token) => $peek_arm, )*
            None => $eof_arm,
        }
    };
}

struct Parser<'a> {
    stream: TokenStream<'a>,
    symbol_table: SymbolTable<'a>,
}

impl<'a> Parser<'a> {
    fn from_str(input: &'a str) -> Parser<'a> {
        Parser {
            stream: TokenStream::from_str(input),
            symbol_table: SymbolTable::new(),
        }
    }

    fn take_instruction(&mut self, op: OpCode) -> Result<'a, ConcreteInstruction> {
        let operand1 = match_token!(self.stream, {
            Token::Register(r) => r,
            other => match op {
                OpCode::NoOperation => return Ok(ConcreteInstruction {
                    label: None,
                    opcode: op,
                    operand1: Register::R0,
                    operand2: SecondOperand {
                        mode: Mode::Immediate,
                        value: Value::Immediate(0),
                        index: None,
                    },
                }),
                _ => return Err(ParseError {
                    span: self.stream.span(),
                    kind: ErrorKind::Expected {
                        got: other,
                        expected: "",
                    },
                }),
            },
            @eof => return Err(ParseError {
                span: self.stream.span(),
                kind: ErrorKind::UnexpectedEOF,
            }),
        });

        match_token!(self.stream, {
            Token::ParameterSeparator => (),
            other => match op {
                OpCode::PushRegisters | OpCode::PopRegisters | OpCode::Not => {
                    return Ok(ConcreteInstruction {
                        label: None,
                        opcode: op,
                        operand1,
                        operand2: SecondOperand {
                            mode: Mode::Immediate,
                            value: Value::Immediate(0),
                            index: None,
                        },
                    });
                },
                _ => return Err(ParseError {
                    span: self.stream.span(),
                    kind: ErrorKind::Expected {
                        got: other,
                        expected: "the second operand",
                    },
                }),
            },
            @eof => return Err(ParseError {
                span: self.stream.span(),
                kind: ErrorKind::UnexpectedEOF,
            }),
        });

        let operand2 = self.take_second_operand()?;

        Ok(ConcreteInstruction {
            label: None,
            opcode: op,
            operand1,
            operand2,
        })
    }

    fn take_second_operand(&mut self) -> Result<'a, SecondOperand> {
        let mode = match_token!(self.stream, {
            Token::IndirectModifier => Mode::Indirect,
            Token::ImmediateModifier => Mode::Immediate,
            @peek _token => Mode::Direct,
            @eof => return Err(ParseError {
                span: self.stream.span(),
                kind: ErrorKind::UnexpectedEOF,
            }),
        });

        let value = match_token!(self.stream, {
            Token::Register(r) => Value::Register(r),
            Token::Symbol(sym) => {
                self.symbol_table.reference_symbol(self.stream.span(), sym);
                Value::Symbol(sym.to_string()) // TODO: Change to SymbolId
            },
            other => return Err(ParseError {
                span: self.stream.span(),
                kind: ErrorKind::Expected {
                    got: other,
                    expected: "a register or a symbol",
                },
            }), 
            @eof => return Err(ParseError {
                span: self.stream.span(),
                kind: ErrorKind::UnexpectedEOF,
            }),
        });

        println!("Before Index: {:?}", self.stream.lexer.remainder());

        let index = match_token!(self.stream, {
            Token::IndexBegin => {
                match self.stream.advance() {
                    Some(Token::Register(r)) => {
                        match self.stream.advance() {
                            Some(Token::IndexEnd) => Some(r),
                            Some(other) => return Err(ParseError {
                                span: self.stream.span(),
                                kind: ErrorKind::Expected {
                                    got: other,
                                    expected: "a closing parenthesis"
                                }
                            }),
                            None => return Err(ParseError {
                                span: self.stream.span(),
                                kind: ErrorKind::UnexpectedEOF,
                            }),
                        }
                    },
                    Some(other) => return Err(ParseError {
                        span: self.stream.span(),
                        kind: ErrorKind::Expected {
                            got: other,
                            expected: "a register"
                        }
                    }),
                    None => return Err(ParseError {
                        span: self.stream.span(),
                        kind: ErrorKind::UnexpectedEOF,
                    }),
                }
            },
            @peek _other => None,
            @eof => None,
        });

        println!("After Index: {:?}", self.stream.lexer.remainder());

        Ok(SecondOperand {
            mode,
            value,
            index,
        })
    }

    fn take_pseudo_instruction(&mut self, op: PseudoOpCode) -> Result<'a, PseudoInstruction> {
        let operand = match_token!(self.stream, {
            Token::Literal(l) => l,
            other => return Err(ParseError {
                span: self.stream.span(),
                kind: ErrorKind::Expected {
                    got: other,
                    expected: "",
                },
            }),
            @eof => return Err(ParseError {
                span: self.stream.span(),
                kind: ErrorKind::UnexpectedEOF,
            }),
        });

        match op {
            PseudoOpCode::DC => Ok(PseudoInstruction {
                size: 1,
                value: operand,
            }),
            PseudoOpCode::DS => Ok(PseudoInstruction {
                size: operand as u16,
                value: 0,
            }),
            PseudoOpCode::EQU => Ok(PseudoInstruction {
                size: 1,
                value: operand,
            }),
        }
    }

    fn parse(&mut self) -> Result<'a, Vec<SymbolicInstruction>> {
        let mut instructions = Vec::new();

        loop {
            println!("Start: {}", self.stream.lexer.remainder());
            match_token!(self.stream, {
                Token::Symbol(label) => {
                    self.symbol_table.define_symbol(self.stream.span(), label, instructions.len() as i32);
                },
                @peek _other => (),
                @eof => break,
            });

            let instruction = match_token!(self.stream, {
                Token::Operator(op) => SymbolicInstruction::Concrete(self.take_instruction(op)?),
                Token::PseudoOperator(op) => SymbolicInstruction::Pseudo(self.take_pseudo_instruction(op)?),
                got => return Err(ParseError {
                    span: self.stream.span(),
                    kind: ErrorKind::Expected {
                        got,
                        expected: "an opcode",
                    },
                }),
                @eof => break,
            });

            println!("Instuction: {:?}", instruction);
            instructions.push(instruction);
        }

        Ok(instructions)
    }
}

/// Parse a single line of assembly.
pub fn parse_line(input: &str)
    -> StdResult<Option<(Option<&str>, SymbolicInstruction)>, ParseError>
{
    unimplemented!()
}

/// Parse an entier assembly program.
///
/// You propably want to use this via [Program::parse](crate::symbolic::Program::parse).
pub fn parse_symbolic_file(input: &str) -> Result<Program> {
    let mut parser = Parser::from_str(input);
    let instructions = parser.parse()?;

    Ok(Program {
        instructions: instructions.into_iter()
            .map(|instruction| InstructionEntry {
                instruction,
                label: None,
                source_line: 0,
            })
            .collect()
    })
}
