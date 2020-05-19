//! Functions for parsing symbolic assembly programs from strings.
//!
//! The only function you problaly are interested in here is [parse_symbolic_file], which
//! you probably want to use via [Program::parse](crate::symbolic::Program::parse).

use logos::{Logos, Lexer, Span};

// use nom::IResult;

use crate::instruction::{
    JumpCondition,
    Mode,
    OpCode,
    Register,
};

use crate::parsing::{
    Error as ParseError,
    ErrorExt,
    ErrorKind,
    SeekStream,
    ParseExt,
    BufferedStream,
    Either,
    either,
};

use crate::symbol_table::{SymbolTable, SymbolId, SymbolInfo, References, Label};

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

type Result<T> = std::result::Result<T, ParseError<String>>;
type TokenStream<'a, 'b> = &'a mut dyn SeekStream<Item=(Token<'b>, Span)>;

fn newline_callback<'a>(lex: &mut Lexer<'a, Token<'a>>) -> logos::Skip {
    lex.extras.line_number += 1;
    lex.extras.line_start_offset = lex.span().end; logos::Skip
}

#[derive(Debug, Clone)]
pub struct PositionInformation {
    line_number: usize,
    line_start_offset: usize,
}

impl Default for PositionInformation {
    fn default() -> PositionInformation {
        PositionInformation {
            line_number: 1,
            line_start_offset: 0,
        }
    }
}

#[derive(Logos, Debug, PartialEq, Clone)]
#[logos(extras = PositionInformation)]
pub enum Token<'a> {
    #[error]
    #[regex(r"[ \t\r\f]", logos::skip)]
    #[regex(r";[^\n]*", logos::skip)]
    #[token("\n", newline_callback)]
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
        "R6" | "SP" => Ok(Register::R6),
        "R7" | "FP" => Ok(Register::R7),
        _ => Err(()),
    } 
}

fn literal_callback<'a>(lex: &mut Lexer<'a, Token<'a>>) -> std::result::Result<i32, std::num::ParseIntError> {
    lex.slice().parse()
}

enum SymbolicOpCode {
    Concrete(OpCode),
    Pseudo(PseudoOpCode),
}

#[test]
fn parse_instructions() {
    let input = r#"
; sum - laske annettuja lukuja yhteen kunnes nolla annettu

Luku  DC    0           ; nykyinen luku
Summa DC    0           ; nykyinen summa

Sum   IN    R1, =KBD	; ohjelma alkaa käskystä 0
      STORE R1, Luku
      JZER  R1, Done    ; luvut loppu?
	
      LOAD  R1, Summa   ; Summa <- Summa+Luku
      ADD   R1, Luku	
      STORE R1, Summa   ; summa muuttujassa, ei rekisterissa?

      JUMP  Sum

Done  LOAD  R1, Summa   ; tulosta summa ja lopeta
      OUT   R1, =CRT

      SVC   SP, =HALT
    "#;

    let mut parser = Parser::from_str(input);

    let result = parser.apply(Parser::take_program);

    println!("{:?}", result);

    if let Err(err) = result {
        if let ErrorKind::UnexpectedToken { span } = err.kind {
            println!("{:?}", &input[span]);
        }
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

#[derive(Default)]
struct State {
    symbol_table: SymbolTable,
}

impl<'a> ParserTrait<(Token<'a>, Span)> for Parser<'a> {
    type Context = State;

    fn span(&self) -> Option<&Span> {
        self.stream.at_offset(-1).map(|t| &t.1)
    }

    fn span_next(&mut self) -> Option<&Span> {
        match self.stream.next() {
            Some((_, span)) => {
                self.stream.seek(-1);
                self.stream.at_offset(0).map(|t| &t.1)
            },
            None => None,
        }
    }

    fn parts(&mut self) -> (&mut dyn SeekStream<Item=(Token<'a>, Span)>, &mut Self::Context) {
        (&mut self.stream, &mut self.state)
    }
}

struct Parser<'a> {
    stream: BufferedStream<logos::SpannedIter<'a, Token<'a>>>,
    state: State,
}

impl<'a> Parser<'a> {
    fn from_str(input: &'a str) -> Self {
        let lex = Token::lexer(input);
        let stream = BufferedStream::from(lex.spanned());

        Parser {
            stream,
            state: Default::default(),
        }
    }
}

use crate::parsing::Parser as ParserTrait;

impl<'t> Parser<'t> {
    fn parse(&mut self) -> Result<Vec<InstructionEntry>> {
        Ok(Vec::new())
    }

    fn parse_second_operand(&mut self) -> Result<SecondOperand> {
        self.apply(Self::take_second_operand)
    }

    fn take_opcode(&mut self) -> Result<SymbolicOpCode> {
        let p = either(Self::take_concrete_opcode, Self::take_pseudo_opcode);

        match self.apply(p)? {
            Either::Left(op) => Ok(SymbolicOpCode::Concrete(op)),
            Either::Right(op) => Ok(SymbolicOpCode::Pseudo(op)),
        }
    }

    fn take_pseudo_opcode(&mut self) -> Result<PseudoOpCode> {
        match self.stream().next() {
            Some((Token::PseudoOperator(op), _)) => Ok(op),
            Some((_, span)) => Err(ParseError::new(span, "expected a pseudo opcode")),
            None => Err(ParseError::eos("expected a pseudo opcode")),
        }
    }

    fn take_concrete_opcode(&mut self) -> Result<OpCode> {
        match self.stream().next() {
            Some((Token::Operator(op), _)) => Ok(op),
            Some((_, span)) => Err(ParseError::new(span, "expected a concrete opcode")),
            None => Err(ParseError::eos("expected a concrete opcode")),
        }
    }

    fn take_register(&mut self) -> Result<Register> {
        match self.stream().next() {
            Some((Token::Register(reg), _)) => Ok(reg),
            Some((_, span)) => Err(ParseError::new(span, "expected a register")),
            None => Err(ParseError::eos("expected a register")),
        }
    }

    fn take_symbol(&mut self) -> Result<SymbolId> {
        match self.stream().next() {
            Some((Token::Symbol(label), span)) => {
                let id = self.context()
                    .symbol_table
                    .get_or_create(label.to_string());

                let sym = self.context()
                    .symbol_table
                    .get_symbol_mut(id);

                sym.get_mut::<References>().push(span);
                sym.set::<Label>(Some(label.to_string()));

                Ok(id)
            },
            Some((_, span)) => Err(ParseError::new(span, "expected a symbol")),
            None => Err(ParseError::eos("expected a symbol")),
        }
    }

    fn take_literal(&mut self) -> Result<i32> {
        match self.stream().next() {
            Some((Token::Literal(num), _)) => Ok(num),
            Some((_, span)) => Err(ParseError::new(span, "expected a literal")),
            None => Err(ParseError::eos("expected a literal")),
        }
    }

    fn take_mode(&mut self) -> Result<Mode> {
        let res = self.apply(either(
            Self::take_token(Token::ImmediateModifier),
            Self::take_token(Token::IndirectModifier),
        ))?;

        match res {
            Either::Left(_) => Ok(Mode::Immediate),
            Either::Right(_) => Ok(Mode::Indirect),
        }
    }

    fn take_token(token: Token<'t>)
        -> impl FnOnce(&mut Parser<'t>) -> Result<Token<'t>>
    {
        let ctx = format!("expected token {:?}", token);
        move |parser| {
            match parser.stream().next() {
                Some((t, _)) if t == token => Ok(t),
                Some((_, span)) => Err(ParseError::new(span, ctx)),
                None => Err(ParseError::eos(ctx)),
            }
        }
    }

    fn take_value(&mut self) -> Result<Value> {
        let p = either(Self::take_symbol, Self::take_register);
        let p = either(Self::take_literal, p);

        let res = self.apply(p).context("expected a symbol, a literal or a register")?;

        match res {
            Either::Left(num) => Ok(Value::Immediate(num as u16)),
            Either::Right(Either::Left(sym)) => Ok(Value::Symbol(sym)),
            Either::Right(Either::Right(reg)) => Ok(Value::Register(reg)),
        }
    }

    fn assert_token<'a>(token: Token<'a>)
        -> impl FnOnce(&mut Parser<'a>) -> Result<()> + 'a
    {
        move |parser| {
            match parser.stream().next() {
                None => Err(ParseError::eos(format!("expected token {:?}", token))),
                Some((t, _)) if t == token => Ok(()),
                Some((_, span)) => Err(ParseError::new(span, format!("expected token {:?}", token))),
            }
        }
    }

    fn take_index_register(&mut self) -> Result<Option<Register>> {
        if self.apply(Self::assert_token(Token::IndexBegin)).is_ok() {
            let reg = self.apply(Self::take_register)?;
            self.apply(Self::assert_token(Token::IndexEnd))?;

            return Ok(Some(reg));
        }

        Ok(None)
    }

    fn take_second_operand(&mut self) -> Result<SecondOperand> {
        let mode = self.apply(Self::take_mode).ok().unwrap_or(Mode::Direct);
        let value = self.apply(Self::take_value)?;
        let index = self.apply(Self::take_index_register)?;

        Ok(SecondOperand {
            mode,
            value,
            index,
        })
    }

    fn take_concrete_instruction(&mut self) -> Result<ConcreteInstruction> {
        let opcode = self.apply(Self::take_concrete_opcode)?;

        if opcode == OpCode::NoOperation {
            return Ok(ConcreteInstruction {
                label: None,
                opcode,
                operand1: Register::R0,
                operand2: SecondOperand {
                    mode: Mode::Immediate,
                    value: Value::Immediate(0),
                    index: None,
                },
            });
        }

        if let OpCode::Jump { condition: JumpCondition::Unconditional, .. } = opcode {
            let operand2 = self.apply(Self::take_second_operand)?;

            return Ok(ConcreteInstruction {
                label: None,
                opcode,
                operand1: Register::R0,
                operand2,
            });
        }

        let operand1 = self.apply(Self::take_register)?;

        if let OpCode::PushRegisters | OpCode::PopRegisters | OpCode::Not = opcode {
            return Ok(ConcreteInstruction {
                label: None,
                opcode,
                operand1,
                operand2: SecondOperand {
                    mode: Mode::Immediate,
                    value: Value::Immediate(0),
                    index: None,
                },
            });
        }

        self.apply(Self::assert_token(Token::ParameterSeparator))
            .context("expected a comma")?;

        let operand2 = self.apply(Self::take_second_operand)
            .context("invalid second operand")?;

        Ok(ConcreteInstruction {
            label: None,
            opcode,
            operand1,
            operand2,
        })
    }

    fn take_pseudo_instruction(&mut self) -> Result<PseudoInstruction> {
        let opcode = self.apply(Self::take_pseudo_opcode)?;
        let operand = self.apply(Self::take_literal)?;

        match opcode {
            PseudoOpCode::DC | PseudoOpCode::EQU => Ok(PseudoInstruction {
                value: operand,
                size: 1,
            }),
            PseudoOpCode::DS => Ok(PseudoInstruction {
                value: 0,
                size: operand as u16,
            }),
        }
    }

    fn take_instruction(&mut self) -> Result<SymbolicInstruction> {
        let p = either(Self::take_concrete_instruction, Self::take_pseudo_instruction);

        match self.apply(p)? {
            Either::Left(ins) => Ok(SymbolicInstruction::Concrete(ins)),
            Either::Right(ins) => Ok(SymbolicInstruction::Pseudo(ins)),
        }
    }

    fn take_program(&mut self) -> Result<Vec<InstructionEntry>> {
        let mut program = Vec::new();

        'outer: loop {
            let mut labels = Vec::new();

            loop {
                match self.apply(Self::take_symbol) {
                    Ok(sym) => labels.push(sym),
                    Err(ParseError { kind: ErrorKind::EndOfStream, .. }) => break 'outer,
                    Err(_) => break,
                }
            }

            let start = self.span_next().cloned();

            let instruction = self.apply(Self::take_instruction)?;

            let end = self.span().clone();

            println!("Line: {:?} {:?}", start, end);

            let span = match (start, end) {
                (Some(start), Some(end)) => Some(start.end .. end.start),
                _ => None,
            };

            program.push(InstructionEntry {
                labels,
                instruction,
                span,
            });
        }

        Ok(program)
    }
}

struct SpanTracker<P> {
    parser: P,
    start: usize,
    end: usize,
}

impl<'a,P> SpanTracker<P> where P: ParserTrait<(Token<'a>, Span)> {
    fn new(parser: P) -> SpanTracker<P> {
        let start = parser.span()
            .map(|span| span.start)
            .unwrap_or(0);

        SpanTracker {
            parser,
            start,
            end: start,
        }
    }

    fn span(self) -> Span {
        self.start .. self.end
    }
}

impl<'a, P> ParserTrait<(Token<'a>, Span)> for SpanTracker<P> where P: ParserTrait<(Token<'a>, Span)> {
    type Context = P::Context;

    fn span(&self) -> Option<&Span> {
        self.parser.span()
    }

    fn span_next(&mut self) -> Option<&Span> {
        self.parser.span_next()
    }

    fn parts(&mut self) -> (&mut dyn SeekStream<Item=(Token<'a>, Span)>, &mut Self::Context) {
        self.parser.parts()
    }
}

/*impl<'a> Parser<'a> {
    fn from_str(input: &'a str) -> Parser<'a> {
        Parser {
            stream: TokenStream::from_str(input),
            symbol_table: SymbolTable::new(),
        }
    }

    fn take_instruction(&mut self, op: OpCode) -> Result<ConcreteInstruction> {
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
                _ => return Err(ErrorKind::Expected {
                    got: other,
                    expected: "",
                }),
            },
            @eof => return Err(ErrorKind::UnexpectedEOF),
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
                _ => return Err(ErrorKind::Expected {
                    got: other,
                    expected: "the second operand",
                }),
            },
            @eof => return Err(ErrorKind::UnexpectedEOF),
        });

        let operand2 = self.take_second_operand()?;

        Ok(ConcreteInstruction {
            label: None,
            opcode: op,
            operand1,
            operand2,
        })
    }

    fn take_second_operand(&mut self) -> Result<'a, SecondOperand, ErrorKind<'a>> {
        let mode = match_token!(self.stream, {
            Token::IndirectModifier => Mode::Indirect,
            Token::ImmediateModifier => Mode::Immediate,
            @peek _token => Mode::Direct,
            @eof => return Err(ErrorKind::UnexpectedEOF),
        });

        let value = match_token!(self.stream, {
            Token::Register(r) => Value::Register(r),
            Token::Literal(l) => Value::Immediate(l as u16),
            Token::Symbol(sym) => {
                let id = self.symbol_table.reference_symbol(self.stream.span(), sym.to_string());
                Value::Symbol(id)
            },
            other => return Err(ErrorKind::Expected {
                got: other,
                expected: "a register or a symbol",
            }), 
            @eof => return Err(ErrorKind::UnexpectedEOF),
        });


        let index = match_token!(self.stream, {
            Token::IndexBegin => {
                match self.stream.advance() {
                    Some(Token::Register(r)) => {
                        match self.stream.advance() {
                            Some(Token::IndexEnd) => Some(r),
                            Some(other) => return Err(ErrorKind::Expected {
                                got: other,
                                expected: "a closing parenthesis"
                            }),
                            None => return Err(ErrorKind::UnexpectedEOF),
                        }
                    },
                    Some(other) => return Err(ErrorKind::Expected {
                        got: other,
                        expected: "a register"
                    }),
                    None => return Err(ErrorKind::UnexpectedEOF),
                }
            },
            @peek _other => None,
            @eof => None,
        });

        Ok(SecondOperand {
            mode,
            value,
            index,
        })
    }

    fn take_pseudo_instruction(&mut self, op: PseudoOpCode) -> Result<'a, PseudoInstruction, ErrorKind<'a>> {
        let operand = match_token!(self.stream, {
            Token::Literal(l) => l,
            other => return Err(ErrorKind::Expected {
                got: other,
                expected: "",
            }),
            @eof => return Err(ErrorKind::UnexpectedEOF),
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

    fn parse(&mut self) -> Result<'a, Vec<InstructionEntry>> {
        match self._parse() {
            Ok(ins) => Ok(ins),
            Err(kind) => {
                Err(ParseError {
                    span: self.stream.span(),
                    line: self.stream.lexer.extras.line_number,
                    column: self.stream.lexer.span().start - self.stream.lexer.extras.line_start_offset,
                    kind,
                })
            },
        }
    }

    fn _parse(&mut self) -> Result<Vec<InstructionEntry>, ErrorKind<'a>> {
        let mut instructions = Vec::new();
        let mut label_acc = Vec::new();

        loop {
            let source_line = self.stream.lexer.extras.line_number;

            let labels = match_token!(self.stream, {
                Token::Symbol(label) => {
                    let res = self.symbol_table.define_symbol(
                        self.stream.span(),
                        label.to_string(),
                        instructions.len() as i32,
                    );

                    match res {
                        Ok(id) => {
                            label_acc.push(id);
                            continue;
                        },
                        Err(id) => return Err(ErrorKind::AlreadyDefined {
                            symbol: id,
                            label,
                        }),
                    };
                },
                @peek _other => {
                    label_acc.drain(..).collect()
                },
                @eof => break,
            });

            let instruction = match_token!(self.stream, {
                Token::Operator(op) => SymbolicInstruction::Concrete(self.take_instruction(op)?),
                Token::PseudoOperator(op) => SymbolicInstruction::Pseudo(self.take_pseudo_instruction(op)?),
                got => return Err(ErrorKind::Expected {
                    got,
                    expected: "an opcode",
                }),
                @eof => break,
            });

            println!("Line: {}", self.stream.lexer.extras.line_number);
            instructions.push(InstructionEntry {
                instruction,
                labels,
                source_line,
            });
        }

        Ok(instructions)
    }
}*/

/// Parse a single line of assembly.
pub fn parse_line(input: &str)
    -> Result<Option<(Option<&str>, SymbolicInstruction)>>
{
    unimplemented!()
}

/// Parse an entier assembly program.
///
/// You propably want to use this via [Program::parse](crate::symbolic::Program::parse).
pub fn parse_symbolic_file(input: &str) -> Result<Program> {
    let mut parser = Parser::from_str(input);
    let instructions = parser.apply(Parser::take_program)?;

    Ok(Program {
        symbol_table: parser.state.symbol_table,
        instructions,
    })
}
