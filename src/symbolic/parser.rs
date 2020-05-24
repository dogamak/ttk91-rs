//! Functions for parsing symbolic assembly programs from strings.

use slog::{Logger, Discard, trace, o};

use std::fmt;

use logos::Logos;

use super::ast::{
    Instruction,
    JumpCondition,
    Part,
    Mode,
    OpCode,
    Program,
    PseudoOpCode,
    RealOpCode,
    Register,
    Operand,
    Value,
};

use crate::error::ResultExt;

use crate::parsing::{
    BufferedStream,
    either,
    ErrorKind as ParseErrorKind,
    Context,
    Either,
    Parser as ParserTrait,
    Span,
    take_token,
};

use crate::symbol_table::{SymbolTable, SymbolId, References, Label};

use super::token::Token;

/// Error kinds specific to parsing the symbolic TTK91 assembly format.
#[derive(Debug, Clone)]
pub enum ErrorKind {
    /// An invalid number of operands were provided for an instruction.
    OperandCount {
        /// Location of the errorneous instruction in the input stream.
        span: Span,

        /// The expected number of operands for this instruction type.
        expected: usize,

        /// The number of instructions provided in the input stream.
        got: usize,
    },

    /// An operand of invalid type was provided for an instruction.
    InvalidOperand {
        /// Location of the errorneous operand in the input stream.
        span: Span,

        /// The number of the operand.
        index: usize,
    },
}

impl fmt::Display for ErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ErrorKind::OperandCount { expected, got, .. } =>
                write!(f, "expected {} operands but got {}", expected, got), 
            ErrorKind::InvalidOperand { index, .. } =>
                write!(f, "operand #{} is invalid", index),
        }
    }
}

/// An error which has occurred while parsing a symbolic TTK91 program.
pub type ParseError<'t> = crate::parsing::ParseError<ErrorKind, Token<'t>>;

/// The [Result] type of symbolic TTK91 format parsing operations.
pub type Result<'t, T> = std::result::Result<T, ParseError<'t>>;

impl<'a, T> ParserTrait<Token<'a>> for Parser<'a, T> {
    type Stream = BufferedStream<logos::SpannedIter<'a, Token<'a>>>;

    fn stream(&self) -> &Self::Stream {
        &self.stream
    }

    fn stream_mut(&mut self) -> &mut Self::Stream {
        &mut self.stream
    }
}

/// The state of the parser.
#[derive(Default)]
pub struct State<T> {
    /// Symbol table containing information about all symbols encountered in the input stream so
    /// far.
    pub symbol_table: T,
}

/// Type for parsing symbolic TTK91 programs.
pub struct Parser<'a, T=SymbolTable> {
    /// A logger to which debugging information is logged during parsing.
    logger: Logger,

    /// The input token stream on which the parser operates.
    stream: BufferedStream<logos::SpannedIter<'a, Token<'a>>>,

    pub state: State<T>,
}

impl<'a> Parser<'a, SymbolTable> {
    /// Runs the provided input string through a tokenizer and creates a parser from the resulting
    /// tokens stream.
    pub fn from_str(input: &'a str) -> Self {
        let lex = Token::lexer(input);
        let stream = BufferedStream::from(lex.spanned());

        Parser {
            logger: Logger::root(Discard, o!()),
            stream,
            state: Default::default(),
        }
    }
}

impl<'a, T> Parser<'a, T> {
    /// Replaces the parser's symbol table with the provided one.
    pub fn with_symbol_table<T2>(self, symbol_table: T2) -> Parser<'a, T2> {
        Parser {
            logger: self.logger,
            stream: self.stream,
            state: State { symbol_table },
        }
    }

    /// Sets the [Logger] used by the [Parser] to the provided one.
    pub fn set_logger(&mut self, logger: &Logger) {
        self.logger = logger.new(o!("parsing" => true));
    }
}

use lazy_static::lazy_static;
use std::collections::HashMap;
use edit_distance::edit_distance;

/// Finds the opcode with the mnemonic that has the shortest edit distance to the provided string.
/// This is used to try and proved helpful suggestions for the user.
fn find_closest_opcode(label: &str) -> &'static OpCode {
    lazy_static! {
        static ref MNEMONIC_MAP: HashMap<&'static str, OpCode> = {
            let mut map = HashMap::new();

            map.insert("NOP", OpCode::Real(RealOpCode::NoOperation));
            map.insert("STORE", OpCode::Real(RealOpCode::Store));
            map.insert("LOAD", OpCode::Real(RealOpCode::Load));
            map.insert("IN", OpCode::Real(RealOpCode::In));
            map.insert("OUT", OpCode::Real(RealOpCode::Out));
            map.insert("ADD", OpCode::Real(RealOpCode::Add));
            map.insert("SUB", OpCode::Real(RealOpCode::Subtract));
            map.insert("MUL", OpCode::Real(RealOpCode::Multiply));
            map.insert("DIV", OpCode::Real(RealOpCode::Divide));
            map.insert("MOD", OpCode::Real(RealOpCode::Modulo));
            map.insert("AND", OpCode::Real(RealOpCode::And));
            map.insert("OR", OpCode::Real(RealOpCode::Or));
            map.insert("XOR", OpCode::Real(RealOpCode::Xor));
            map.insert("SHL", OpCode::Real(RealOpCode::ShiftLeft));
            map.insert("SHR", OpCode::Real(RealOpCode::ShiftRight));
            map.insert("NOT", OpCode::Real(RealOpCode::Not));
            map.insert("COMP", OpCode::Real(RealOpCode::Compare));
            map.insert("CALL", OpCode::Real(RealOpCode::Call));
            map.insert("EXIT", OpCode::Real(RealOpCode::Exit));
            map.insert("PUSH", OpCode::Real(RealOpCode::Push));
            map.insert("POP", OpCode::Real(RealOpCode::Pop));
            map.insert("PUSHR", OpCode::Real(RealOpCode::PushRegisters));
            map.insert("POPR", OpCode::Real(RealOpCode::PopRegisters));
            map.insert("SVC", OpCode::Real(RealOpCode::SupervisorCall));
            map.insert(
                "JUMP",
                OpCode::Real(RealOpCode::Jump {
                    negated: false,
                    condition: JumpCondition::Unconditional,
                }),
            );
            map.insert(
                "JZER",
                OpCode::Real(RealOpCode::Jump {
                    negated: false,
                    condition: JumpCondition::Zero,
                }),
            );
            map.insert(
                "JNZER",
                OpCode::Real(RealOpCode::Jump {
                    negated: true,
                    condition: JumpCondition::Zero,
                }),
            );
            map.insert(
                "JPOS",
                OpCode::Real(RealOpCode::Jump {
                    negated: false,
                    condition: JumpCondition::Positive,
                }),
            );
            map.insert(
                "JNPOS",
                OpCode::Real(RealOpCode::Jump {
                    negated: true,
                    condition: JumpCondition::Positive,
                }),
            );
            map.insert(
                "JNEG",
                OpCode::Real(RealOpCode::Jump {
                    negated: false,
                    condition: JumpCondition::Negative,
                }),
            );
            map.insert(
                "JNNEG",
                OpCode::Real(RealOpCode::Jump {
                    negated: true,
                    condition: JumpCondition::Negative,
                }),
            );
            map.insert(
                "JEQU",
                OpCode::Real(RealOpCode::Jump {
                    negated: false,
                    condition: JumpCondition::Equal,
                }),
            );
            map.insert(
                "JNEQU",
                OpCode::Real(RealOpCode::Jump {
                    negated: true,
                    condition: JumpCondition::Equal,
                }),
            );
            map.insert(
                "JLES",
                OpCode::Real(RealOpCode::Jump {
                    negated: false,
                    condition: JumpCondition::Less,
                }),
            );
            map.insert(
                "JNLES",
                OpCode::Real(RealOpCode::Jump {
                    negated: true,
                    condition: JumpCondition::Less,
                }),
            );
            map.insert(
                "JGRE",
                OpCode::Real(RealOpCode::Jump {
                    negated: false,
                    condition: JumpCondition::Greater,
                }),
            );
            map.insert(
                "JNGRE",
                OpCode::Real(RealOpCode::Jump {
                    negated: true,
                    condition: JumpCondition::Greater,
                }),
            );

            map.insert("DC", OpCode::Pseudo(PseudoOpCode::DC));
            map.insert("DS", OpCode::Pseudo(PseudoOpCode::DS));
            map.insert("EQU", OpCode::Pseudo(PseudoOpCode::EQU));
            
            map
        };
    }

    let mut distances = MNEMONIC_MAP.iter()
        .map(|(key, opcode)| (edit_distance(key, label), opcode))
        .collect::<Vec<_>>();

    distances.sort_by_key(|(distance, _)| *distance);

    distances[0].1
}

/// An error type for the [Parser::_parse_verbose] function. Provides a middle state in addition to
/// the success and error states found in [Result]. This middle state [Fixes] represents an error
/// from which the parser was able to recover from.
///
/// [Fixes]: IterativeParsingResult::Fixes
#[derive(Debug)]
enum IterativeParsingResult<T,E> {
    /// The parse operation was successfull without any errors.
    Success(T),

    /// The parse operation encountered errors, but was able to recover from them.
    Fixes(T, Vec<E>),

    /// The parse operation encountered an error from which it could not recover.
    Error(E),
}

impl<'t> Parser<'t, SymbolTable> {
    /// Parses a single instruction from the input stream.
    pub fn parse_instruction(input: &'t str) -> Result<Instruction> {
        Parser::<SymbolTable>::from_str(input)
            .apply(Parser::take_instruction)
    }
}

impl<'t, T> Parser<'t, T>
where
    T: std::borrow::BorrowMut<SymbolTable>,
{
    /// Parse a single line of assembly. This includes a possible label and an instruction.
    pub fn parse_line(&mut self)
        -> Result<'t, (Option<SymbolId>, Instruction)>
    {
        let label = self.apply(Self::take_symbol).ok();

        let instruction = self.apply(Parser::take_instruction)?;

        Ok((label, instruction))
    }

    /// Tries to parse a program written in symbolic TTK91 assembly. Fails on the first
    /// encountered error and returns it.
    pub fn parse(&mut self) -> Result<'t, Program> {
        self.stream.reset();
        let res = self.apply(Self::take_program);

        res
    }

    /// Like [Parser::parse], tries to parse a program written in symbolic TTK91 assembly.
    /// Unlike [Parser::parse], this function tries it's best to recover from any syntax errors in
    /// order to provide suggestions on how to fix these errors and continue parsing further.
    pub fn parse_verbose(&mut self) -> std::result::Result<Program, (Option<Program>, Vec<ParseError<'t>>)> {
        match self._parse_verbose(None) {
            IterativeParsingResult::Success(program) => Ok(program),
            IterativeParsingResult::Error(error) => Err((None, vec![error])),
            IterativeParsingResult::Fixes(result, errors) => Err((Some(result), errors)),
        }
    }

    fn _parse_verbose(&mut self, previous_error: Option<ParseError>)
        -> IterativeParsingResult<Program, ParseError<'t>>
    {
        let logger = self.logger.clone();

        let error = match self.parse() {
            Ok(program) => {
                if let Some(_) = self.stream_mut().next() {
                    trace!(logger, "Trailing Input");
                    return IterativeParsingResult::Error(ParseError::new(ParseErrorKind::TrailingInput));
                } else {
                    return IterativeParsingResult::Success(program);
                }
            },
            Err(err) => err,
        };

        if let Some(ref previous_error) = previous_error {
            let further = match (previous_error.span(), error.span()) {
                (None, None) => false,
                (Some(_), None) => true,
                (None, Some(_)) => false,
                (Some(s1), Some(s2)) => s1.start < s2.start,
            };

            trace!(logger, "Checking if error location has changed";
                "previous" => ?previous_error.span(),
                "new" => ?error.span(),
                "further" => further,
            );

            if !further {
                return IterativeParsingResult::Error(error);
            }
        }

        let mut fixes = Vec::new();

        for i in (0..self.stream.buffer_mut().len()).rev() {
            let (ref mut token, ref span) = self.stream.buffer_mut()[i];
            let span = span.clone();

            if let ParseErrorKind::UnexpectedToken { span: ref error_span, .. } = error.kind {
                if span.start > error_span.start {
                    continue;
                }
            }

            if let Token::Symbol(label) = token {
                let replacement = match find_closest_opcode(label) {
                    OpCode::Real(op) => Token::RealOperator(op.clone()),
                    OpCode::Pseudo(op) => Token::PseudoOperator(op.clone()),
                };

                let original = std::mem::replace(token, replacement.clone());

                trace!(logger, "Attempting fix: Change token";
                   "original" => ?original,
                   "replacement" => ?replacement,
                );

                let res = self._parse_verbose(Some(error.clone()));
                
                trace!(logger, "Attempting fix: Parse result: {:?}", res);

                self.stream.buffer_mut()[i].0 = original;

                let errors = match res {
                    IterativeParsingResult::Success(program) => Some((program, Vec::new())),
                    IterativeParsingResult::Error(_) => None,
                    IterativeParsingResult::Fixes(result, fixes) => Some((result, fixes)),
                };

                if let Some((program, mut errors)) = errors {
                    let mut error = error.clone();

                    error.context.push(Context::Suggestion {
                        span: span.clone(),
                        message: format!("Consider changing this to {:?}", replacement),
                    });

                    errors.push(error);

                    fixes.push((1, program, errors));
                    break;
                }
            }

            let token = self.stream.remove_token(i);

            trace!(logger, "Attempting fix: Remove token"; "token" => ?token);

            let res = self._parse_verbose(Some(error.clone()));
            
            trace!(logger, "Attempting fix: Parse result: {:?}", res);

            self.stream.buffer_mut().insert(i, token);

            let errors = match res {
                IterativeParsingResult::Success(program) => Some((program, Vec::new())),
                IterativeParsingResult::Error(_) => None,
                IterativeParsingResult::Fixes(result, fixes) => Some((result, fixes)),
            };

            if let Some((result, mut errors)) = errors {
                let mut error = error.clone();

                error.context.push(Context::Suggestion {
                    span: span.clone(),
                    message: format!("Consider removing this"),
                });

                errors.push(error);

                fixes.push((2, result, errors));
            }
        }

        fixes.sort_by_key(|f| f.0);

        if !fixes.is_empty() {
            let (_, program, fixes) = fixes.remove(0);
            IterativeParsingResult::Fixes(program, fixes)
        } else {
            IterativeParsingResult::Error(ParseError::end_of_stream())
        }
    }

    /// Tries to parse an register (R1-R9, SP or FP).
    fn take_register(&mut self) -> Result<'t, Register> {
        match self.stream_mut().next() {
            Some((Token::Register(reg), _)) => Ok(reg),
            Some((got, span)) => Err(ParseError::unexpected(span, got, "a register".into())),
            None => Err(ParseError::end_of_stream().context("expected a register")),
        }
    }

    /// Tries to parse an symbol. If required, allocates an entry for the symbol in the
    /// [SymbolTable] and returns the symbol's [SymbolId].
    ///
    /// Any additional symbol metadata (including it's label) can be accessed via the
    /// [SymbolTable].
    fn take_symbol(&mut self) -> Result<'t, SymbolId> {
        match self.stream_mut().next() {
            Some((Token::Symbol(label), span)) => {
                let id = self.state
                    .symbol_table
                    .borrow_mut()
                    .get_or_create(label.to_string());

                let sym = self.state
                    .symbol_table
                    .borrow_mut()
                    .symbol_mut(id);

                sym.get_mut::<References>().push(span);
                sym.set::<Label>(Some(label.to_string()));

                Ok(id)
            },
            Some((got, span)) => Err(ParseError::unexpected(span, got, "a symbol".into())),
            None => Err(ParseError::end_of_stream().context("expected a symbol")),
        }
    }

    /// Tries to parse an integer literal.
    fn take_literal(&mut self) -> Result<'t, i32> {
        match self.stream_mut().next() {
            Some((Token::Literal(num), _)) => Ok(num),
            Some((got, span)) => Err(ParseError::unexpected(span, got, "a literal".into())),
            None => Err(ParseError::end_of_stream().context("expected a literal")),
        }
    }

    /// Tries to parse an addressing mode specifier (either `@` or `=`).
    fn take_modifier(&mut self) -> Result<'t, Mode> {
        let res = self.apply(either(
            take_token(Token::ImmediateModifier),
            take_token(Token::IndirectModifier),
        ))?;

        match res {
            Either::Left(_) => Ok(Mode::Immediate),
            Either::Right(_) => Ok(Mode::Indirect),
        }
    }

    /// Tries to parse a [Value], which can be a integer literal, a symbol or a register.
    ///
    /// Take note that the [Value::Symbol] variant contains a [SymbolId], and not the symbol label.
    /// The symbol label and other information can be fetched and/or modified via the [SymbolTable].
    fn take_value(&mut self) -> Result<'t, Value> {
        let p = either(Self::take_symbol, Self::take_register);
        let p = either(Self::take_literal, p);

        let res = self.apply(p).context("expected a symbol, a literal or a register")?;

        match res {
            Either::Left(num) => Ok(Value::Immediate(num as u16)),
            Either::Right(Either::Left(sym)) => Ok(Value::Symbol(sym)),
            Either::Right(Either::Right(reg)) => Ok(Value::Register(reg)),
        }
    }

    /// Tries to parse an index register construct, including the parentheses.
    ///
    /// Note that this function returns an [Option] and so succeeds even if no index register
    /// construct is present. However, if there is an opening parenthesis, but the rest of the
    /// constuct is malformed, this function returns an error.
    fn take_index_register(&mut self) -> Result<'t, Option<Register>> {
        if self.assert_token::<()>(Token::IndexBegin).is_ok() {
            let reg = self.apply(Self::take_register)?;
            self.assert_token(Token::IndexEnd)?;

            return Ok(Some(reg));
        }

        Ok(None)
    }

    /// Tries to parse the second operand of an instruction.
    ///
    /// The operand consist of an optional addressing mode specifier, a base operand and an
    /// optional index register. The base operand can be either a symbol, a register or a value and
    /// is the only required component of the operand.
    fn take_operand(&mut self) -> Result<'t, Operand> {
        let start = self.boundary_right();

        // Take an optional adressing modifier.
        let mode = self.apply(Self::take_modifier).ok();

        // The operand base. A register, a symbol or a literal.
        let base = self.apply(Self::take_value)?;

        // Take the index register if present. Otherwise returns None.
        let index = self.apply(Self::take_index_register)?;

        let end = self.boundary_left();

        Ok(Operand {
            mode,
            base,
            index,
            span: start..end,
        })
    }

    /// Takes an [OpCode] from the input stream.
    pub fn take_opcode(&mut self) -> Result<'t, OpCode> {
        match self.stream_mut().next() {
            Some((Token::RealOperator(op), _span)) => Ok(OpCode::Real(op)),
            Some((Token::PseudoOperator(op), _span)) => Ok(OpCode::Pseudo(op)),
            Some((got, span)) => Err(ParseError::unexpected(span, got, "expected an opcode".into())),
            None => Err(ParseError::end_of_stream().context("expected an opcode")),
        }
    }

    /// Tries to parse an instruction, which can be either pseudo or concrete.
    pub fn take_instruction(&mut self) -> Result<'t, Instruction> {
        let start = self.boundary_right();

        let opcode = self.apply(Self::take_opcode)?;

        let mut operands = Vec::new();

        let mut first = true;
        loop {
            if !first {
                if !self.assert_token::<()>(Token::ParameterSeparator).is_ok() {
                    break;
                }
            }

            match self.apply(Self::take_operand) {
                Ok(operand) => operands.push(operand),
                Err(_) if first => break,
                Err(err) => return Err(err),
            }

            first = false;
        }

        let end = self.boundary_left();

        Ok(Instruction {
            opcode,
            operands,
            span: start..end,
        })
    }

    /// Takes any number of labels and an instruction from the input stream.
    fn take_part(&mut self) -> Result<'t, Option<Part>> {
        let mut labels = Vec::new();

        // Take any number of labels.
        loop {
            match self.apply(Self::take_symbol) {
                Ok(sym) => labels.push(sym),
                Err(ParseError { kind: ParseErrorKind::EndOfStream, .. }) => return Ok(None),
                Err(_) => break,
            }
        }

        let instruction = self.apply(Self::take_instruction)?;

        Ok(Some(Part {
            labels,
            instruction,
        }))
    }

    /// Tries to parse a whole symbolic program.
    fn take_program(&mut self) -> Result<'t, Program> {
        let take_part = || self.apply(Self::take_part).transpose();

        std::iter::from_fn(take_part)
            .collect::<Result<_>>()
            .map(|parts| Program { parts })
    }
}

/// Parse a single line of assembly.
pub fn parse_line(input: &str)
    -> Result<Part>
{
    Parser::from_str(input)
        .apply(Parser::take_part)
        .transpose()
        .ok_or(ParseError::end_of_stream().context("expected an instruction"))
        .and_then(|res| res) // Collapse the nested Results
}

#[cfg(test)]
mod tests {
    use itertools::Itertools;
    use super::*;

    /// Returns the line number and the column number of the specified offset in the provided input
    /// buffer.
    fn calc_line_col(input: &str, location: usize) -> (usize, usize) {
        input[..location]
            .split('\n')
            .fold((0,0), |(l, _), line| (l+1,line.len()))
    }

    /// Prints the supplied errors in an user friendly format.
    fn print_errors(input: &str, errors: &Vec<ParseError>) {
        for error in errors {
            let index = error.span().map(|s| s.start).unwrap_or(input.len());
            let (error_line, error_col) = calc_line_col(input, index);

            let message = error.context.iter()
                .filter_map(|ctx| match ctx {
                    Context::Error { message } => Some(message),
                    _ => None,
                })
                .join(": ");

            let line = input.split('\n').skip(error_line-1).next().unwrap();
            let prefix = format!("Line {} Column {}: Error: ", error_line, error_col);
            let old_len = line.len();
            let line = line.trim_start();
            let trim_diff = old_len - line.len();
            println!("{}{}", prefix, line);
            print!("{}{} ", " ".repeat(prefix.len() + error_col - trim_diff), "^".repeat(error.span().unwrap().len()));
            println!("{}", message);

            for ctx in &error.context {
                if let Context::Suggestion { span, message } = ctx {
                    let (error_line, error_col) = calc_line_col(input, span.start);

                    let line = input.split('\n').skip(error_line-1).next().unwrap();
                    let prefix = format!("Line {} Column {}: Suggestion: ", error_line, error_col);
                    let old_len = line.len();
                    let line = line.trim_start();
                    let trim_diff = old_len - line.len();
                    println!("{}{}", prefix, line);
                    print!("{}{} ", " ".repeat(prefix.len() + error_col - trim_diff), "^".repeat(span.len()));
                    println!("{}", message);
                }
            }
        }
    }

    #[test]
    fn parse_instructions() {
        let input = r#"
    ; sum - laske annettuja lukuja yhteen kunnes nolla annettu

    Luku  DC    0            ; nykyinen luku
    Summa DC    R0           ; nykyinen summa

    Sum   IN    R1, =KBD	 ; ohjelma alkaa käskystä 0
          STORE Luku
          JZER  R1(R2), Done ; luvut loppu?
        
          LOAD  R1, Summa    ; Summa <- Summa+Luku
          ADDe  R1, Luku	
          STORE R1, Summa    ; summa muuttujassa, ei rekisterissa?

          JUMP  Sum, R0

    Done  LOAD  R1, Summa    ; tulosta summa ja lopeta
          OUpr  R1, ==CRT

          SVC   SP, =HALT
        "#;

        let result = crate::symbolic::program::Program::parse_verbose(input);

        println!("{:?}", result);

        if let Err(errors) = result {
            for error in &errors { 
                println!("Display: {}", error);
            }

            print_errors(input, &errors);
        }
    }
}
