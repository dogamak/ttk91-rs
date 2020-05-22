//! Functions for parsing symbolic assembly programs from strings.
//!
//! The only function you problaly are interested in here is [parse_symbolic_file], which
//! you probably want to use via [Program::parse](crate::symbolic::Program::parse).

use slog::{Logger, Discard, trace, o};

use logos::Logos;

use super::ast::{
    JumpCondition,
    Mode,
    OpCode,
    PseudoOpCode,
    Register,
    Instruction,
    Value,
    ConcreteInstruction,
    PseudoInstruction,
    SymbolicInstruction,
    Program,
    SecondOperand,
};

use crate::parsing::{
    BufferedStream,
    either,
    Either,
    ErrorExt,
    ErrorKind,
    Parser as ParserTrait,
    SeekStream,
    Span,
};

use crate::symbol_table::{SymbolTable, SymbolId, References, Label};

use super::token::Token;

pub type ParseError = crate::parsing::Error<Context>;

/// Provides context for a parsing error. Multiple [Context] instances can be associated with a
/// single [ParseError].
#[derive(Debug, Clone)]
pub enum Context {
    /// This variant provides an suggestion for the user on how to recover from a parsing error.
    /// Alternatively, this can be used to show linter-like warnings to the user when the parser or
    /// the compiler is reasonably sure that the user might have wanted to do something else.
    Suggestion {
        span: Span,
        message: String,
    },

    /// This variant procides context directly relating to the error itself.
    Error {
        message: String,
    },

    /// This variant is used to indicate that the parsing operation itsel was successfull, but
    /// there are tokens left in the input stream.
    TrailingInput,
}

impl From<&str> for Context {
    fn from(s: &str) -> Context {
        Context::Error {
            message: s.to_string(),
        }
    }
}

impl From<String> for Context {
    fn from(s: String) -> Context {
        Context::Error {
            message: s,
        }
    }
}

type Result<T> = std::result::Result<T, ParseError>;

impl<'a,T> ParserTrait<(Token<'a>, Span)> for Parser<'a, T> {
    type Context = State<T>;

    fn span(&self) -> Option<&Span> {
        self.stream.at_offset(-1).map(|t| &t.1)
    }

    fn span_next(&mut self) -> Option<&Span> {
        match self.stream.next() {
            Some(_) => {
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

#[derive(Default)]
pub struct State<T> {
    symbol_table: T,
}

pub struct Parser<'a, T=SymbolTable> {
    logger: Logger,
    stream: BufferedStream<logos::SpannedIter<'a, Token<'a>>>,
    state: State<T>,
}

impl<'a> Parser<'a, SymbolTable> {
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
    pub fn with_symbol_table<T2>(self, symbol_table: T2) -> Parser<'a, T2> {
        Parser {
            logger: self.logger,
            stream: self.stream,
            state: State { symbol_table },
        }
    }

    pub fn set_logger(&mut self, logger: &Logger) {
        self.logger = logger.new(o!("parsing" => true));
    }
}

enum SymbolicOpCode {
    Concrete(OpCode),
    Pseudo(PseudoOpCode),
}

use lazy_static::lazy_static;
use std::collections::HashMap;
use edit_distance::edit_distance;

/// Finds the opcode with the mnemonic that has the shortest edit distance to the provided string.
/// This is used to try and proved helpful suggestions for the user.
fn find_closest_opcode(label: &str) -> &'static SymbolicOpCode {
    lazy_static! {
        static ref MNEMONIC_MAP: HashMap<&'static str, SymbolicOpCode> = {
            let mut map = HashMap::new();

            map.insert("NOP", SymbolicOpCode::Concrete(OpCode::NoOperation));
            map.insert("STORE", SymbolicOpCode::Concrete(OpCode::Store));
            map.insert("LOAD", SymbolicOpCode::Concrete(OpCode::Load));
            map.insert("IN", SymbolicOpCode::Concrete(OpCode::In));
            map.insert("OUT", SymbolicOpCode::Concrete(OpCode::Out));
            map.insert("ADD", SymbolicOpCode::Concrete(OpCode::Add));
            map.insert("SUB", SymbolicOpCode::Concrete(OpCode::Subtract));
            map.insert("MUL", SymbolicOpCode::Concrete(OpCode::Multiply));
            map.insert("DIV", SymbolicOpCode::Concrete(OpCode::Divide));
            map.insert("MOD", SymbolicOpCode::Concrete(OpCode::Modulo));
            map.insert("AND", SymbolicOpCode::Concrete(OpCode::And));
            map.insert("OR", SymbolicOpCode::Concrete(OpCode::Or));
            map.insert("XOR", SymbolicOpCode::Concrete(OpCode::Xor));
            map.insert("SHL", SymbolicOpCode::Concrete(OpCode::ShiftLeft));
            map.insert("SHR", SymbolicOpCode::Concrete(OpCode::ShiftRight));
            map.insert("NOT", SymbolicOpCode::Concrete(OpCode::Not));
            map.insert("COMP", SymbolicOpCode::Concrete(OpCode::Compare));
            map.insert("CALL", SymbolicOpCode::Concrete(OpCode::Call));
            map.insert("EXIT", SymbolicOpCode::Concrete(OpCode::Exit));
            map.insert("PUSH", SymbolicOpCode::Concrete(OpCode::Push));
            map.insert("POP", SymbolicOpCode::Concrete(OpCode::Pop));
            map.insert("PUSHR", SymbolicOpCode::Concrete(OpCode::PushRegisters));
            map.insert("POPR", SymbolicOpCode::Concrete(OpCode::PopRegisters));
            map.insert("SVC", SymbolicOpCode::Concrete(OpCode::SupervisorCall));
            map.insert(
                "JUMP",
                SymbolicOpCode::Concrete(OpCode::Jump {
                    negated: false,
                    condition: JumpCondition::Unconditional,
                }),
            );
            map.insert(
                "JZER",
                SymbolicOpCode::Concrete(OpCode::Jump {
                    negated: false,
                    condition: JumpCondition::Zero,
                }),
            );
            map.insert(
                "JNZER",
                SymbolicOpCode::Concrete(OpCode::Jump {
                    negated: true,
                    condition: JumpCondition::Zero,
                }),
            );
            map.insert(
                "JPOS",
                SymbolicOpCode::Concrete(OpCode::Jump {
                    negated: false,
                    condition: JumpCondition::Positive,
                }),
            );
            map.insert(
                "JNPOS",
                SymbolicOpCode::Concrete(OpCode::Jump {
                    negated: true,
                    condition: JumpCondition::Positive,
                }),
            );
            map.insert(
                "JNEG",
                SymbolicOpCode::Concrete(OpCode::Jump {
                    negated: false,
                    condition: JumpCondition::Negative,
                }),
            );
            map.insert(
                "JNNEG",
                SymbolicOpCode::Concrete(OpCode::Jump {
                    negated: true,
                    condition: JumpCondition::Negative,
                }),
            );
            map.insert(
                "JEQU",
                SymbolicOpCode::Concrete(OpCode::Jump {
                    negated: false,
                    condition: JumpCondition::Equal,
                }),
            );
            map.insert(
                "JNEQU",
                SymbolicOpCode::Concrete(OpCode::Jump {
                    negated: true,
                    condition: JumpCondition::Equal,
                }),
            );
            map.insert(
                "JLES",
                SymbolicOpCode::Concrete(OpCode::Jump {
                    negated: false,
                    condition: JumpCondition::Less,
                }),
            );
            map.insert(
                "JNLES",
                SymbolicOpCode::Concrete(OpCode::Jump {
                    negated: true,
                    condition: JumpCondition::Less,
                }),
            );
            map.insert(
                "JGRE",
                SymbolicOpCode::Concrete(OpCode::Jump {
                    negated: false,
                    condition: JumpCondition::Greater,
                }),
            );
            map.insert(
                "JNGRE",
                SymbolicOpCode::Concrete(OpCode::Jump {
                    negated: true,
                    condition: JumpCondition::Greater,
                }),
            );

            map.insert("DC", SymbolicOpCode::Pseudo(PseudoOpCode::DC));
            map.insert("DS", SymbolicOpCode::Pseudo(PseudoOpCode::DS));
            map.insert("EQU", SymbolicOpCode::Pseudo(PseudoOpCode::EQU));
            
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
    Fixes(Vec<E>),

    /// The parse operation encountered an error from which it could not recover.
    Error(E),
}

impl<'t> Parser<'t, SymbolTable> {
    pub fn parse_instruction(input: &'t str) -> Result<SymbolicInstruction> {
        Parser::<SymbolTable>::from_str(input).apply(Parser::take_instruction)
    }
}

impl<'t, T> Parser<'t, T>
where
    T: std::borrow::BorrowMut<SymbolTable>,
{
    /// Parse a single line of assembly.
    pub fn parse_line(&mut self)
        -> Result<(Option<SymbolId>, SymbolicInstruction)>
    {
        let label = self.apply(Self::take_symbol).ok();

        let instruction = self.apply(Parser::take_instruction)?;

        Ok((label, instruction))
    }

    /// Tries to parse a program written in symbolic TTK91 assembly. Fails on the first
    /// encountered error and returns it.
    fn parse(&mut self) -> Result<Vec<Instruction>> {
        self.stream.reset();
        let res = self.apply(Self::take_program);

        res
    }

    /// Like [Parser::parse], tries to parse a program written in symbolic TTK91 assembly.
    /// Unlike [Parser::parse], this function tries it's best to recover from any syntax errors in
    /// order to provide suggestions on how to fix these errors and continue parsing further.
    pub fn parse_verbose(&mut self) -> std::result::Result<Vec<Instruction>, Vec<ParseError>> {
        match self._parse_verbose(None) {
            IterativeParsingResult::Success(program) => Ok(program),
            IterativeParsingResult::Error(error) => Err(vec![error]),
            IterativeParsingResult::Fixes(errors) => Err(errors),
        }
    }

    fn _parse_verbose(&mut self, previous_error: Option<ParseError>)
        -> IterativeParsingResult<Vec<Instruction>, ParseError>
    {
        let logger = self.logger.clone();

        let error = match self.parse() {
            Ok(program) => {
                if let Some(span) = self.span_next() {
                    trace!(logger, "Trailing Input");
                    let ctx = Context::TrailingInput;
                    return IterativeParsingResult::Error(ParseError::new(span.clone(), ctx));
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

            if let ErrorKind::UnexpectedToken { span: ref error_span } = error.kind {
                if span.start > error_span.start {
                    continue;
                }
            }

            if let Token::Symbol(label) = token {
                let replacement = match find_closest_opcode(label) {
                    SymbolicOpCode::Concrete(op) => Token::Operator(op.clone()),
                    SymbolicOpCode::Pseudo(op) => Token::PseudoOperator(op.clone()),
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
                    IterativeParsingResult::Success(_program) => Some(Vec::new()),
                    IterativeParsingResult::Error(_) => None,
                    IterativeParsingResult::Fixes(fixes) => Some(fixes),
                };

                if let Some(mut errors) = errors {
                    let mut error = error.clone();

                    error.context.push(Context::Suggestion {
                        span: span.clone(),
                        message: format!("Consider changing this to {:?}", replacement),
                    });

                    errors.push(error);

                    fixes.push((1, errors));
                    break;
                }
            }

            let token = self.stream.remove_token(i);

            trace!(logger, "Attempting fix: Remove token"; "token" => ?token);

            let res = self._parse_verbose(Some(error.clone()));
            
            trace!(logger, "Attempting fix: Parse result: {:?}", res);

            self.stream.buffer_mut().insert(i, token);

            let errors = match res {
                IterativeParsingResult::Success(_program) => Some(Vec::new()),
                IterativeParsingResult::Error(_) => None,
                IterativeParsingResult::Fixes(fixes) => Some(fixes),
            };

            if let Some(mut errors) = errors {
                let mut error = error.clone();

                error.context.push(Context::Suggestion {
                    span: span.clone(),
                    message: format!("Consider removing this"),
                });

                errors.push(error);

                fixes.push((2, errors));
            }
        }

        fixes.sort_by_key(|f| f.0);

        if !fixes.is_empty() {
            let (_, fixes) = fixes.remove(0);
            IterativeParsingResult::Fixes(fixes)
        } else {
            IterativeParsingResult::Error(ParseError::eos("unexpected end of stream"))
        }
    }

    /// Tries to parse a "pseudo" opcode, meaning an opcode that has no directly corresponding
    /// instruction and is meant for preprocessing or other stages of the compilation.
    fn take_pseudo_opcode(&mut self) -> Result<PseudoOpCode> {
        match self.stream().next() {
            Some((Token::PseudoOperator(op), _)) => Ok(op),
            Some((_, span)) => Err(ParseError::new(span, "expected a pseudo opcode")),
            None => Err(ParseError::eos("expected a pseudo opcode")),
        }
    }

    /// Tries to parse a "concrete" opcode, meaning an opcode that directly corresponds to an
    /// instruction on the instruction set.
    fn take_concrete_opcode(&mut self) -> Result<OpCode> {
        match self.stream().next() {
            Some((Token::Operator(op), _)) => Ok(op),
            Some((_, span)) => Err(ParseError::new(span, "expected a concrete opcode")),
            None => Err(ParseError::eos("expected a concrete opcode")),
        }
    }

    /// Tries to parse an register (R1-R9, SP or FP).
    fn take_register(&mut self) -> Result<Register> {
        match self.stream().next() {
            Some((Token::Register(reg), _)) => Ok(reg),
            Some((_, span)) => Err(ParseError::new(span, "expected a register")),
            None => Err(ParseError::eos("expected a register")),
        }
    }

    /// Tries to parse an symbol. If required, allocates an entry for the symbol in the
    /// [SymbolTable] and returns the symbol's [SymbolId].
    ///
    /// Any additional symbol metadata (including it's label) can be accessed via the
    /// [SymbolTable].
    fn take_symbol(&mut self) -> Result<SymbolId> {
        match self.stream().next() {
            Some((Token::Symbol(label), span)) => {
                let id = self.context()
                    .symbol_table
                    .borrow_mut()
                    .get_or_create(label.to_string());

                let sym = self.context()
                    .symbol_table
                    .borrow_mut()
                    .get_symbol_mut(id);

                sym.get_mut::<References>().push(span);
                sym.set::<Label>(Some(label.to_string()));

                Ok(id)
            },
            Some((_, span)) => Err(ParseError::new(span, "expected a symbol")),
            None => Err(ParseError::eos("expected a symbol")),
        }
    }

    /// Tries to parse an integer literal.
    fn take_literal(&mut self) -> Result<i32> {
        match self.stream().next() {
            Some((Token::Literal(num), _)) => Ok(num),
            Some((_, span)) => Err(ParseError::new(span, "expected a literal")),
            None => Err(ParseError::eos("expected a literal")),
        }
    }

    /// Tries to parse an addressing mode specifier (either `@` or `=`).
    fn take_modifier(&mut self) -> Result<Mode> {
        let res = self.apply(either(
            Self::take_token(Token::ImmediateModifier),
            Self::take_token(Token::IndirectModifier),
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

    /// Returns a parsing function that either parses an token and returns it or fails.
    fn take_token(token: Token<'t>)
        -> impl FnOnce(&mut Parser<'t,T>) -> Result<Token<'t>>
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

    /// Returns a parsing function which either consumes the specified token or fails.
    fn assert_token(token: Token<'t>)
        -> impl FnOnce(&mut Parser<'t,T>) -> Result<()>
    {
        move |parser| parser.apply(Self::take_token(token)).map(|_| ())
    }

    /// Tries to parse an index register construct, including the parentheses.
    ///
    /// Note that this function returns an [Option] and so succeeds even if no index register
    /// construct is present. However, if there is an opening parenthesis, but the rest of the
    /// constuct is malformed, this function returns an error.
    fn take_index_register(&mut self) -> Result<Option<Register>> {
        if self.apply(Self::assert_token(Token::IndexBegin)).is_ok() {
            let reg = self.apply(Self::take_register)?;
            self.apply(Self::assert_token(Token::IndexEnd))?;

            return Ok(Some(reg));
        }

        Ok(None)
    }

    /// Tries to parse the second operand of an instruction.
    ///
    /// The operand consist of an optional addressing mode specifier, a base operand and an
    /// optional index register. The base operand can be either a symbol, a register or a value and
    /// is the only required component of the operand.
    fn take_second_operand(&mut self) -> Result<SecondOperand> {
        // Take an optional adressing modifier.  Default to direct addressing mode.
        // FIXME: This decision sould not be made by the parser and the AST should express the
        // abence of explicit addressing mode specifier.
        let mode = self.apply(Self::take_modifier)
            .ok()
            .unwrap_or(Mode::Direct);

        // The operand base. A register, a symbol or a literal.
        let value = self.apply(Self::take_value)?;

        // Take the index register if present. Otherwise returns None.
        let index = self.apply(Self::take_index_register)?;

        Ok(SecondOperand {
            mode,
            value,
            index,
        })
    }

    fn take_concrete_instruction(&mut self) -> Result<ConcreteInstruction> {
        let opcode = self.apply(Self::take_concrete_opcode)?;

        // The NOP opcode takes no arguments.
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

        // The jump instructions that examine the state register take only the second operand.
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

        // The PUSHR, POPR and NOT instructions take only the first operand.
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

        // The ParameterSeparator token (a comma) has no syntactial purpose but is required.
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

    /// Tries to parse an "pseudo" instruction, that is, an instruction meant for the preprocessor.
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

    /// Tries to parse an instruction, which can be either pseudo or concrete.
    pub fn take_instruction(&mut self) -> Result<SymbolicInstruction> {
        let p = either(Self::take_concrete_instruction, Self::take_pseudo_instruction);

        match self.apply(p)? {
            Either::Left(ins) => Ok(SymbolicInstruction::Concrete(ins)),
            Either::Right(ins) => Ok(SymbolicInstruction::Pseudo(ins)),
        }
    }

    /// Tries to parse a whole symbolic program.
    fn take_program(&mut self) -> Result<Vec<Instruction>> {
        let mut program = Vec::new();

        'outer: loop {
            let mut labels = Vec::new();

            // Take any number of labels.
            loop {
                match self.apply(Self::take_symbol) {
                    Ok(sym) => labels.push(sym),
                    Err(ParseError { kind: ErrorKind::EndOfStream, .. }) => break 'outer,
                    Err(_) => break,
                }
            }

            // Get the starting position of the current instruction.
            let start = self.span_next().cloned();

            let instruction = self.apply(Self::take_instruction)?;

            // Get the ending position of the current instruction.
            let end = self.span().clone();

            let span = match (start, end) {
                (Some(start), Some(end)) => Some(start.end .. end.start),
                _ => None,
            };

            program.push(Instruction {
                labels,
                instruction,
                span,
            });
        }

        Ok(program)
    }
}

/// Parse a single line of assembly.
pub fn parse_line(input: &str)
    -> Result<(Option<String>, SymbolicInstruction)>
{
    let mut parser = Parser::from_str(input);

    let label = parser.apply(Parser::take_symbol)
        .ok()
        .and_then(|id| parser.state.symbol_table.get_symbol(id).get::<Label>().into_owned());

    let instruction = parser.apply(Parser::take_instruction)?;

    Ok((label, instruction))
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

    Luku  DC    0           ; nykyinen luku
    Summa DC    0           ; nykyinen summa

    Sum   IN    R1, =KBD	; ohjelma alkaa käskystä 0
          STORE R1, Luku
          JZER  R1, Done    ; luvut loppu?
        
          LOAD  R1, Summa   ; Summa <- Summa+Luku
          ADDe   R1, Luku	
          STORE R1, Summa   ; summa muuttujassa, ei rekisterissa?

          JUMP  Sum

    Done  LOAD  R1, Summa   ; tulosta summa ja lopeta
          OUpr   R1, ==CRT

          SVC   SP, =HALT
        "#;

        let mut parser = Parser::from_str(input);

        use slog::Drain;
        let decorator = slog_term::TermDecorator::new().build();
        let drain = slog_term::FullFormat::new(decorator).build().fuse();
        let drain = slog_async::Async::new(drain)
            .overflow_strategy(slog_async::OverflowStrategy::Block)
            .build().fuse();
        parser.set_logger(&Logger::root(drain, o!()));

        let result = parser.parse_verbose();

        println!("{:?}", result);

        if let Err(errors) = result {
            print_errors(input, &errors);
        }
    }
}
