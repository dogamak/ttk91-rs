//! Parser for the bytecode text format.

use logos::Logos;

use crate::error::ResultExt;

use crate::parsing::{either, BufferedStream, Either, ParseError, Parser as ParserTrait, Span};

use super::token::{Section, Token};

use super::program::{Program, Segment};
use crate::symbol_table::{SymbolTable, Value};

/// Error types specific to parsing the bytecode format.
#[derive(Debug, Clone)]
pub enum ErrorKind {
    /// A section has a different actual size than what was specified in the section header.
    SectionSizeConflict {
        /// Location of the section header in the input stream.
        span: Span,

        /// The expected size of the section.
        specified: usize,

        /// The number of elements provided in the source.
        got: usize,
    },

    /// A section was defined multiple times.
    RepeatedSection {
        /// The type of the repeated section.
        kind: Section,
    },
}

/// Bytecode format parsing error.
pub type Error<'t> = ParseError<ErrorKind, Token<'t>>;

/// Result of a bytecode parsing operation.
pub type Result<'t, T> = std::result::Result<T, Error<'t>>;

pub(crate) fn parse_bytecode_file(input: &str) -> Result<Program> {
    Parser::parse(input)
}

/// Parser for the bytecode format.
struct Parser<'t> {
    stream: BufferedStream<logos::SpannedIter<'t, Token<'t>>>,
}

impl<'t> ParserTrait<Token<'t>> for Parser<'t> {
    type Stream = BufferedStream<logos::SpannedIter<'t, Token<'t>>>;

    fn stream(&self) -> &Self::Stream {
        &self.stream
    }

    fn stream_mut(&mut self) -> &mut Self::Stream {
        &mut self.stream
    }
}

/// Type that can hold the contents of any of the three sections.
enum SectionContent {
    /// The contents of the `___symboltable___` section.
    SymbolTable(SymbolTable),

    /// The contents of the `___code___` section.
    Code(Segment),

    /// The contents of the `___data___` section.
    Data(Segment),
}

impl SectionContent {
    fn kind(&self) -> Section {
        match self {
            SectionContent::SymbolTable(_) => Section::SymbolTable,
            SectionContent::Code(_) => Section::Code,
            SectionContent::Data(_) => Section::Data,
        }
    }
}

impl<'t> Parser<'t> {
    /// Creates a parser with the given string slice as it's input.
    fn from_str(input: &'t str) -> Parser<'t> {
        let lex = Token::lexer(input);
        let stream = BufferedStream::from(lex.spanned());

        Parser { stream }
    }

    /// Takes a number literal from the input stream.
    fn take_number(&mut self) -> Result<'t, i32> {
        match self.stream_mut().next() {
            Some((Token::Number(num), _)) => Ok(num),
            Some((got, span)) => Err(Error::unexpected(span, got, "a number".into())),
            None => Err(Error::end_of_stream().context("expected a number")),
        }
    }

    /// Creates a parsing operation that takes an section with the specified header from the input
    /// stream.
    ///
    /// The section header contains the start and end addresses of the section and he sections body
    /// consists of a list of number literals.  This matches the format of the `___data___` and
    /// `___code___` sections.
    fn take_section_with_header(
        header: Section,
    ) -> impl FnOnce(&mut Parser<'t>) -> Result<'t, Segment> {
        move |parser| {
            parser
                .assert_token(Token::Section(header))
                .context("Expected ___data___ header")?;

            let header_start = parser.boundary_right();
            let start = parser
                .apply(Self::take_number)
                .context("expected section start address")?;
            let end = parser
                .apply(Self::take_number)
                .context("expected section end address")?;
            let header_end = parser.boundary_left();

            let mut content = Vec::with_capacity((end - start + 1) as usize);

            while let Ok(word) = parser.apply(Self::take_number) {
                content.push(word);
            }

            if content.len() != (end - start + 1) as usize {
                let span = header_start..header_end;

                return Err(Error::other(
                    span.clone(),
                    ErrorKind::SectionSizeConflict {
                        span,
                        specified: (end - start + 1) as usize,
                        got: content.len(),
                    },
                ));
            }

            Ok(Segment {
                start: start as usize,
                content,
            })
        }
    }

    /// Takes a label from the input stream.
    fn take_label(&mut self) -> Result<'t, &'t str> {
        match self.stream_mut().next() {
            Some((Token::Symbol(sym), _)) => Ok(sym),
            Some((got, span)) => Err(Error::unexpected(span, got, "a symbol".into())),
            None => Err(Error::end_of_stream().context("expected a symbol")),
        }
    }

    /// Takes a symbol table section beginning with the `___symboltable___` section header from the
    /// input stream.
    ///
    /// The sections body consists of symbol-value pairs.
    fn take_symbol_table_section(&mut self) -> Result<'t, SymbolTable> {
        let mut table = SymbolTable::new();

        self.assert_token(Token::Section(Section::SymbolTable))
            .context("expected ___symboltable___ header")?;

        while let Ok(label) = self.apply(Self::take_label) {
            let address = self.apply(Self::take_number)?;

            let sym = table.get_or_create(label.to_string());
            sym.set::<Value>(Some(address));
        }

        Ok(table)
    }

    /// Take any of the three sections (`data`, `code` or `symboltable`) from the input stream,
    /// including their headers.
    fn take_section(&mut self) -> Result<'t, SectionContent> {
        let op = either(
            Self::take_symbol_table_section,
            either(
                Self::take_section_with_header(Section::Data),
                Self::take_section_with_header(Section::Code),
            ),
        );

        let section = match self.apply(op)? {
            Either::Right(Either::Left(data)) => SectionContent::Data(data),
            Either::Right(Either::Right(code)) => SectionContent::Code(code),
            Either::Left(st) => SectionContent::SymbolTable(st),
        };

        Ok(section)
    }

    /// Parses a whole bytecode program from the input stream.
    fn parse(input: &'t str) -> Result<Program> {
        let mut parser = Parser::from_str(input);

        let mut symbol_table = None;
        let mut code = None;
        let mut data = None;

        parser.assert_token(Token::Section(Section::Start))?;

        while symbol_table.is_none() || code.is_none() || data.is_none() {
            let start = parser.boundary_right();

            match parser.apply(Self::take_section)? {
                SectionContent::SymbolTable(section) if symbol_table.is_none() => {
                    symbol_table = Some(section)
                }
                SectionContent::Code(section) if code.is_none() => code = Some(section),
                SectionContent::Data(section) if data.is_none() => data = Some(section),
                section => {
                    let end = parser.boundary_left();

                    return Err(Error::other(
                        start..end,
                        ErrorKind::RepeatedSection {
                            kind: section.kind(),
                        },
                    ));
                }
            }
        }

        parser.assert_token(Token::Section(Section::End))?;

        let code = code.unwrap_or_default();
        let data = data.unwrap_or_default();

        Ok(Program {
            symbol_table: symbol_table.unwrap_or_default(),
            source_map: Default::default(),
            code,
            data,
        })
    }
}

#[test]
fn tokenize() {
    let bytecode_file = include_str!("../../tests/hello.b91");
    let lex = Token::lexer(bytecode_file);
    let tokens = lex.into_iter().collect::<Vec<_>>();
    println!("{:?}", tokens);
}
