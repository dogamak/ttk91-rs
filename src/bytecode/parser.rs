use logos::Logos;

use crate::error::ResultExt;

use crate::parsing::{either, BufferedStream, Either, ParseError, Parser as ParserTrait, Span};

use super::token::{Section, Token};

use super::program::{Program, Segment};
use crate::symbol_table::{Label, SymbolTable, Value};

#[derive(Debug)]
pub enum Context {
    RepeatedSection,
    SectionSizeConflict { specified: usize, got: usize },
    Other { message: String },
}

impl From<&str> for Context {
    fn from(s: &str) -> Context {
        Context::Other {
            message: s.to_string(),
        }
    }
}

impl From<String> for Context {
    fn from(s: String) -> Context {
        Context::Other { message: s }
    }
}

#[derive(Debug, Clone)]
pub enum ErrorKind {
    SectionSizeConflict {
        span: Span,
        specified: usize,
        got: usize,
    },
    RepeatedSection {
        kind: Section,
    },
}

pub type Error<'t> = ParseError<ErrorKind, Token<'t>>;
pub type Result<'t, T> = std::result::Result<T, Error<'t>>;

pub(crate) fn parse_bytecode_file(input: &str) -> Result<Program> {
    Parser::parse(input)
}

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

enum SectionContent {
    SymbolTable(SymbolTable),
    Code(Segment),
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
    fn from_str(input: &'t str) -> Parser<'t> {
        let lex = Token::lexer(input);
        let stream = BufferedStream::from(lex.spanned());

        Parser { stream }
    }

    fn take_number(&mut self) -> Result<'t, i32> {
        match self.stream_mut().next() {
            Some((Token::Number(num), _)) => Ok(num),
            Some((got, span)) => Err(Error::unexpected(span, got, "a number".into())),
            None => Err(Error::end_of_stream().context("expected a number")),
        }
    }

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

    fn take_label(&mut self) -> Result<'t, &'t str> {
        match self.stream_mut().next() {
            Some((Token::Symbol(sym), _)) => Ok(sym),
            Some((got, span)) => Err(Error::unexpected(span, got, "a symbol".into())),
            None => Err(Error::end_of_stream().context("expected a symbol")),
        }
    }

    fn take_symbol_table_section(&mut self) -> Result<'t, SymbolTable> {
        let mut table = SymbolTable::new();

        self.assert_token(Token::Section(Section::SymbolTable))
            .context("expected ___symboltable___ header")?;

        while let Ok(label) = self.apply(Self::take_label) {
            let address = self.apply(Self::take_number)?;

            let id = table.get_or_create(label.to_string());
            let sym = table.get_symbol_mut(id);
            sym.set::<Value>(Some(address));
            sym.set::<Label>(Some(label.to_string()));
        }

        Ok(table)
    }

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
