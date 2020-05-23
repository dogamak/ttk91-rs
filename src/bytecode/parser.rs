use std::result::Result as StdResult;
use logos::Logos;

use crate::parsing::{
    Parser as ParserTrait,
    BufferedStream,
    Error as ParseError,
    ErrorExt,
    Either,
    either,
};

use super::token::{
    Token,
    Section,
};

use crate::symbol_table::{SymbolTable, Value, Label};
use super::program::{Segment, Program};

#[derive(Debug)]
pub enum Context {
    RepeatedSection,
    SectionSizeConflict {
        specified: usize,
        got: usize,
    },
    Other {
        message: String,
    },
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
        Context::Other {
            message: s,
        }
    }
}

pub type Error = ParseError<Context>;
pub type Result<T> = std::result::Result<T, Error>;

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


impl<'t> Parser<'t> {
    fn from_str(input: &'t str) -> Parser<'t> {
        let lex = Token::lexer(input);
        let stream = BufferedStream::from(lex.spanned());

        Parser {
            stream,
        }
    }
    
    fn take_number(&mut self) -> Result<i32> {
        match self.stream_mut().next() {
            Some((Token::Number(num), _)) => Ok(num),
            Some((_, span)) => Err(Error::new(span, "expected a number")),
            None => Err(Error::eos("expected a number")),
        }
    }

    fn take_word_sequence(&mut self) -> Result<Vec<i32>> {
        let mut words = Vec::new();

        while let Ok(word) = self.apply(Self::take_number) {
            words.push(word);
        }

        Ok(words)
    }

    fn take_section_with_header(header: Section) -> impl FnOnce(&mut Parser<'t>) -> Result<Segment> {
        move |parser| {
            parser.assert_token(Token::Section(header))
                .context("Expected ___data___ header")?;

            let header_start = parser.boundary_right().unwrap();
            let start = parser.apply(Self::take_number)
                .context("expected section start address")?;
            let end = parser.apply(Self::take_number)
                .context("expected section end address")?;
            let header_end = parser.boundary_left().unwrap();

            let mut content = Vec::with_capacity((end - start + 1) as usize);

            while let Ok(word) = parser.apply(Self::take_number) {
                content.push(word);
            }

            if content.len() != (end - start + 1) as usize {
                let span = header_start .. header_end;

                return Err(Error::new(span, Context::SectionSizeConflict {
                    specified: (end - start + 1) as usize,
                    got: content.len(),
                }));
            }

            Ok(Segment {
                start: start as usize,
                content,
            })
        }
    }

    fn take_label(&mut self) -> Result<&'t str> {
        match self.stream_mut().next() {
            Some((Token::Symbol(sym), _)) => Ok(sym),
            Some((_, span)) => Err(Error::new(span, "expected a symbol")),
            None => Err(Error::eos("expected a symbol")),
        }
    }

    fn take_symbol_table_section(&mut self) -> Result<SymbolTable> {
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

    fn take_section(&mut self) -> Result<SectionContent> {
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
            let start = parser.boundary_right().unwrap();

            match parser.apply(Self::take_section)? {
                SectionContent::SymbolTable(section) if symbol_table.is_none() => symbol_table = Some(section),
                SectionContent::Code(section) if code.is_none() => code = Some(section),
                SectionContent::Data(section) if data.is_none() => data = Some(section),
                _ => {
                    let end = parser.boundary_left().unwrap();

                    return Err(Error::new(start..end, Context::RepeatedSection));
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
