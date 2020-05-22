use std::result::Result as StdResult;

use crate::symbol_table::{SymbolTable, Address};

use nom::{
    IResult,
    bytes::complete::{tag, take_while},
    combinator::{map, map_res},
    multi::{many0, fold_many0},
    sequence::{delimited, terminated, tuple, preceded, separated_pair},
};

use super::program::{Segment, Program};

use nom_locate::LocatedSpan;

type Span<'a> = LocatedSpan<&'a str>;

/// Represents error specific to bytecode file parsing.
#[derive(Debug, Clone)]
pub enum ErrorKind {}

/// Represents an error which has prevented the bytecode file from being parsed.
pub type ParseError = crate::error::ParseError<ErrorKind>;
type Result<'a,T> = IResult<Span<'a>, T, ParseError>;

const SPACE_CHARACTERS: &'static str = " \t";
const NEWLINE_CHARACTERS: &'static str = "\r\n";

fn sp(input: Span) -> Result<Span> {
    take_while(|c| SPACE_CHARACTERS.contains(c))(input)
}

fn newline(input: Span) -> Result<Span> {
    take_while(|c| NEWLINE_CHARACTERS.contains(c))(input)
}

pub(crate) fn parse_bytecode_file(input: Span) -> StdResult<Program, ParseError> {
    match parse_bytecode_file_nom(input) {
        Ok((_, program)) => Ok(program),
        Err(nom::Err::Error(err)) | Err(nom::Err::Failure(err)) => Err(err),
        Err(nom::Err::Incomplete(_)) => Err(ParseError::incomplete()),
    }
}

fn parse_segment(header: &'static str) -> impl for<'a> Fn(Span<'a>) -> Result<'a, Segment> {
    fn _parse_segment<'a>(header: &'static str, input: Span<'a>) -> Result<'a, Segment> {
        map(
            preceded(
                terminated(tag(header), newline),
                tuple((
                    terminated(
                        separated_pair(take_usize(10), sp, take_usize(10)),
                        newline,
                    ),
                    many0(terminated(map(take_u32(10), |i| i as i32), newline)),
                ))
            ),
            |((start, _end), content)| Segment {
                start,
                content,
            },
        )(input)
    }

    move |input| _parse_segment(header, input)
}

fn take_symbol_name(input: Span) -> Result<Span> {
    take_while(char::is_alphanumeric)(input)
}

fn take_usize(base: u32) -> impl Fn(Span) -> Result<usize> {
    move |input: Span| map_res(
        take_while(|c: char| c.is_digit(base)),
        |s: Span| usize::from_str_radix(s.fragment, base),
    )(input)
}

fn take_u32(base: u32) -> impl Fn(Span) -> Result<u32> {
    move |input: Span| map_res(
        take_while(|c: char| c.is_digit(base)),
        |s: Span| u32::from_str_radix(s.fragment, base),
    )(input)
}

fn take_u16(base: u32) -> impl Fn(Span) -> Result<u16> {
    move |input: Span| map_res(
        take_while(|c: char| c.is_digit(base)),
        |s: Span| u16::from_str_radix(s.fragment, base),
    )(input)
}

fn parse_symbol_table(input: Span) -> Result<SymbolTable> {
    preceded(
        preceded(tag("___symboltable___"), newline),
        fold_many0(
            terminated(separated_pair(take_symbol_name, sp, take_u16(10)), newline),
            SymbolTable::new(),
            |mut m, (symbol, value)| {
                let id = m.define_symbol(0..0, symbol.to_string(), value as i32).unwrap();
                m.get_symbol_mut(id).set::<Address>(Some(value));
                // m.insert(symbol.to_string(), value);
                m
            },
        ),
    )(input)
}

fn parse_bytecode_file_nom(input: Span) -> Result<Program> {
    map(
        delimited(
            preceded(tag("___b91___"), newline),
            tuple((
                    parse_segment("___code___"),
                    parse_segment("___data___"),
                    parse_symbol_table,
            )),
            preceded(tag("___end___"), newline),
        ),
        |(code, data, symbol_table)| Program {
            code,
            data,
            symbol_table,
        },
    )(input)
}
