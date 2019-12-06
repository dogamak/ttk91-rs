use std::collections::HashMap;
use std::result::Result as StdResult;

use nom::{
    IResult,
    bytes::complete::{tag, take_while},
    branch::alt,
    combinator::{map, map_res},
    multi::{many0, fold_many0},
    sequence::{delimited, terminated, tuple, preceded, separated_pair},
    error::context,
};

use super::program::{Segment, Program};

#[derive(Debug, Clone)]
pub enum ErrorKind {}

pub type ParseError = crate::error::ParseError<ErrorKind>;
type Result<'a,T> = IResult<&'a str, T, ParseError>;

const SPACE_CHARACTERS: &'static str = " \t";
const NEWLINE_CHARACTERS: &'static str = "\r\n";

fn sp(input: &str) -> Result<&str> {
    take_while(|c| SPACE_CHARACTERS.contains(c))(input)
}

fn newline(input: &str) -> Result<&str> {
    take_while(|c| NEWLINE_CHARACTERS.contains(c))(input)
}

fn parse_usize(s: &str) -> std::result::Result<usize, std::num::ParseIntError> {
    usize::from_str_radix(s, 10)
}

fn parse_u32(s: &str) -> std::result::Result<u32, std::num::ParseIntError> {
    u32::from_str_radix(s, 10)
}

fn is_digit(c: char) -> bool {
    c.is_digit(10)
}

//pub type ParseError<'a> = ::nom::Err<::nom::error::VerboseError<&'a str>>;

pub(crate) fn parse_bytecode_file(input: &str) -> StdResult<Program, ParseError> {
    match parse_bytecode_file_nom(input) {
        Ok((_, program)) => Ok(program),
        Err(nom::Err::Error(err)) | Err(nom::Err::Failure(err)) => Err(err),
        Err(nom::Err::Incomplete(_)) => Err(ParseError::incomplete()),
    }
}

fn parse_segment(header: &'static str) -> impl for<'a> Fn(&'a str) -> Result<'a, Segment> {
    fn _parse_segment<'a>(header: &'static str, input: &'a str) -> Result<'a, Segment> {
        map(
            preceded(
                terminated(tag(header), newline),
                tuple((
                    terminated(
                        separated_pair(take_usize(10), sp, take_usize(10)),
                        newline,
                    ),
                    many0(terminated(take_u32(10), newline)),
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

fn take_symbol_name(input: &str) -> Result<&str> {
    take_while(char::is_alphanumeric)(input)
}

fn take_usize(base: u32) -> impl Fn(&str) -> Result<usize> {
    move |input: &str| map_res(
        take_while(|c: char| c.is_digit(base)),
        |s| usize::from_str_radix(s, base),
    )(input)
}

fn take_u32(base: u32) -> impl Fn(&str) -> Result<u32> {
    move |input: &str| map_res(
        take_while(|c: char| c.is_digit(base)),
        |s| u32::from_str_radix(s, base),
    )(input)
}

fn take_u16(base: u32) -> impl Fn(&str) -> Result<u16> {
    move |input: &str| map_res(
        take_while(|c: char| c.is_digit(base)),
        |s| u16::from_str_radix(s, base),
    )(input)
}

fn take_i32(input: &str) -> Result<u32> {
    alt((
        preceded(tag("0x"), take_u32(16)),
        take_u32(10),
    ))(input)
}

fn parse_symbol_table(input: &str) -> Result<HashMap<String, u16>> {
    preceded(
        preceded(tag("___symboltable___"), newline),
        fold_many0(
            terminated(separated_pair(take_symbol_name, sp, take_u16(10)), newline),
            HashMap::new(),
            |mut m, (symbol, value)| {
                m.insert(symbol.to_string(), value);
                m
            },
        ),
    )(input)
}

fn parse_bytecode_file_nom(input: &str) -> Result<Program> {
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
