use std::collections::HashMap;

use nom::{
    IResult,
    bytes::complete::{tag, take_while},
    combinator::map_res,
    multi::{many0, fold_many0},
    sequence::{terminated, tuple},
    error::context,
};

use super::program::{Segment, Program};

/*impl Program {
    fn as_bytes(&self) -> Vec<u8> {
        let memory_size = std::cmp::max(self.code.end+1, self.data.end+1)*4;
        let mut buffer = vec![0; memory_size];

        for (i, addr) in (self.code.start..=self.code.end).enumerate() {
            let bytes = self.code.content[i].to_be_bytes();
            buffer[addr*4+0] = bytes[0];
            buffer[addr*4+1] = bytes[1];
            buffer[addr*4+2] = bytes[2];
            buffer[addr*4+3] = bytes[3];
        }

        for (i, addr) in (self.data.start..=self.data.end).enumerate() {
            let bytes = self.data.content[i].to_be_bytes();
            buffer[addr*4+0] = bytes[0];
            buffer[addr*4+1] = bytes[1];
            buffer[addr*4+2] = bytes[2];
            buffer[addr*4+3] = bytes[3];
        }

        buffer
    }
}*/

fn parse_usize(s: &str) -> Result<usize, std::num::ParseIntError> {
    usize::from_str_radix(s, 10)
}

fn parse_u32(s: &str) -> Result<u32, std::num::ParseIntError> {
    u32::from_str_radix(s, 10)
}

fn is_digit(c: char) -> bool {
    c.is_digit(10)
}

pub type ParseError<'a> = ::nom::Err<::nom::error::VerboseError<&'a str>>;

pub(crate) fn parse_bytecode_file(input: &str) -> Result<Program, ParseError> {
    match parse_bytecode_file_nom(input) {
        Ok((_, program)) => Ok(program),
        Err(e) => Err(e),
    }
}

fn parse_bytecode_file_nom(input: &str) -> IResult<&str, Program, ::nom::error::VerboseError<&str>> {
    let (input, _) = context(
        "expected ___b91___ header",
        tag("___b91___\r\n"))(input)?;

    let (input, _) = context(
        "expected ___code___ header",
        tag("___code___\r\n"))(input)?;

    let take_usize = map_res(take_while(is_digit), parse_usize);
    let take_u32 = map_res(take_while(is_digit), parse_u32);
    let take_symbol_name = take_while(|c| c != ' ');

    let (input, code_start) = take_usize(input)?;
    let (input, _) = tag(" ")(input)?;
    let (input, code_end) = take_usize(input)?;
    let (input, _) = tag("\r\n")(input)?;

    let (input, code) = many0(terminated(&take_u32, tag("\r\n")))(input)?;

    let (input, _) = tag("___data___\r\n")(input)?;

    let (input, data_start) = take_usize(input)?;
    let (input, _) = tag(" ")(input)?;
    let (input, data_end) = take_usize(input)?;
    let (input, _) = tag("\r\n")(input)?;
    let (input, data) = many0(terminated(&take_u32, tag("\r\n")))(input)?;

    let (input, _) = tag("___symboltable___\r\n")(input)?;

    let (input, symbol_table) = fold_many0(
        tuple((take_symbol_name, tag(" "), take_usize, tag("\r\n"))),
        HashMap::new(),
        |mut m, t| {
            m.insert(t.0.to_string(), t.2);
            m
        })(input)?;

    let (input, _) = tag("___end___\r\n")(input)?;

    Ok((input, Program {
        code: Segment {
            start: code_start,
            //end: code_end,
            content: code,
        },

        data: Segment {
            start: data_start,
            //end: data_end,
            content: data,
        },

        symbol_table,
    }))
}
