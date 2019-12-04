use std::collections::HashMap;
use super::parser::{parse_bytecode_file, ParseError as BytecodeParseError};

#[derive(Debug, Clone, Default)]
pub struct Segment {
    pub start: usize,
    pub content: Vec<u32>,
}

#[derive(Debug, Clone)]
pub struct Program {
    pub code: Segment,
    pub data: Segment,
    pub symbol_table: HashMap<String, usize>,
}

impl Program {
    pub fn parse_bytecode<'a>(bytecode: &'a str) -> Result<Program, BytecodeParseError<'a>> {
        parse_bytecode_file(bytecode)
    }

    pub fn to_words(&self) -> Vec<u32> {
        let size = std::cmp::max(
            self.code.start + self.code.content.len(),
            self.data.start + self.data.content.len());

        let mut v = vec![0; size];

        for (i, word) in self.code.content.iter().enumerate() {
            v[self.code.start + i] = *word;
        }

        for (i, word) in self.data.content.iter().enumerate() {
            v[self.data.start + i] = *word;
        }

        v
    }
}
