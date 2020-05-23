use super::parser::{parse_bytecode_file, Error};
use crate::symbol_table::SymbolTable;

#[derive(Debug, Clone, Default)]
pub struct Segment {
    pub start: usize,
    pub content: Vec<i32>,
}

#[derive(Debug, Clone)]
pub struct Program {
    pub code: Segment,
    pub data: Segment,
    pub symbol_table: SymbolTable,
}

impl Program {
    pub fn parse<'a>(bytecode: &'a str) -> Result<Program, Error> {
        parse_bytecode_file(bytecode)
    }

    pub fn to_words(&self) -> Vec<i32> {
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
