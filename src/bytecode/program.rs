//! Bytecode program containing instructions, data and a symbol table.

use crate::parsing::Span;
use crate::source_map::SourceMap;
use super::parser::{parse_bytecode_file, Error};
use crate::symbol_table::SymbolTable;

/// A memory segment of a bytecode program that contains data or instructions.
#[derive(Debug, Clone, Default)]
pub struct Segment {
    /// Memory address at which the segment starts.
    pub start: usize,

    /// The contents of the segment as words.
    pub content: Vec<i32>,
}

/// A bytecode program consisting of instructions, data and a symbol table.
#[derive(Debug, Clone)]
pub struct Program {
    pub code: Segment,
    pub data: Segment,
    pub symbol_table: SymbolTable,
    pub source_map: SourceMap<Span>,
}

impl Program {
    /// Parse a bytecode program from its textual representation.
    pub fn parse<'a>(bytecode: &'a str) -> Result<Program, Error> {
        parse_bytecode_file(bytecode)
    }

    /// Convert a bytecode program to a list of words.
    pub fn to_words(&self) -> Vec<i32> {
        let size = std::cmp::max(
            self.code.start + self.code.content.len(),
            self.data.start + self.data.content.len(),
        );

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
