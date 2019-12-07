//! Parsing and storing bytecode programs.

mod parser;
mod program;

pub use self::program::{
    Program,
    Segment,
};
