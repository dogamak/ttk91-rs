//! Parsing and storing bytecode programs.

mod token;
mod parser;
mod program;

pub use self::program::{
    Program,
    Segment,
};
