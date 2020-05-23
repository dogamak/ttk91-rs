//! Parsing and storing bytecode programs.

mod token;
pub mod parser;
mod program;

pub use self::program::{
    Program,
    Segment,
};
