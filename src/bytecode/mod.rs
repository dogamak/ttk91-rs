//! Parsing and storing bytecode programs.

pub mod parser;
mod program;
mod token;

pub use self::program::{Program, Segment};
