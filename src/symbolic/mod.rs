//! Parsing and storing symbolic assembly programs.

pub mod parser;
pub mod program;

pub use self::program::{Program, InitializationTableEntry};
