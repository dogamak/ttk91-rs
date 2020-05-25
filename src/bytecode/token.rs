//! Lexer and an enumeration of the tokens that make up the bytecode format.

use logos::Logos;
use std::fmt;
use std::str::FromStr;

/// A section header.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Section {
    /// Start of the bytecode file.
    Start,

    /// End of the bytecode file.
    End,

    /// Start of the code section.
    Code,

    /// Start of the data section.
    Data,

    /// Start of the symbol table section.
    SymbolTable,
}

impl fmt::Display for Section {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Section::Start => write!(f, "___b91___"),
            Section::End => write!(f, "___end___"),
            Section::Code => write!(f, "___code___"),
            Section::Data => write!(f, "___data___"),
            Section::SymbolTable => write!(f, "___symboltable___"),
        }
    }
}

impl FromStr for Section {
    type Err = ();

    fn from_str(input: &str) -> Result<Section, ()> {
        match input {
            "___b91___" | "b91" => Ok(Section::Start),
            "___end___" | "end" => Ok(Section::End),
            "___code___" | "code" => Ok(Section::Code),
            "___data___" | "data" => Ok(Section::Data),
            "___symboltable___" | "symboltable" => Ok(Section::SymbolTable),
            _ => Err(()),
        }
    }
}

/// Enumeration of the all possible token.
#[derive(Logos, Debug, Clone, PartialEq)]
pub enum Token<'t> {
    /// An errorneous token that cannot be interpreted as any of the other tokens.
    #[error]
    #[regex(r"[ \t\f\r\n]+", logos::skip)]
    Error,

    /// A section header that starts and ends with three underscores.
    #[regex("___(b91|code|data|symboltable|end)___", |lex| lex.slice().parse())]
    Section(Section),

    /// A signed number literal.
    #[regex("-?[0-9]+", |lex| lex.slice().parse())]
    Number(i32),

    /// A symbol that begins with a letter or an underscore and can contain the characters
    /// `A-Za-z0-9_`.
    #[regex("(?i)[a-z_][a-z0-9_]*")]
    Symbol(&'t str),
}

impl<'t> fmt::Display for Token<'t> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Token::Error => write!(f, "<error>"),
            Token::Section(section) => write!(f, "{}", section),
            Token::Number(num) => write!(f, "{}", num),
            Token::Symbol(label) => write!(f, "{}", label),
        }
    }
}
