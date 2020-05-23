use logos::Logos;
use std::str::FromStr;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Section {
    Start,
    End,
    Code,
    Data,
    SymbolTable,
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

#[derive(Logos, Debug, Clone, PartialEq)]
pub enum Token<'t> {
    #[error]
    #[regex(r"[ \t\f\r\n]+", logos::skip)]
    Error,

    #[regex("___(b91|code|data|symboltable|end)___", |lex| lex.slice().parse())]
    Section(Section),

    #[regex("-?[0-9]+", |lex| lex.slice().parse())]
    Number(i32),

    #[regex("(?i)[a-z_][a-z0-9_]*")]
    Symbol(&'t str),
}
