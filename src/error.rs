use std::fmt::{Display, self};
use nom::error::ErrorKind;

#[derive(Debug, Clone)]
enum InnerError<Kind> {
    Incomplete,
    Context(&'static str),
    Other(Kind),
    Nom(ErrorKind),
}

impl<Kind: Display> fmt::Display for InnerError<Kind> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            InnerError::Context(ctx) => write!(f, "invalid {}", ctx),
            InnerError::Nom(_err) => write!(f, "unexpected input"),
            InnerError::Other(op) => fmt::Display::fmt(op, f),
            InnerError::Incomplete => write!(f, "expected more input"),
        }
    }
}

/// Error type that contains the reason of the error and the unconsumed input.
///
/// For error location information see [ParseError::verbose].
#[derive(Clone, Debug)]
pub struct ParseError<Kind> {
    stack: Vec<(String, InnerError<Kind>)>,
}

impl<Kind> ParseError<Kind> {
    pub(crate) fn from_kind(input: String, kind: Kind) -> ParseError<Kind> {
        ParseError {
            stack: vec![(input, InnerError::Other(kind))],
        }
    }

    pub(crate) fn incomplete() -> ParseError<Kind> {
        ParseError {
            stack: vec![(String::new(), InnerError::Incomplete)],
        }
    }
}

/// Error type containing location information in addition to the reason of the error.
/// 
/// Created from a [ParseError] with [ParseError::verbose].
#[derive(Clone, Debug)]
pub struct VerboseParseError<'a, Kind> {
    /// The line number of the error location.
    pub line: usize,
    /// The column number of the error location.
    pub column: usize,
    kind: InnerError<Kind>,
    rest: &'a str,
}

impl<'a, Kind: Display> fmt::Display for VerboseParseError<'a, Kind> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "at line {} col {}: {}, at '{}'", self.line, self.column, self.kind, self.rest)
    }
}

impl<Kind> ParseError<Kind> {
    /// Calculates the error location information from the [ParseError] and the original input
    /// buffer.
    ///
    /// # Parameters
    /// - `input`: The original input buffer or an exact copy of it.
    pub fn verbose(self, input: &str) -> VerboseParseError<Kind> {
        for (rest, kind) in self.stack {
            let mut line = 1;
            let mut column = 1;

            for ch in input[..input.len()-rest.len()].chars() {
                if ch == '\n' {
                    line += 1;
                    column = 0;
                }

                column += 1;
            }

            let start = input.len() - rest.len();
            let mut end = start;

            for ch in input[start..].chars() {
                if ch == '\n' {
                    break;
                }

                if end - start > 20 {
                    break;
                }

                end += 1;
            }

            let rest = &input[start..end];

            return VerboseParseError {
                line,
                column,
                kind,
                rest,
            };
        }

        unreachable!();
    }
}

impl<Kind: Display> fmt::Display for ParseError<Kind> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (input, kind) = &self.stack[0];

        let end = input
            .chars()
            .enumerate()
            .find_map(|(i, c)| match c {
                '\n' => Some(i),
                _ => None,
            })
            .unwrap_or(20);

        let end = std::cmp::min(end, 20);

        write!(f, "{} at: {}", kind, &input[..end])
    }
}

impl<Kind> nom::error::ParseError<&str> for ParseError<Kind> {
    fn from_error_kind(input: &str, kind: ErrorKind) -> Self {
        ParseError {
            stack: vec![(input.to_string(), InnerError::Nom(kind))],
        }
    }

    fn append(input: &str, kind: ErrorKind, mut other: Self) -> Self {
        other.stack.push((input.to_string(), InnerError::Nom(kind)));
        other
    }

    fn add_context(input: &str, ctx: &'static str, mut other: Self) -> Self {
        other.stack.push((input.to_string(), InnerError::Context(ctx)));
        other
    }
}
