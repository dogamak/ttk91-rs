//! Types and traits for common parsing functionality.

use std::fmt;
use std::fmt::Write;
use std::ops::Range;

use crate::error::{Error, ErrorContext};

pub type Span = Range<usize>;

pub type ParseError<K, T> = Error<ErrorKind<K, T>, Context>;

/// Common error cases for parsing.  Cases specific to the format being parsed can be defined via
/// the `K` type parameter.
#[derive(Clone, Debug, PartialEq)]
pub enum ErrorKind<K, T> {
    /// The parser encountered an unexpected end of the input stream.
    EndOfStream,

    /// The parser finished successfully, but there was unconsumed data left in the input stream.
    TrailingInput,

    /// The parser encountered an token which it did not expect.
    UnexpectedToken {
        /// Location of the token in the input stream.
        span: Span,

        /// List of user facing descriptions of the types of tokens that were expected.
        ///
        /// Should contain phrases like `a register` or `an instruction`, that can be used in a
        /// phrase like `expected [a register] or [an instruction]`.
        expected: Vec<String>,

        /// The token that was unexpectedly encountered.
        got: T,
    },

    /// Parser or format specific error. 
    Other {
        /// Location where the error occurred.
        span: Span,

        /// Type of the error. Usually an enum.
        kind: K,
    },
}

impl<K, T> fmt::Display for ErrorKind<K, T>
where
    K: fmt::Display,
    T: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ErrorKind::EndOfStream => write!(f, "end of stream"),
            ErrorKind::TrailingInput => write!(f, "trailing input"),
            ErrorKind::UnexpectedToken { expected, got, .. } => {
                let mut expected_str = String::new();

                if expected.len() > 0 {
                    write!(expected_str, "{}", expected[0])?;

                    for i in 1..expected.len() {
                        if i == expected.len() - 1 {
                            write!(expected_str, " or ")?;
                        } else {
                            write!(expected_str, ", ")?;
                        }

                        write!(expected_str, "{}", expected[i])?;
                    }
                }

                write!(f, "expected {}, got '{}'", expected_str, got)
            }
            ErrorKind::Other { kind, .. } => write!(f, "{}", kind),
        }
    }
}

impl<K, T> ParseError<K, T> {
    /// Creates a new [ParseError] with the kind [ErrorKind::EndOfStream].
    pub fn end_of_stream() -> ParseError<K, T> {
        Error {
            kind: ErrorKind::EndOfStream,
            context: vec![],
        }
    }

    /// Creates a new [ParseError] with the kind [ErrorKind::UnexpectedToken].
    pub fn unexpected(span: Span, got: T, expected: String) -> ParseError<K, T> {
        Error {
            kind: ErrorKind::UnexpectedToken {
                span,
                got,
                expected: vec![expected],
            },
            context: Vec::new(),
        }
    }

    /// Creates a new [ParseError] from an parser of format specific error type.
    /// The returned parse error will have a kind of [ErrorKind::Other], with the
    /// [kind](ErrorKind::Other::kind) set to the provided value.
    pub fn other(span: Span, kind: K) -> ParseError<K, T> {
        Error {
            kind: ErrorKind::Other { span, kind },
            context: Vec::new(),
        }
    }

    /// Returns the location of the error relative to the start of the input stream if known.
    pub fn span(&self) -> Option<&Span> {
        match self.kind {
            ErrorKind::EndOfStream => None,
            ErrorKind::TrailingInput => None, // FIXME
            ErrorKind::UnexpectedToken { ref span, .. } => Some(span),
            ErrorKind::Other { ref span, .. } => Some(span),
        }
    }
}

/// Context type for parsing errors.
#[derive(Debug, Clone)]
pub enum Context {
    /// Context information directly relating to the error itself.
    Error { message: String },

    /// Information displayed to the user, but not directly relating to the error itself.
    Suggestion {
        /// Location in the input stream to which this message relates to.
        span: Span,

        /// An user facing message.
        message: String,
    },
}

impl From<&str> for Context {
    fn from(message: &str) -> Context {
        Context::Error {
            message: message.to_string(),
        }
    }
}

impl From<String> for Context {
    fn from(message: String) -> Context {
        Context::Error { message: message }
    }
}

impl ErrorContext for Context {
    fn display(&self) -> Option<&str> {
        match self {
            Context::Error { ref message } => Some(message),
            _ => None,
        }
    }
}

/// A stream that supports seeking.
pub trait SeekStream: Iterator {
    /// Returns the distance from the start of the stream to the current cursor position.
    fn offset(&self) -> usize;

    /// Moves the cursor position in the stream by `amount` items.
    fn seek(&mut self, amount: isize);

    /// Returns the range in which the stream's cursor can move safely.
    fn seek_boundary(&self) -> Range<isize>;

    /// Returns a reference to the item at the defined offset from the stream's start, if such
    /// offset exists in the stream.
    fn at_offset(&self, offset: isize) -> Option<&Self::Item>;
}

impl<S> SeekStream for &mut S
where
    S: SeekStream,
{
    fn offset(&self) -> usize {
        SeekStream::offset(*self)
    }

    fn seek(&mut self, amount: isize) {
        SeekStream::seek(*self, amount)
    }

    fn seek_boundary(&self) -> Range<isize> {
        SeekStream::seek_boundary(*self)
    }

    fn at_offset(&self, offset: isize) -> Option<&Self::Item> {
        SeekStream::at_offset(*self, offset)
    }
}

impl<I> SeekStream for &mut dyn SeekStream<Item = I> {
    fn offset(&self) -> usize {
        SeekStream::offset(*self)
    }

    fn seek(&mut self, amount: isize) {
        SeekStream::seek(*self, amount)
    }

    fn seek_boundary(&self) -> Range<isize> {
        SeekStream::seek_boundary(*self)
    }

    fn at_offset(&self, offset: isize) -> Option<&Self::Item> {
        SeekStream::at_offset(*self, offset)
    }
}

/// An adapter that can be used to create [SeekStream]s from any type implementing the [Iterator]
/// trait.
pub struct BufferedStream<S: Iterator> {
    /// The original iterator from which new items are taken.
    stream: S,

    /// The cursor's position in the stream and the [buffer](BufferedStream::buffer).
    position: usize,

    /// List of all items take from the iterator, in order.
    buffer: Vec<S::Item>,
}

impl<S> BufferedStream<S>
where
    S: Iterator,
{
    /// Resets the streams cursor back to the start of the stream.
    pub fn reset(&mut self) {
        self.position = 0;
    }

    // TODO: Safer API for this.
    /// Returns an mutable reference to the stream's internal buffer.
    pub(crate) fn buffer_mut(&mut self) -> &mut Vec<S::Item> {
        &mut self.buffer
    }

    /// Removes a token at the specified offset from the buffer.
    /// Updates the stream's cursor location if needed.
    pub(crate) fn remove_token(&mut self, index: usize) -> S::Item {
        if index < self.position {
            self.position -= 1;
        }

        self.buffer.remove(index)
    }
}

impl<S> From<S> for BufferedStream<S>
where
    S: Iterator,
{
    fn from(stream: S) -> BufferedStream<S> {
        BufferedStream {
            stream,
            position: 0,
            buffer: Vec::new(),
        }
    }
}

impl<S> Iterator for BufferedStream<S>
where
    S: Iterator,
    S::Item: Clone,
{
    type Item = S::Item;

    fn next(&mut self) -> Option<S::Item> {
        if let Some(item) = self.buffer.get(self.position) {
            self.position += 1;
            return Some(item.clone());
        }

        match self.stream.next() {
            Some(item) => {
                self.position += 1;
                self.buffer.push(item.clone());
                Some(item)
            }
            None => None,
        }
    }
}

impl<S> SeekStream for BufferedStream<S>
where
    S: Iterator,
    S::Item: Clone,
{
    fn offset(&self) -> usize {
        self.position
    }

    fn seek(&mut self, amount: isize) {
        assert!(self.seek_boundary().contains(&amount));
        self.position = ((self.position as isize) + amount) as usize;
    }

    fn seek_boundary(&self) -> Range<isize> {
        let backwards = -(self.position as isize);
        let forwards = (self.buffer.len() as isize) - (self.position as isize);

        backwards..forwards + 1
    }

    fn at_offset(&self, offset: isize) -> Option<&Self::Item> {
        if !self.seek_boundary().contains(&offset) {
            return None;
        }

        let index = (self.position as isize) + offset;

        self.buffer.get(index as usize)
    }
}

/// Trait which provides convinience methods for parsers operating on [SeekStream]s of tokens and
/// their [Span]s.
pub trait Parser<T> {
    /// The token stream type on which the parser operates.
    type Stream: SeekStream<Item = (T, Span)>;

    /// Returns an immutable reference to the stream.
    fn stream(&self) -> &Self::Stream;

    /// Returns a mutable reference to the stream.
    fn stream_mut(&mut self) -> &mut Self::Stream;

    /// Returns the start offset of the next token. Can be used together with
    /// [Parser::boundary_left] to find the span of a token stream.
    fn boundary_right(&mut self) -> usize {
        let stream = self.stream_mut();

        match stream.next() {
            Some((_, span)) => {
                stream.seek(-1);
                span.start
            }
            None => stream.at_offset(0).map(|(_, span)| span.end).unwrap_or(0),
        }
    }

    /// Returns the ending offset of the previous token. Can be used together with
    /// [Parser::boundary_right] to find the span of a token stream.
    fn boundary_left(&mut self) -> usize {
        let stream = self.stream_mut();
        stream.at_offset(-1).map(|t| (t.1).end).unwrap_or(0)
    }

    /// Applies the given parsing operation to the token stream, returning it's result.
    /// If the operation fails, reverts the token stream to its original position.
    fn apply<P, O, C>(&mut self, op: P) -> Result<O, ParseError<C, T>>
    where
        Self: Sized,
        P: Operation<Self, O, C, T>,
        // P: FnOnce(&mut Self) -> Result<R, Error<C>>
    {
        let position = self.stream_mut().offset() as isize;

        let result = op.call(self);

        let stream = self.stream_mut();

        if result.is_err() {
            let delta = position - stream.offset() as isize;
            stream.seek(delta);
        }

        result
    }

    /// Consumes the specified token from the token stream and returns it.
    /// If the next token in the stream is not the wanted token, returns an error.
    fn take_token<X>(&mut self, token: T) -> Result<T, ParseError<X, T>>
    where
        T: std::fmt::Display + PartialEq,
        Self: Sized,
    {
        self.apply(take_token(token))
    }

    /// Consumes the specified token from the token stream.
    /// If the next token in the stream is not the wanted token, returns an error.
    fn assert_token<X>(&mut self, token: T) -> Result<(), ParseError<X, T>>
    where
        T: std::fmt::Display + PartialEq,
        Self: Sized,
    {
        self.apply(assert_token(token))
    }
}

impl<P, T> Parser<T> for &mut P
where
    P: Parser<T>,
{
    type Stream = P::Stream;

    fn stream(&self) -> &Self::Stream {
        (**self).stream()
    }

    fn stream_mut(&mut self) -> &mut Self::Stream {
        (**self).stream_mut()
    }
}

/// A parsing operation.
/// Basically a function of the type `FnOnce(&mut Parser) -> Result<Output, ParseError<Kind,
/// Token>>`.
pub trait Operation<Parser, Output, Kind, Token> {
    fn call<'a>(self, parser: &'a mut Parser) -> Result<Output, ParseError<Kind, Token>>;
}

impl<F, Parser, Output, Kind, Token> Operation<Parser, Output, Kind, Token> for F
where
    F: FnOnce(&mut Parser) -> Result<Output, ParseError<Kind, Token>>,
{
    fn call(self, parser: &mut Parser) -> Result<Output, ParseError<Kind, Token>> {
        self(parser)
    }
}

/// A parsing operation which consumes a specific token from the token stream or returns an error
/// if the next token in the stream is not what was specified.
pub struct AssertToken<T>(T);

impl<P, K, T> Operation<P, (), K, T> for AssertToken<T>
where
    P: Parser<T>,
    T: PartialEq + std::fmt::Display,
{
    fn call(self, parser: &mut P) -> Result<(), ParseError<K, T>> {
        match parser.stream_mut().next() {
            Some((t, _)) if t == self.0 => Ok(()),
            Some((got, span)) => Err(Error {
                kind: ErrorKind::UnexpectedToken {
                    span,
                    got,
                    expected: vec![format!("the token '{}'", self.0)],
                },
                context: Vec::new(),
            }),
            None => Err(Error {
                kind: ErrorKind::EndOfStream,
                context: Vec::new(),
            }),
        }
    }
}

/// A convinience function that creates an [AssertToken] operation.
pub fn assert_token<T>(token: T) -> AssertToken<T> {
    AssertToken(token)
}

/// A parsing operation which consumes a specific token from the token stream and returns the
/// token.  If the next token in the stream is not what was specified, returns an error.
pub struct TakeToken<T>(T);

impl<P, T, X> Operation<P, T, X, T> for TakeToken<T>
where
    P: Parser<T>,
    T: PartialEq + std::fmt::Display,
{
    fn call(self, parser: &mut P) -> Result<T, ParseError<X, T>> {
        match parser.stream_mut().next() {
            Some((t, _)) if t == self.0 => Ok(t),
            Some((got, span)) => Err(Error {
                kind: ErrorKind::UnexpectedToken {
                    span,
                    got,
                    expected: vec![format!("the token '{}'", self.0)],
                },
                context: Vec::new(),
            }),
            None => Err(Error {
                kind: ErrorKind::EndOfStream,
                context: Vec::new(),
            }),
        }
    }
}

/// A convinience function that creates a [TakeToken] operation.
pub fn take_token<T>(token: T) -> TakeToken<T> {
    TakeToken(token)
}

/// An enum that contains either one of the two types `L` and `R`.
pub enum Either<L, R> {
    Left(L),
    Right(R),
}

/// Tries both provided parsing operations and returns the result of the one that succeeds.
/// If neither of the operations succeeds, tries to be clever about the error message that it
/// returns.
/// 
/// In a case where an error is returned, this operation returns the error of the operation that
/// made if furthest in the token stream before failing.  If both operations failed at the same
/// token, this operation joins both operations' error messages, given that they were of the
/// [ErrorKind::UnexpectedToken] type.
pub fn either<P1, P2, R1, R2, K, P, T>(
    parser1: P1,
    parser2: P2,
) -> impl FnOnce(&mut P) -> Result<Either<R1, R2>, ParseError<K, T>>
where
    P: Parser<T>,
    P1: Operation<P, R1, K, T>,
    P2: Operation<P, R2, K, T>,
    T: Clone,
{
    move |parser| {
        let err = match parser.apply(parser1) {
            Ok(r) => return Ok(Either::Left(r)),
            Err(err) => err,
        };

        // TODO: Clean this mess up
        match parser.apply(parser2) {
            Ok(r) => Ok(Either::Right(r)),
            Err(err2) => match (err.span(), err2.span()) {
                (None, None) => Err(err),
                (Some(_), None) => Err(err2),
                (None, Some(_)) => Err(err),
                (Some(span1), Some(span2)) => {
                    if span1.start == span2.start {
                        let mut expected = Vec::new();

                        let mut got = None;

                        if let ErrorKind::UnexpectedToken {
                            expected: e,
                            got: g,
                            ..
                        } = &err.kind
                        {
                            expected.extend(e.iter().cloned());
                            got = Some(g);
                        }

                        if let ErrorKind::UnexpectedToken {
                            expected: e,
                            got: g,
                            ..
                        } = &err2.kind
                        {
                            expected.extend(e.iter().cloned());
                            got = Some(g);
                        }

                        if let Some(got) = got {
                            Err(Error {
                                kind: ErrorKind::UnexpectedToken {
                                    span: span1.clone(),
                                    got: got.clone(),
                                    expected: expected.clone(),
                                },
                                context: Vec::new(),
                            })
                        } else {
                            Err(err)
                        }
                    } else {
                        match span1.start < span2.start {
                            true => Err(err2),
                            false => Err(err),
                        }
                    }
                }
            },
        }
    }
}
