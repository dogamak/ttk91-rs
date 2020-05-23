use std::ops::Range;
use std::fmt;
use std::fmt::Write;

use crate::error::{Error, ErrorContext};

pub type Span = Range<usize>;

pub type ParseError<K,T> = Error<ErrorKind<K,T>, Context>;

#[derive(Clone, Debug, PartialEq)]
pub enum ErrorKind<K,T> {
    EndOfStream,
    TrailingInput,
    UnexpectedToken {
        span: Span,
        expected: Vec<String>,
        got: T,
    },
    Other {
        span: Span,
        kind: K,
    },
}

impl<K,T> fmt::Display for ErrorKind<K,T>
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
                        if i == expected.len()-1 {
                            write!(expected_str, " or ")?;
                        } else {
                            write!(expected_str, ", ")?;
                        }

                        write!(expected_str, "{}", expected[i])?;
                    }
                }

                write!(f, "expected {}, got '{}'", expected_str, got)
            },
            ErrorKind::Other { kind, .. } => write!(f, "{}", kind),
        }
    }
}

impl<K,T> ParseError<K,T> {
    pub fn end_of_stream() -> ParseError<K,T> {
        Error {
            kind: ErrorKind::EndOfStream,
            context: vec![],
        }
    }

    pub fn unexpected(span: Span, got: T, expected: String) -> ParseError<K,T> {
        Error {
            kind: ErrorKind::UnexpectedToken {
                span,
                got,
                expected: vec![expected],
            },
            context: Vec::new(),
        }
    }

    pub fn other(span: Span, kind: K) -> ParseError<K,T> {
        Error {
            kind: ErrorKind::Other {
                span,
                kind,
            },
            context: Vec::new(),
        }
    }

    pub fn span(&self) -> Option<&Span> {
        match self.kind {
            ErrorKind::EndOfStream => None,
            ErrorKind::TrailingInput => None, // FIXME
            ErrorKind::UnexpectedToken { ref span, .. } => Some(span),
            ErrorKind::Other { ref span, .. } => Some(span),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Context {
    Error {
        message: String,
    },
    Suggestion {
        span: Span,
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
        Context::Error {
            message: message,
        }
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

pub trait SeekStream: Iterator {
    fn offset(&self) -> usize;
    fn seek(&mut self, amount: isize);
    fn seek_boundary(&self) -> Range<isize>;
    fn at_offset(&self, offset: isize) -> Option<&Self::Item>;
}

impl<S> SeekStream for &mut S where S: SeekStream {
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

impl<I> SeekStream for &mut dyn SeekStream<Item=I> {
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

pub struct BufferedStream<S: Iterator> {
    stream: S,
    position: usize,
    buffer: Vec<S::Item>,
}

impl<S> BufferedStream<S> where S: Iterator {
    pub fn reset(&mut self) {
        self.position = 0;
    }

    pub fn buffer_mut(&mut self) -> &mut Vec<S::Item> {
        &mut self.buffer
    }

    pub fn remove_token(&mut self, index: usize) -> S::Item {
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
            },
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
        let backwards = - (self.position as isize);
        let forwards = (self.buffer.len() as isize) - (self.position as isize);

        backwards .. forwards + 1
    }

    fn at_offset(&self, offset: isize) -> Option<&Self::Item> {
        if !self.seek_boundary().contains(&offset) {
            return None;
        }

        let index = (self.position as isize) + offset;

        self.buffer.get(index as usize)
    }
}

pub trait Parser<T> {
    type Stream: SeekStream<Item=(T, Span)>;

    fn stream(&self) -> &Self::Stream;
    fn stream_mut(&mut self) -> &mut Self::Stream;

    fn boundary_right(&mut self) -> usize {
        let stream = self.stream_mut();

        match stream.next() {
            Some((_, span)) => {
                stream.seek(-1);
                span.start
            },
            None => stream.at_offset(0)
                .map(|(_, span)| span.end)
                .unwrap_or(0)
        }
    }

    fn boundary_left(&mut self) -> usize {
        let stream = self.stream_mut();
        stream.at_offset(-1).map(|t| (t.1).end).unwrap_or(0)
    }

    fn apply<P,O,C>(&mut self, op: P) -> Result<O,ParseError<C,T>>
    where
        Self: Sized,
        P: Operation<Self,O,C,T>,
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

    fn take_token<X>(&mut self, token: T) -> Result<T, ParseError<X,T>>
    where
        T: std::fmt::Display + PartialEq,
        Self: Sized,
    {
        self.apply(take_token(token))
    }

    fn assert_token<X>(&mut self, token: T) -> Result<(), ParseError<X,T>>
    where
        T: std::fmt::Display + PartialEq,
        Self: Sized,
    {
        self.apply(assert_token(token))
    }
}

impl<P,T> Parser<T> for &mut P where P: Parser<T> {
    type Stream = P::Stream;

    fn stream(&self) -> &Self::Stream {
        (*self).stream()
    }

    fn stream_mut(&mut self) -> &mut Self::Stream {
        (*self).stream_mut()
    }
}

pub trait Operation<Parser,Output,Kind,Token> {
    fn call<'a>(self, parser: &'a mut Parser) -> Result<Output, ParseError<Kind,Token>>;
}

impl<F,Parser,Output,Kind,Token> Operation<Parser,Output,Kind,Token> for F
where
    F: FnOnce(&mut Parser) -> Result<Output, ParseError<Kind,Token>>,
{
    fn call(self, parser: &mut Parser) -> Result<Output, ParseError<Kind,Token>> {
        self(parser)
    }
} 

pub struct AssertToken<T>(T);

impl<P,K,T> Operation<P,(),K,T> for AssertToken<T>
where
    P: Parser<T>,
    T: PartialEq + std::fmt::Display,
{
    fn call(self, parser: &mut P) -> Result<(), ParseError<K,T>> {
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

pub fn assert_token<T>(token: T) -> AssertToken<T> {
    AssertToken(token)
}

pub struct TakeToken<T>(T);

impl<P,T,X> Operation<P,T,X,T> for TakeToken<T>
where
    P: Parser<T>,
    T: PartialEq + std::fmt::Display,
{
    fn call(self, parser: &mut P) -> Result<T, ParseError<X,T>> {
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

pub fn take_token<T>(token: T) -> TakeToken<T> {
    TakeToken(token)
}

/*pub(crate) trait ParseExt<T> {
    fn apply<P,R,C>(&mut self, parser: P) -> Result<R, ParseError<C,T>>
    where
        P: FnOnce(&mut dyn SeekStream<Item=T>) -> Result<R, ParseError<C,T>>;

    fn assert(&mut self, item: T) -> bool where T: PartialEq;
}*/

/*impl<I> ParseExt<I> for &mut dyn SeekStream<Item=I>
{
    fn apply<P,R,C>(&mut self, parser: P) -> Result<R, Error<C>>
    where
        P: FnOnce(&mut dyn SeekStream<Item=I>) -> Result<R, Error<C>>
    {
        let position = self.offset() as isize;
        
        let result = parser(*self);

        if result.is_err() {
            let delta = position - self.offset() as isize;
            self.seek(delta);
        }

        result
    }
}*/

/*impl<S> ParseExt<S::Item> for S where S: SeekStream,
{
    fn apply<P,R,C>(&mut self, parser: P) -> Result<R, Error<C>>
    where
        P: FnOnce(&mut dyn SeekStream<Item=S::Item>) -> Result<R, Error<C>>
    {
        let position = self.offset() as isize;
        
        let result = parser(self);

        if result.is_err() {
            let delta = position - self.offset() as isize;
            self.seek(delta);
        }

        result
    }

    fn assert(&mut self, item: S::Item) -> bool where S::Item: PartialEq {
        match self.next() {
            None => false,
            Some(t) if t == item => true,
            Some(_) => {
                self.seek(-1);
                false
            },
        }
    }
}*/

pub enum Either<L,R> {
    Left(L),
    Right(R),
}

pub fn either<P1,P2,R1,R2,K,P,T>(parser1: P1, parser2: P2)
    -> impl FnOnce(&mut P) -> Result<Either<R1,R2>, ParseError<K,T>>
where
    P: Parser<T>,
    P1: Operation<P,R1,K,T>,
    P2: Operation<P,R2,K,T>,
    T: Clone,
{
    move |parser| {
        let mut err = match parser.apply(parser1) {
            Ok(r) => return Ok(Either::Left(r)),
            Err(err) => err,
        };

        // TODO: Clean this mess up
        match parser.apply(parser2) {
            Ok(r) => Ok(Either::Right(r)),
            Err(mut err2) => match (err.span(), err2.span()) {
                (None, None) => Err(err),
                (Some(_), None) => Err(err2),
                (None, Some(_)) => Err(err),
                (Some(span1), Some(span2)) => {
                    if span1.start == span2.start {
                        let mut expected = Vec::new();

                        let mut got = None;

                        if let ErrorKind::UnexpectedToken { expected: e, got: g, .. } = &err.kind {
                            expected.extend(e.iter().cloned());
                            got = Some(g);
                        }

                        if let ErrorKind::UnexpectedToken { expected: e, got: g, .. } = &err2.kind {
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
                },
            },
        }
    }
}
