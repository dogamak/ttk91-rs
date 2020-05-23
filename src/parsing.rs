use std::fmt;
use std::ops::Range;
use itertools::Itertools;

#[derive(Clone, Debug)]
pub struct Error<Context> {
    pub kind: ErrorKind,
    pub context: Vec<Context>,
}

impl<C> Error<C> {
    pub fn new<T>(span: Span, ctx: T) -> Error<C> where T: Into<C> {
        Error {
            kind: ErrorKind::UnexpectedToken { span },
            context: vec![ctx.into()],
        }
    }

    pub fn eos<T>(ctx: T) -> Error<C> where T: Into<C> {
        Error {
            kind: ErrorKind::EndOfStream,
            context: vec![ctx.into()],
        }
    }

    pub fn span(&self) -> Option<&Span> {
        match self.kind {
            ErrorKind::EndOfStream => None,
            ErrorKind::UnexpectedToken { ref span } => Some(span),
        }
    }
}

pub trait ErrorExt<R,C> {
    fn context<T>(self, ctx: T) -> Self where T: Into<C>;
}

impl<R,C> ErrorExt<R,C> for Result<R, Error<C>> {
    fn context<T>(mut self, ctx: T) -> Self where T: Into<C> {
        if let Err(ref mut err) = self {
            err.context.push(ctx.into());
        }

        self
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum ErrorKind {
    EndOfStream,
    UnexpectedToken {
        span: Span,
    },
}

pub type Span = Range<usize>;

impl<C> fmt::Display for Error<C>
where
    C: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let ctx = self.context.iter()
            .rev()
            .join(": ");

        match self.kind {
            ErrorKind::EndOfStream =>
                write!(f, "{}: unexpected end of stream", ctx),
            ErrorKind::UnexpectedToken { ref span } =>
                write!(f, "error at position {}-{}: {}: unexpected token", span.start, span.end, ctx),
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

    fn apply<P,O,X>(&mut self, op: P) -> Result<O, Error<X>>
    where
        Self: Sized,
        P: Operation<Self,O,X>,
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

    fn take_token<X>(&mut self, token: T) -> Result<T, Error<X>>
    where
        T: PartialEq,
        Self: Sized,
    {
        self.apply(take_token(token))
    }

    fn assert_token<X>(&mut self, token: T) -> Result<(), Error<X>>
    where
        T: PartialEq,
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

pub trait Operation<Parser,Output,Context> {
    fn call<'a>(self, parser: &'a mut Parser) -> Result<Output, Error<Context>>;
}

impl<F,Parser,Output,Context> Operation<Parser,Output,Context> for F
where
    F: FnOnce(&mut Parser) -> Result<Output, Error<Context>>,
{
    fn call(self, parser: &mut Parser) -> Result<Output, Error<Context>> {
        self(parser)
    }
} 

pub struct AssertToken<T>(T);

impl<P,T,X> Operation<P,(),X> for AssertToken<T>
where
    P: Parser<T>,
    T: PartialEq,
{
    fn call(self, parser: &mut P) -> Result<(), Error<X>> {
        match parser.stream_mut().next() {
            Some((t, _)) if t == self.0 => Ok(()),
            Some((_, span)) => Err(Error {
                kind: ErrorKind::UnexpectedToken { span },
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

impl<P,T,X> Operation<P,T,X> for TakeToken<T>
where
    P: Parser<T>,
    T: PartialEq,
{
    fn call(self, parser: &mut P) -> Result<T, Error<X>> {
        match parser.stream_mut().next() {
            Some((t, _)) if t == self.0 => Ok(t),
            Some((_, span)) => Err(Error {
                kind: ErrorKind::UnexpectedToken { span },
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

pub(crate) trait ParseExt<T> {
    fn apply<P,R,C>(&mut self, parser: P) -> Result<R, Error<C>>
    where
        P: FnOnce(&mut dyn SeekStream<Item=T>) -> Result<R, Error<C>>;

    fn assert(&mut self, item: T) -> bool where T: PartialEq;
}

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

impl<S> ParseExt<S::Item> for S where S: SeekStream,
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
}

pub enum Either<L,R> {
    Left(L),
    Right(R),
}

pub fn either<P1,P2,R1,R2,C,P,I>(parser1: P1, parser2: P2)
    -> impl FnOnce(&mut P) -> Result<Either<R1,R2>, Error<C>>
where
    P: Parser<I>,
    P1: Operation<P,R1,C>,
    P2: Operation<P,R2,C>,
{
    move |parser| {
        let err = match parser.apply(parser1) {
            Ok(r) => return Ok(Either::Left(r)),
            Err(err) => err,
        };

        match parser.apply(parser2) {
            Ok(r) => Ok(Either::Right(r)),
            Err(err2) => match (&err.kind, &err2.kind) {
                (ErrorKind::EndOfStream, ErrorKind::EndOfStream) => Err(err),
                (ErrorKind::UnexpectedToken {..}, ErrorKind::EndOfStream) => Err(err2),
                (ErrorKind::EndOfStream, ErrorKind::UnexpectedToken {..}) => Err(err),
                (
                    ErrorKind::UnexpectedToken { span: span1 },
                    ErrorKind::UnexpectedToken { span: span2 },
                ) => match span1.start < span2.start {
                    true => Err(err2),
                    false => Err(err),
                },
            },
        }
    }
}
