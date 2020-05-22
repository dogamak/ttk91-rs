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

pub(crate) struct BufferedStream<S: Iterator> {
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
    type Context;

    fn parts(&mut self) -> (&mut dyn SeekStream<Item=T>, &mut Self::Context);

    fn span(&self) -> Option<&Span>;
    fn span_next(&mut self) -> Option<&Span>;

    fn stream(&mut self) -> &mut dyn SeekStream<Item=T> {
        self.parts().0
    }

    fn context<'a>(&'a mut self) -> &'a mut Self::Context where T: 'a {
        self.parts().1
    }

    fn apply<P,R,C>(&mut self, parser: P) -> Result<R, Error<C>>
    where
        P: FnOnce(&mut Self) -> Result<R, Error<C>>
    {
        let position = self.stream().offset() as isize;
        
        let result = parser(self);

        if result.is_err() {
            let delta = position - self.stream().offset() as isize;
            self.stream().seek(delta);
        }

        result
    }
}

impl<P,T> Parser<T> for &mut P where P: Parser<T> {
    type Context = P::Context;

    fn parts(&mut self) -> (&mut dyn SeekStream<Item=T>, &mut Self::Context) {
        (**self).parts()
    }

    fn span(&self) -> Option<&Span> {
        (**self).span()
    }

    fn span_next(&mut self) -> Option<&Span> {
        (**self).span_next()
    }
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
    P1: FnOnce(&mut P) -> Result<R1, Error<C>>,
    P2: FnOnce(&mut P) -> Result<R2, Error<C>>,
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
