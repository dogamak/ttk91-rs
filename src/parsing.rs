use std::fmt;
use std::ops::Range;
use itertools::Itertools;

#[derive(Clone, Debug)]
pub(crate) struct Error<Context> {
    pub kind: ErrorKind,
    pub context: Vec<Context>,
}

#[derive(Clone, Debug, PartialEq)]
pub(crate) enum ErrorKind {
    EndOfStream,
    UnexpectedToken {
        span: Span,
    },
}

type Span = Range<usize>;

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

pub(crate) trait SeekStream: Iterator {
    fn offset(&self) -> usize;
    fn seek(&mut self, amount: isize);
    fn seek_boundary(&self) -> Range<isize>;
}

pub(crate) struct BufferedStream<S: Iterator> {
    stream: S,
    position: usize,
    buffer: Vec<S::Item>,
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

        backwards .. forwards
    }
}

pub(crate) trait ParseExt<T>: Sized {
    fn apply<P,R,C>(&mut self, parser: P) -> Result<R, Error<C>>
    where
        P: FnOnce(&mut dyn SeekStream<Item=T>) -> Result<R, Error<C>>;
}

impl<S> ParseExt<S::Item> for S
where
    S: SeekStream,
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
}
