use std::fmt;

pub trait ErrorContext {
    fn display(&self) -> Option<&str> {
        None
    }
}

#[derive(Debug, Clone)]
pub struct Error<Kind, Context> {
    pub(crate) kind: Kind,
    pub(crate) context: Vec<Context>,
}

impl<Kind, Context> fmt::Display for Error<Kind, Context>
where
    Kind: fmt::Display,
    Context: ErrorContext,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.kind)?;

        for ctx in &self.context {
            if let Some(s) = ctx.display() {
                write!(f, ": {}", s)?;
            }
        }

        Ok(())
    }
}

impl<Kind, Context> Error<Kind, Context> {
    pub fn new<T: Into<Kind>>(kind: T) -> Error<Kind, Context> {
        Error {
            kind: kind.into(),
            context: Vec::new(),
        }
    }

    pub fn context<T: Into<Context>>(mut self, ctx: T) -> Self {
        self.context.push(ctx.into());
        self
    }
}

pub trait ResultExt<C> {
    fn context<T>(self, ctx: T) -> Self where T: Into<C>;
}

impl<R,K,C> ResultExt<C> for Result<R, Error<K,C>> {
    fn context<T>(mut self, ctx: T) -> Self where T: Into<C> {
        if let Err(ref mut err) = self {
            err.context.push(ctx.into());
        }

        self
    }
}
