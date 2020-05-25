//! Common error handling functionality.

use std::fmt;

/// Trait for formatting error context types.
/// Used and required only when printing or formatting an [Error].
pub trait ErrorContext {
    /// Returns an user friendly representation of the context type if this type is meant to be
    /// seen by the user.  If the information contained in the type is only meant to be read
    /// programmatically, returns None.
    fn display(&self) -> Option<&str> {
        None
    }
}

/// An error that has a `Kind` and optional list of `Context` instances.
///
/// The `Kind` represents the original root cause of the error, whereas
/// the `Context` type provides additional information.
#[derive(Debug, Clone)]
pub struct Error<Kind, Context> {
    /// The root cause of the error.
    pub(crate) kind: Kind,

    /// Additional information about the error.
    ///
    /// Items closer to the start of the list provide more specific information and items closer to
    /// the tail of the list are more broad and general.
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
    /// Creates a new [Error] of the desired kind. The created error contains no additional
    /// context information.
    pub fn new<T: Into<Kind>>(kind: T) -> Error<Kind, Context> {
        Error {
            kind: kind.into(),
            context: Vec::new(),
        }
    }

    /// Adds context to the error.
    pub fn context<T: Into<Context>>(mut self, ctx: T) -> Self {
        self.context.push(ctx.into());
        self
    }
}

/// Trait which provides additional methods for [Result]s that have an [Error] as the error type.
pub trait ResultExt<C> {
    /// If the [Result] contains an error, adds context to that error.
    fn context<T>(self, ctx: T) -> Self
    where
        T: Into<C>;
}

impl<R, K, C> ResultExt<C> for Result<R, Error<K, C>> {
    fn context<T>(mut self, ctx: T) -> Self
    where
        T: Into<C>,
    {
        if let Err(ref mut err) = self {
            err.context.push(ctx.into());
        }

        self
    }
}
