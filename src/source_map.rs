//! Mapping between memory locations and source code spans.

use std::collections::HashMap;
use std::iter::FromIterator;

use crate::parsing::{Span, LineSpan, AsLineSpan};

/// Mapping from memory addresses into source code spans. This type is generic
/// over the span type. Most common types for the generic `V` are [Span] and [LineSpan].
#[derive(Debug, Clone, Default)]
pub struct SourceMap<V> {
    inner: HashMap<usize, V>,
}

impl<V> FromIterator<(usize, V)> for SourceMap<V> {
    fn from_iter<I>(iter: I) -> Self
        where I: IntoIterator<Item = (usize, V)>
    {
        SourceMap {
            inner: HashMap::from_iter(iter),
        }
    }
}

impl<V> SourceMap<V> {
    /// Returns the span in the original source code which
    /// defined the value for the given memory location.
    pub fn get_source_span(&self, addr: usize) -> Option<&V> {
        self.inner.get(&addr)
    }
}

impl SourceMap<Span> {
    /// Converts a [SourceMap] containing character offset based spans ([Span])
    /// into one containing line and column number based spans ([LineSpan]).
    pub fn into_line_based(self, source: &str) -> SourceMap<LineSpan> {
        SourceMap {
            inner: self.inner.into_iter()
                .map(|(addr, span)| (addr, span.as_line_span(source)))
                .collect(),
        }
    }
}
