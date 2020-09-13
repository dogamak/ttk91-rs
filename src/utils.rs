pub struct Span = Range<usize>;

pub struct LineLocation {
    pub line: usize,
    pub column: usize,
}

pub type LineSpan = Range<LineLocation>;
