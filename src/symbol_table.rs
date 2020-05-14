use logos::Span;

use std::collections::HashMap;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;

pub struct SymbolTable<'a> {
    inner: HashMap<&'a str, SymbolTableEntry>,
    id_table: HashMap<SymbolId, &'a str>,
}

#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq)]
pub struct SymbolId(usize);

const SYMBOL_ID_COUNTER: AtomicUsize = AtomicUsize::new(0);

impl Default for SymbolId {
    fn default() -> Self {
        SymbolId(SYMBOL_ID_COUNTER.fetch_add(1, Ordering::SeqCst))
    }
}

#[derive(Clone, Default, Debug)]
pub struct SymbolTableEntry {
    id: SymbolId,
    defined: Option<Span>,
    value: Option<i32>,
    references: Vec<Span>,
}

impl<'a> SymbolTable<'a> {
    pub(crate) fn new() -> Self {
        SymbolTable {
            inner: HashMap::new(),
            id_table: HashMap::new(),
        }
    }

    pub(crate) fn define_symbol(&mut self, span: Span, label: &'a str, value: i32) -> Result<SymbolId, SymbolId> {
        if let Some(symbol) = self.inner.get_mut(label) {
            if symbol.defined.is_some() {
                return Err(symbol.id);
            }

            symbol.defined = Some(span);
            symbol.value = Some(value);

            return Ok(symbol.id);
        }

        let symbol = SymbolTableEntry {
            defined: Some(span),
            value: Some(value),
            .. Default::default()
        };

        let id = symbol.id;

        self.inner.insert(label, symbol);
        self.id_table.insert(id, label);

        Ok(id)
    }

    pub(crate) fn reference_symbol(&mut self, span: Span, label: &'a str) -> SymbolId {
        if let Some(symbol) = self.inner.get_mut(label) {
            symbol.references.push(span);
            return symbol.id;
        }

        let symbol = SymbolTableEntry {
            references: vec![span],
            .. Default::default()
        };

        let id = symbol.id;

        self.inner.insert(label, symbol);
        self.id_table.insert(id, label);

        id
    }

    pub fn get_symbol(&self, id: SymbolId) -> &SymbolTableEntry {
        let label = self.id_table.get(&id).unwrap();
        self.inner.get(label).unwrap()
    }

    pub(crate) fn get_symbol_mut(&mut self, id: SymbolId) -> &mut SymbolTableEntry {
        let label = self.id_table.get(&id).unwrap();
        self.inner.get_mut(label).unwrap()
    }

    pub fn get_symbol_by_label<S: AsRef<str>>(&self, label: S) -> &SymbolTableEntry {
        self.inner.get(label.as_ref()).unwrap()
    }

    pub(crate) fn get_symbol_by_label_mut<S: AsRef<str>>(&mut self, label: S) -> &mut SymbolTableEntry {
        self.inner.get_mut(label.as_ref()).unwrap()
    }
}
