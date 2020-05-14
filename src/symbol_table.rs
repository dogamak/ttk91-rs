use logos::Span;

use std::collections::HashMap;
use std::marker::PhantomData;
use std::any::{Any, TypeId};
use std::fmt::Debug;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;

use crate::compiler::CompileTarget;

#[derive(Default, Debug, Clone)]
pub struct SymbolTable {
    inner: HashMap<String, SymbolInfo>,
    id_table: HashMap<SymbolId, String>,
}

impl std::fmt::Debug for SymbolInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let mut builder = f.debug_map();

        for info in self.map.values() {
            builder.key(&info.name());
            info.debug_fmt(&mut builder);
        }

        builder.finish()
    }
}

#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq)]
pub struct SymbolId(usize);

static SYMBOL_ID_COUNTER: AtomicUsize = AtomicUsize::new(0);

impl Default for SymbolId {
    fn default() -> Self {
        SymbolId(SYMBOL_ID_COUNTER.fetch_add(1, Ordering::SeqCst))
    }
}

macro_rules! impl_field_type {
    ( $name:ident, $value:ty ) => {
        pub struct $name;

        impl SymbolTableField for $name {
            const NAME: &'static str = stringify!($name);
            type Value = $value;
        }
    };
}

impl_field_type!(Defined, Option<Span>);
impl_field_type!(Value, Option<i32>);
impl_field_type!(References, Vec<Span>);
impl_field_type!(Label, Option<String>);
impl_field_type!(Address, Option<u16>);

impl SymbolTableField for SymbolId {
    const NAME: &'static str = "SymbolId";
    type Value = SymbolId;
}

#[derive(Clone, Copy)]
pub struct Location<T> {
    loc: PhantomData<T>,
}

impl<T> SymbolTableField for Location<T> where T: CompileTarget {
    const NAME: &'static str = "Location";
    type Value = Option<T::Location>;
}

pub trait SymbolTableField {
    const NAME: &'static str;
    type Value: Default + Clone + Debug;
}

struct SymbolTableEntry<F: SymbolTableField> {
    value: F::Value,
}

impl<F> std::fmt::Debug for SymbolTableEntry<F>
where
    F: SymbolTableField,
{
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{:?}", self.value)
    }
}

trait SymbolTableEntryTrait {
    fn clone(&self) -> Box<dyn SymbolTableEntryTrait>;
    fn name(&self) -> &str;
    fn debug_fmt(&self, f: &mut std::fmt::DebugMap);
    fn get_value(&self) -> &dyn Any;
    fn get_value_mut(&mut self) -> &mut dyn Any;
    fn into_value(self: Box<Self>) -> Box<dyn Any>;
}

impl<T> SymbolTableEntryTrait for SymbolTableEntry<T>
where 
    T: SymbolTableField + 'static,
    T::Value: Clone + 'static,
{
    fn clone(&self) -> Box<dyn SymbolTableEntryTrait> {
        Box::new(SymbolTableEntry::<T> {
            value: self.value.clone(),
        })
    }

    fn name(&self) -> &str {
        T::NAME
    }

    fn debug_fmt(&self, f: &mut std::fmt::DebugMap) {
        f.value(&self.value);
    }

    fn get_value(&self) -> &dyn Any {
        &self.value
    }

    fn get_value_mut(&mut self) -> &mut dyn Any {
        &mut self.value
    }
    
    fn into_value(self: Box<Self>) -> Box<dyn Any> {
        self as Box<dyn Any>
    }
}

#[derive(Default)]
pub struct SymbolInfo {
    map: HashMap<TypeId, Box<dyn SymbolTableEntryTrait>>,
}

impl Clone for SymbolInfo {
    fn clone(&self) -> SymbolInfo {
        let map = self.map.iter()
            .map(|(type_id, boxed)| ( *type_id, SymbolTableEntryTrait::clone(&**boxed) ))
            .collect();

        SymbolInfo { map }
    }
}

use std::borrow::Cow;

impl SymbolInfo {
    pub fn set<F: SymbolTableField + 'static>(&mut self, value: F::Value) -> Option<F::Value> {
        let id = TypeId::of::<F>();
        println!("Set ({}) {:?} = {:?}", F::NAME, id, value);

        self.map.insert(id, Box::new(SymbolTableEntry::<F> { value }))
            .and_then(|entry| entry.into_value().downcast().ok().map(|b| *b))
    }

    pub fn get<F: SymbolTableField + 'static>(&self) -> Cow<F::Value> {
        let id = TypeId::of::<F>();

        if let Some(s) = self.map.get(&TypeId::of::<F>()) {
            let r = s.get_value().downcast_ref().unwrap();
            println!("Get ({}) {:?} = {:?}", F::NAME, id, r);
            Cow::Borrowed(r)
        } else {
            let v = Default::default();
            println!("Get ({}) {:?} = {:?} (default)", F::NAME, id, v);
            Cow::Owned(v)
        }
    }

    pub fn get_mut<F>(&mut self) -> &mut F::Value
    where
        F: SymbolTableField + 'static,
    {
        self.map.entry(TypeId::of::<F>())
            .or_insert_with(|| Box::new(SymbolTableEntry::<F> { value: Default::default() }))
            .get_value_mut().downcast_mut().unwrap()
    }
}

#[derive(Clone, Default, Debug)]
pub struct _SymbolTableEntry {
    id: SymbolId,
    label: String,
    location: usize,
    defined: Option<Span>,
    value: Option<i32>,
    references: Vec<Span>,
}

impl SymbolTable {
    pub(crate) fn new() -> Self {
        SymbolTable {
            inner: HashMap::new(),
            id_table: HashMap::new(),
        }
    }

    pub(crate) fn iter_mut(&mut self) -> impl Iterator<Item=&mut SymbolInfo> {
        self.inner.values_mut()

    }

    pub(crate) fn define_symbol(&mut self, span: Span, label: String, value: i32) -> Result<SymbolId, SymbolId> {
        if let Some(symbol) = self.inner.get_mut(&*label) {
            let id = *symbol.get::<SymbolId>();

            if symbol.get::<Defined>().is_some() {
                return Err(id);
            }

            symbol.set::<Defined>(Some(span));
            symbol.set::<Value>(Some(value));

            return Ok(id);
        }

        let mut symbol = SymbolInfo::default();

        let id = SymbolId::default();
        symbol.set::<SymbolId>(id);

        symbol.set::<Defined>(Some(span));
        symbol.set::<Value>(Some(value));
        symbol.set::<Label>(Some(label.clone()));

        self.inner.insert(label.clone(), symbol);
        self.id_table.insert(id, label);

        Ok(id)
    }

    pub(crate) fn reference_symbol(&mut self, span: Span, label: String) -> SymbolId {
        if let Some(symbol) = self.inner.get_mut(&*label) {
            symbol.get_mut::<References>().push(span);
            return *symbol.get::<SymbolId>();
        }

        let mut symbol = SymbolInfo::default();

        let id = SymbolId::default();

        symbol.set::<SymbolId>(id);
        symbol.set::<References>(vec![span]);
        symbol.set::<Label>(Some(label.clone()));

        self.inner.insert(label.clone(), symbol);
        self.id_table.insert(id, label);

        id
    }

    pub fn get_symbol(&self, id: SymbolId) -> &SymbolInfo {
        let label = self.id_table.get(&id).unwrap();
        self.inner.get(label).unwrap()
    }

    pub(crate) fn get_symbol_mut(&mut self, id: SymbolId) -> &mut SymbolInfo {
        let label = self.id_table.get(&id).unwrap();
        self.inner.get_mut(label).unwrap()
    }

    pub fn get_symbol_by_label<S: AsRef<str>>(&self, label: S) -> Option<&SymbolInfo> {
        self.inner.get(label.as_ref())
    }

    pub(crate) fn get_symbol_by_label_mut<S: AsRef<str>>(&mut self, label: S) -> Option<&mut SymbolInfo> {
        self.inner.get_mut(label.as_ref())
    }
}
