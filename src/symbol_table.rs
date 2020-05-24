//! Data structure for information associated with symbols.
//!
//! # What is a symbol?
//!
//! A symbol in this context refers to an unique identifier in an program.
//! These identifiers can denote numeric constants or labels, locations in the program code.
//! Aside from these primary values of the symbols, symbols also have other associated metadata,
//! that is generated and used in various stages of the compilation process.
//!
//! # What is a symbol table?
//!
//! The [SymbolTable] is a data structure for storing information related to symbols and the
//! mechanism for ensuring the symbols' uniqueness.  Essentially, the [SymbolTable] is a [HashMap]
//! that maps [SymbolId]s and [String] labels into collections of metadata entries.
//!
//! All metadata associated with a single symbol is stored in [SymbolInfo] instance, which is
//! essentially a typed [HashMap] with types implementing [Property] as the keys. The types
//! of the values in the map is determined by the key's [Property::Value] associated type.
//!
//! The values stored in [SymbolInfo] are required to implement [Default] because the default value
//! is returned whenever a property's value is queried, but it is not defined. The [Default] trait
//! is implemented for [Option] and so if a property has a value of `Option<V>`, it has
//! automatically an implementation for [Default]. Most of the properties use this pattern.
//!
//! # What proerties can a symbol have?
//!
//! All the possible properties symbols can have are listed in the `Implementors` section of
//! the [Property] documentation page. The type system quarantees that no other properties
//! can be defined for any symbol.
//!
//!  - [SymbolId] ([SymbolId]): The unique [SymbolId] of the symbol.
//!  - [Value] ([i32]): The value of the symbol. A numeric constant or an memory address.
//!  - [Location] (Generic): Location of the symbol in the binary. Used by the compiler before the
//!    final memory addresses are known.
//!  - [Defined] ([Span]): Location in the input stream at which the symbol was defined.
//!  - [References] ([Vec]<[Span]>): List of locations in the input stream at which the symbol was
//!    referenced.
//!  - [Label] ([String]): The human readable label used for the symbol in the source code.

use logos::Span;

use std::any::{Any, TypeId};
use std::collections::HashMap;
use std::fmt::Debug;
use std::marker::PhantomData;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;

use crate::compiler::CompileTarget;

/// A collection of information associated with symbols.
///
/// Every symbol has a [SymbolId] which is quaranteed to be an unique identifier for the symbol.
/// This struct provides methods for accessing the symbols' information by their [SymbolId] or
/// [Label]. While all symbols have [SymbolId]s, a symbol does not neccessarily have a [Label].
#[derive(Default, Debug, Clone)]
pub struct SymbolTable {
    /// A map that contains the symbols' information. The symbol's [Label] acts as the key.
    inner: HashMap<String, SymbolInfo>,

    /// A mapping from [SymbolId]s to the respective symbols' [Label]s.
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

/// An unique identifier for a symbol.
#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq)]
pub struct SymbolId(usize);

static SYMBOL_ID_COUNTER: AtomicUsize = AtomicUsize::new(0);

impl Default for SymbolId {
    fn default() -> Self {
        SymbolId(SYMBOL_ID_COUNTER.fetch_add(1, Ordering::SeqCst))
    }
}

macro_rules! impl_field_type {
    ($(#[$attrs:meta])* $name:ident, $value:ty ) => {
        $(#[$attrs])*
        pub struct $name;

        impl $crate::symbol_table::Property for $name {
            const NAME: &'static str = stringify!($name);
            type Value = $value;
        }
    };
}

impl_field_type!(
    /// Location at which the symbol is defined.
    Defined, Option<Span>
);

impl_field_type!(
    /// Value of the symbol. Most of the time this is a memory address, but ocassionally a
    /// constant.
    Value, Option<i32>
);


impl_field_type!(
    /// List of locations at which the symbol is referenced. This list includes the location of the
    /// definition.
    References, Vec<Span>
);

impl_field_type!(
    /// Label of the symbol. Every symbol generally has a label, but this invariant is not (yet)
    /// built into the types.
    Label, Option<String>
);

impl Property for SymbolId {
    const NAME: &'static str = "SymbolId";
    type Value = SymbolId;
}

/// Location to which the symbol points to in the binary.
/// Used at the compilation stage, when the final memory addresses are not known.
#[derive(Clone, Copy)]
pub struct Location<T> {
    loc: PhantomData<T>,
}

impl<T> Property for Location<T>
where
    T: CompileTarget,
{
    const NAME: &'static str = "Location";
    type Value = Option<T::Location>;
}

/// A type that represents a property in a symbol's entry in the [SymbolTable].
pub trait Property {
    /// Human readable name of the property that is used only for debugging purposes.
    const NAME: &'static str;

    /// Type of the value that is stored in this property. The [Default] of the type is used if the
    /// property is not defined for a symbol.
    type Value: Default + Clone + Debug;
}

/// An property entry in a symbol's [SymbolTable] entry.
///
/// This type is a wrapper around [SymbolTableField] and exists so that we can create a trait
/// object from it using the trait [SymbolTableEntryTrait].
struct SymbolTableEntry<F: Property> {
    value: F::Value,
}

impl<F> std::fmt::Debug for SymbolTableEntry<F>
where
    F: Property,
{
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{:?}", self.value)
    }
}

/// Trait for creating a trait object from [SymbolTableEntry]. Essentially a type-erased interface
/// to [SymbolTableField] and the traits it requires ([Debug] and [Clone]).
trait SymbolTableEntryTrait {
    /// Clones the internal [SymbolTableEntry] and returns it as a type-erased trait object.
    fn clone(&self) -> Box<dyn SymbolTableEntryTrait>;

    /// Returns the name of the property. Directly from [SymbolTableField::NAME].
    fn name(&self) -> &str;

    /// Formats the property as a key-value pair.
    fn debug_fmt(&self, f: &mut std::fmt::DebugMap);

    /// Gets the value of the property as an [Any] trait object.
    fn get_value(&self) -> &dyn Any;

    /// Gets the value of the property as a mutable [Any] trait object.
    fn get_value_mut(&mut self) -> &mut dyn Any;

    /// Consumes the trait object and returns the proprty's value as a boxed [Any] trait object.
    fn into_value(self: Box<Self>) -> Box<dyn Any>;
}

impl<T> SymbolTableEntryTrait for SymbolTableEntry<T>
where
    T: Property + 'static,
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

/// The entry in [SymbolTable] which contains the information relating to a single symbol.
///
/// Provides a typed map API that uses types implementing [Property] as the keys.
/// Each of these key types has an associated [Value](Property::Value) type, an so the keys
/// can have values of differing types.
#[derive(Default)]
pub struct SymbolInfo {
    map: HashMap<TypeId, Box<dyn SymbolTableEntryTrait>>,
}

impl Clone for SymbolInfo {
    fn clone(&self) -> SymbolInfo {
        let map = self
            .map
            .iter()
            .map(|(type_id, boxed)| (*type_id, SymbolTableEntryTrait::clone(&**boxed)))
            .collect();

        SymbolInfo { map }
    }
}

use std::borrow::Cow;

impl SymbolInfo {
    /// Sets the value of the field specified by the type `F`. If the field is already specified,
    /// replaces the value and returns the original.
    pub fn set<F: Property + 'static>(&mut self, value: F::Value) -> Option<F::Value> {
        let id = TypeId::of::<F>();
        // println!("Set ({}) {:?} = {:?}", F::NAME, id, value);

        self.map
            .insert(id, Box::new(SymbolTableEntry::<F> { value }))
            .and_then(|entry| entry.into_value().downcast().ok().map(|b| *b))
    }

    /// Gets the value of the field specified by the type `F`. If the field has an value, returns
    /// an reference to it. Otherwise returns the [Default] of that value.
    pub fn get<F: Property + 'static>(&self) -> Cow<F::Value> {
        if let Some(s) = self.map.get(&TypeId::of::<F>()) {
            let r = s.get_value().downcast_ref().unwrap();
            // println!("Get ({}) {:?} = {:?}", F::NAME, id, r);
            Cow::Borrowed(r)
        } else {
            let v = Default::default();
            // println!("Get ({}) {:?} = {:?} (default)", F::NAME, id, v);
            Cow::Owned(v)
        }
    }

    /// Gets a mutable reference to the field specified by the type `F`. If the field is not
    /// present for this symbol, inserts the [Default] value of the field into the [SymbolTable].
    pub fn get_mut<F>(&mut self) -> &mut F::Value
    where
        F: Property + 'static,
    {
        self.map
            .entry(TypeId::of::<F>())
            .or_insert_with(|| {
                Box::new(SymbolTableEntry::<F> {
                    value: Default::default(),
                })
            })
            .get_value_mut()
            .downcast_mut()
            .unwrap()
    }
}

impl SymbolTable {
    /// Creates a new symbol table with no symbol information.
    pub fn new() -> Self {
        SymbolTable {
            inner: HashMap::new(),
            id_table: HashMap::new(),
        }
    }

    /// Returns an iterator over the symbols contained in the [SymbolTable].
    pub fn iter(&self) -> impl Iterator<Item = &SymbolInfo> {
        self.inner.values()
    }

    /// Returns an iterator of mutable references to the symbols contained in the [SymbolTable].
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut SymbolInfo> {
        self.inner.values_mut()
    }

    pub(crate) fn define_symbol(
        &mut self,
        span: Span,
        label: String,
        value: i32,
    ) -> Result<SymbolId, SymbolId> {
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

    /// Returns the [SymbolId] of a symbol with the specified label.
    /// If no such symbol exists, inserts a new symbol into the [SymbolTable] and returns it's
    /// [SymbolId].
    pub fn get_or_create(&mut self, label: String) -> SymbolId {
        if let Some(symbol) = self.inner.get(&label) {
            return symbol.get::<SymbolId>().into_owned();
        }

        let mut symbol = SymbolInfo::default();
        let id = SymbolId::default();
        symbol.set::<SymbolId>(id);

        self.id_table.insert(id, label.clone());
        self.inner.insert(label.clone(), symbol);

        id
    }

    /// Returns an immutable reference to the symbol denothet by the provided [SymbolId].
    pub fn symbol(&self, id: SymbolId) -> &SymbolInfo {
        let label = self.id_table.get(&id).unwrap();
        self.inner.get(label).unwrap()
    }

    /// Returns a mutable reference to the symbol denothet by the provided [SymbolId].
    pub fn symbol_mut(&mut self, id: SymbolId) -> &mut SymbolInfo {
        let label = self.id_table.get(&id).unwrap();
        self.inner.get_mut(label).unwrap()
    }

    /// Returns an immutable reference to a symbol with the specified label, if such symbol exists.
    pub fn symbol_by_label<S: AsRef<str>>(&self, label: S) -> Option<&SymbolInfo> {
        self.inner.get(label.as_ref())
    }

    /// Returns a mutable reference to a symbol with the specified label, if such symbol exists.
    pub fn symbol_by_label_mut<S: AsRef<str>>(&mut self, label: S) -> Option<&mut SymbolInfo> {
        self.inner.get_mut(label.as_ref())
    }
}
