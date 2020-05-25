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
//! Queries of properties never fail and if the property has not been defined for the symbol in
//! question, the query operations return a default value. This default value is determined by the
//! [Property::default_value] method.
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
    /// A map that contains the symbols' information. The symbol's [SymbolId] acts as the key.
    inner: HashMap<SymbolId, SymbolInfo>,

    /// A mapping from labels to the respective symbols' [SymbolId]s.
    label_table: HashMap<String, SymbolId>,
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

impl SymbolId {
    fn unique() -> Self {
        SymbolId(SYMBOL_ID_COUNTER.fetch_add(1, Ordering::SeqCst))
    }
}

/// Macro for creating an unit struct and implementing [Property] for it.
///
/// # Example
/// ```
/// # struct TypeOfValue;
///
/// impl_field_type! {
///     /// A documentation for the property.
///     #[derive(Debug, Clone)]
///     PropertyName, TypeOfValue
/// }
/// ```
macro_rules! impl_field_type {
    ($(#[$attrs:meta])* $name:ident, $value:ty ) => {
        $(#[$attrs])*
        pub struct $name;

        impl $crate::symbol_table::Property for $name {
            const NAME: &'static str = stringify!($name);
            type Value = $value;

            fn default_value() -> Self::Value {
                Default::default()
            }
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
    /// A human readable label of the symbol as defined in the source code.
    Label, String
);

impl Property for SymbolId {
    const NAME: &'static str = "SymbolId";
    type Value = SymbolId;

    fn default_value() -> Self::Value {
        panic!("symbol without SymbolId should not exist")
    }
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

    fn default_value() -> Self::Value {
        None
    }
}

/// A type that represents a property in a symbol's entry in the [SymbolTable].
pub trait Property {
    /// Human readable name of the property that is used only for debugging purposes.
    const NAME: &'static str;

    /// Type of the value that is stored in this property.
    type Value: Clone + Debug;

    /// If the value of this property is queried on an symbol for which it is not specidied,
    /// this method is called to determine the default value for this property.
    fn default_value() -> Self::Value;
}

/// An property entry in a symbol's [SymbolTable] entry.
///
/// This type is a wrapper around [Property] and exists so that we can create a trait
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

/// Trait for creating a trait object from [Property]. Essentially a type-erased interface
/// to [Property] and the traits it requires ([Debug] and [Clone]).
trait SymbolTableEntryTrait {
    /// Clones the internal [SymbolTableEntry] and returns it as a type-erased trait object.
    fn clone(&self) -> Box<dyn SymbolTableEntryTrait>;

    /// Returns the name of the property. Directly from [Property::NAME].
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
pub struct SymbolInfo {
    map: HashMap<TypeId, Box<dyn SymbolTableEntryTrait>>,
}

impl SymbolInfo {
    fn new() -> SymbolInfo {
        let mut info = SymbolInfo {
            map: HashMap::new(),
        };

        info.set::<SymbolId>(SymbolId::unique());

        info
    }
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
            let v = F::default_value();
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
                    value: F::default_value(),
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
            label_table: HashMap::new(),
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

    /// Returns the [SymbolId] of a symbol with the specified label.
    /// If no such symbol exists, inserts a new symbol into the [SymbolTable] and returns it's
    /// [SymbolId].
    pub fn get_or_create(&mut self, label: String) -> &mut SymbolInfo {
        let id = match self.label_table.get(&label) {
            Some(id) => *id,
            None => {
                let mut entry = SymbolInfo::new();
                entry.set::<Label>(label.clone());

                let id = entry.get::<SymbolId>().into_owned();

                self.inner.insert(id, entry);
                self.label_table.insert(label.clone(), id);

                id
            },
        };

        self.inner.get_mut(&id).unwrap()
    }

    /// Returns an immutable reference to the symbol denothet by the provided [SymbolId].
    pub fn symbol(&self, id: SymbolId) -> &SymbolInfo {
        self.inner.get(&id).unwrap()
    }

    /// Returns a mutable reference to the symbol denothet by the provided [SymbolId].
    pub fn symbol_mut(&mut self, id: SymbolId) -> &mut SymbolInfo {
        self.inner.get_mut(&id).unwrap()
    }

    /// Returns an immutable reference to a symbol with the specified label, if such symbol exists.
    pub fn symbol_by_label<S: AsRef<str>>(&self, label: S) -> Option<&SymbolInfo> {
        match self.label_table.get(label.as_ref()).cloned() {
            None => None,
            Some(label) => Some(self.symbol(label)),
        }
    }

    /// Returns a mutable reference to a symbol with the specified label, if such symbol exists.
    pub fn symbol_by_label_mut<S: AsRef<str>>(&mut self, label: S) -> Option<&mut SymbolInfo> {
        match self.label_table.get(label.as_ref()).cloned() {
            None => None,
            Some(label) => Some(self.symbol_mut(label)),
        }
    }
}
