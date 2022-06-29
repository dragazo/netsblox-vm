use std::prelude::v1::*;
use std::collections::BTreeMap;
use std::marker::PhantomData;
use std::fmt;

use netsblox_ast as ast;

use crate::gc::*;
use crate::json::*;

#[derive(Debug, PartialEq)]
pub enum SimpleValue {
    Bool(bool),
    Number(f64),
    String(String),
    List(Vec<SimpleValue>),
}
impl From<bool> for SimpleValue { fn from(v: bool) -> Self { Self::Bool(v) } }
impl From<f64> for SimpleValue { fn from(v: f64) -> Self { Self::Number(v) } }
impl From<i64> for SimpleValue { fn from(v: i64) -> Self { Self::Number(v as f64) } }
impl From<String> for SimpleValue { fn from(v: String) -> Self { Self::String(v) } }
impl From<Vec<SimpleValue>> for SimpleValue { fn from(v: Vec<SimpleValue>) -> Self { Self::List(v) } }
impl TryFrom<Json> for SimpleValue {
    type Error = JsonError;
    /// Create a new [`SimpleValue`] from a [`Json`] value.
    /// 
    /// NetsBlox does not allow a concept of null, so [`Json`] values containing [`Json::Null`] will result in [`JsonError::HadNull`].
    /// Additionally, `serde_json`'s interface states that [`Json::Number`] values might not be able to be encoded as [`f64`], in which case [`JsonError::HadBadNumber`] is returned;
    /// however, based on their source code, this should only be possible with special feature flags passed in to allow arbitrary precision floating point.
    fn try_from(value: Json) -> Result<Self, JsonError> {
        Ok(match value {
            Json::Null => return Err(JsonError::HadNull),
            Json::Bool(x) => x.into(),
            Json::Number(x) => x.as_f64().ok_or(JsonError::HadBadNumber)?.into(),
            Json::String(x) => x.into(),
            Json::Array(x) => x.into_iter().map(|x| SimpleValue::try_from(x)).collect::<Result<Vec<_>,_>>()?.into(),
            Json::Object(x) => x.into_iter().map(|(k, v)| Ok(vec![ k.into(), SimpleValue::try_from(v)? ].into())).collect::<Result<Vec<_>,_>>()?.into(),
        })
    }
}

/// Creates a new [`SimpleValue`] using Python-like syntax.
/// 
/// Python-style dictionary notation creates NetsBlox structured data, which is simply a list of key/value pairs.
/// Compound expressions in the extended syntax must be wrapped in parenthesis to match with a `tt` token.
/// 
/// ```
/// # use netsblox_vm::simple_value;
/// let friends = simple_value!([
///     { "name" => "Sarah", "age" => 22, "isMale" => false, "pets" => [] },
///     { "name" => "John", "age" => 31.5 + 2.25, "isMale" => true, "pets" => ["Mr. Fluffy"] },
/// ]);
/// ```
#[macro_export]
macro_rules! simple_value {
    (@list [$($elems:expr),*$(,)?]) => { $crate::runtime::SimpleValue::List(vec![$($elems),*]) };

    (@list [$($elems:expr,)*] [$($lst:tt)*] $($rest:tt)*) => { simple_value!(@list [$($elems,)* simple_value!([$($lst)*])] $($rest)*) };
    (@list [$($elems:expr,)*] {$($map:tt)*} $($rest:tt)*) => { simple_value!(@list [$($elems,)* simple_value!({$($map)*})] $($rest)*) };
    (@list [$($elems:expr,)*]    $val:expr, $($rest:tt)*) => { simple_value!(@list [$($elems,)* simple_value!(   $val  ),] $($rest)*) };
    (@list [$($elems:expr,)*]    $val:expr              ) => { simple_value!(@list [$($elems,)* simple_value!(   $val   )]          ) };
    (@list [$($elems:expr),*]        ,      $($rest:tt)*) => { simple_value!(@list [$($elems,)*]                           $($rest)*) };

    (@object [$($fields:expr),*$(,)?] () ()) => { $crate::runtime::SimpleValue::List(vec![$($fields),*]) };

    (@object [$($fields:expr,)*] ($key:expr) ([$($lst:tt)*]    $($rest:tt)*  )) => { simple_value!(@object [$($fields,)* $crate::runtime::SimpleValue::List(vec![ $key, simple_value!([$($lst)*]) ])] () (   $($rest)*)  ) };
    (@object [$($fields:expr,)*] ($key:expr) ({$($map:tt)*}    $($rest:tt)*  )) => { simple_value!(@object [$($fields,)* $crate::runtime::SimpleValue::List(vec![ $key, simple_value!({$($map)*}) ])] () (   $($rest)*)  ) };
    (@object [$($fields:expr,)*] ($key:expr) (   $val:expr  $(,$($rest:tt)*)?)) => { simple_value!(@object [$($fields,)* $crate::runtime::SimpleValue::List(vec![ $key, simple_value!(   $val)    ])] () ($(,$($rest)*)?)) };

    (@object [$($fields:expr,)*] () ([$($lst:tt)*] => $($rest:tt)*)) => { simple_value!(@object [$($fields,)*] (simple_value!([$($lst)*])) ($($rest)*)) };
    (@object [$($fields:expr,)*] () ({$($map:tt)*} => $($rest:tt)*)) => { simple_value!(@object [$($fields,)*] (simple_value!({$($map)*})) ($($rest)*)) };
    (@object [$($fields:expr,)*] () (   $key:expr  => $($rest:tt)*)) => { simple_value!(@object [$($fields,)*] (simple_value!($key))       ($($rest)*)) };
    (@object [$($fields:expr),*] () (       ,         $($rest:tt)*)) => { simple_value!(@object [$($fields,)*] ()                          ($($rest)*)) };

    ([ $($tt:tt)* ]) => { simple_value!(@list   []     $($tt)*)  };
    ({ $($tt:tt)* }) => { simple_value!(@object [] () ($($tt)*)) };
    ($val:expr) => { $crate::runtime::SimpleValue::from($val.to_owned()) };
}

#[test]
fn test_simple_value_macro() {
    let hello = String::from("hello world");
    match simple_value!(true) { SimpleValue::Bool(x) => assert!(x), _ => panic!() }
    match simple_value!(false) { SimpleValue::Bool(x) => assert!(!x), _ => panic!() }
    match simple_value!(-12.5) { SimpleValue::Number(x) => assert_eq!(x, -12.5), _ => panic!() }
    match simple_value!(-12.5 + 1.0) { SimpleValue::Number(x) => assert_eq!(x, -11.5), _ => panic!() }
    match simple_value!(String::from("hello world")) { SimpleValue::String(x) => assert_eq!(x, "hello world"), _ => panic!() }
    match simple_value!(hello.clone()) { SimpleValue::String(x) => assert_eq!(x, "hello world"), _ => panic!() }
    match simple_value!("hello world") { SimpleValue::String(x) => assert_eq!(x, "hello world"), _ => panic!() }
    match simple_value!([true, -6 + 2, "test", hello.clone()]) {
        SimpleValue::List(x) => {
            assert_eq!(x.len(), 4);
            match &x[0] { SimpleValue::Bool(x) => assert!(x), _ => panic!() }
            match &x[1] { SimpleValue::Number(x) => assert_eq!(*x, -4.0), _ => panic!() }
            match &x[2] { SimpleValue::String(x) => assert_eq!(x, "test"), _ => panic!() }
            match &x[3] { SimpleValue::String(x) => assert_eq!(x, "hello world"), _ => panic!() }
        }
        _ => panic!()
    }
    match simple_value!([4.5, 3.25, 1.125, -6.75]) {
        SimpleValue::List(x) => {
            assert_eq!(x.len(), 4);
            match &x[0] { SimpleValue::Number(x) => assert_eq!(*x, 4.5), _ => panic!() }
            match &x[1] { SimpleValue::Number(x) => assert_eq!(*x, 3.25), _ => panic!() }
            match &x[2] { SimpleValue::Number(x) => assert_eq!(*x, 1.125), _ => panic!() }
            match &x[3] { SimpleValue::Number(x) => assert_eq!(*x, -6.75), _ => panic!() }
        }
        _ => panic!()
    }
    match simple_value!({ "name" => "john", "age" => 8.0, String::from("isMale") => true, ["friends"] => [{ "name" => "sarah", "id" => 43783745.0, "test" => {} }] }) {
        SimpleValue::List(x) => {
            assert_eq!(x.len(), 4);
            assert_eq!(x[0], simple_value!(["name", "john"]));
            assert_eq!(x[1], simple_value!(["age", 8.0]));
            assert_eq!(x[2], simple_value!(["isMale", true]));
            match &x[3] {
                SimpleValue::List(x) => {
                    assert_eq!(x.len(), 2);
                    assert_eq!(x[0], simple_value!(["friends"]));
                    match &x[1] {
                        SimpleValue::List(x) => {
                            assert_eq!(x.len(), 1);
                            match &x[0] {
                                SimpleValue::List(x) => {
                                    assert_eq!(x.len(), 3);
                                    assert_eq!(x[0], simple_value!(["name", "sarah"]));
                                    assert_eq!(x[1], simple_value!(["id", 43783745.0]));
                                    assert_eq!(x[2], simple_value!(["test", []]));
                                }
                                _ => panic!(),
                            }
                            assert_eq!(x[0], simple_value!({ "name" => "sarah", "id" => 43783745.0, "test" => {} }));
                            assert_eq!(x[0], simple_value!([ ["name", "sarah"], ["id", 43783745.0], ["test", []] ]));
                        }
                        _ => panic!(),
                    }
                    assert_eq!(x[1], simple_value!([{ "name" => "sarah", "id" => 43783745.0, "test" => [] }]));
                }
                _ => panic!(),
            }
        }
        _ => panic!()
    }
}

/// The type of a [`Value`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Type {
    Bool, Number, String, List, Closure, Entity,
}

/// A type conversion error on a [`Value`].
#[derive(Debug)]
pub struct ConversionError {
    pub got: Type,
    pub expected: Type,
}

#[derive(Debug)]
pub enum JsonError {
    HadNull, HadBadNumber,
}

/// A value representing the identity of a [`Value`].
#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq,)]
pub struct Identity<'gc>(*const (), PhantomData<&'gc Value<'gc>>);

/// Any primitive value.
#[derive(Debug, Clone, Copy, Collect)]
#[collect(no_drop)]
pub enum Value<'gc> {
    /// A primitive boolean value.
    Bool(bool),
    /// A primitive numeric value. Snap! and NetsBlox use 64-bit floating point values for all numbers.
    Number(f64),
    /// A primitive string value, which is an immutable reference type.
    /// Although [`Rc`] would be sufficient for this purpose, using [`Gc`] instead makes the arena automatically
    /// include strings in its calculation of the total memory footprint (and allows [`Value`] to be [`Copy`]).
    String(Gc<'gc, String>),
    /// A primitive list type, which is a mutable reference type.
    List(GcCell<'gc, Vec<Value<'gc>>>),
    /// A closure/lambda function. This contains information about the closure's bytecode location, parameters, and captures from the parent scope.
    Closure(GcCell<'gc, Closure<'gc>>),
    /// A reference to an [`Entity`] in the environment.
    Entity(GcCell<'gc, Entity<'gc>>),
}
impl<'gc> From<bool> for Value<'gc> { fn from(v: bool) -> Self { Value::Bool(v) } }
impl<'gc> From<f64> for Value<'gc> { fn from(v: f64) -> Self { Value::Number(v) } }
impl<'gc> From<Gc<'gc, String>> for Value<'gc> { fn from(v: Gc<'gc, String>) -> Self { Value::String(v) } }
impl<'gc> From<GcCell<'gc, Vec<Value<'gc>>>> for Value<'gc> { fn from(v: GcCell<'gc, Vec<Value<'gc>>>) -> Self { Value::List(v) } }
impl<'gc> From<GcCell<'gc, Closure<'gc>>> for Value<'gc> { fn from(v: GcCell<'gc, Closure<'gc>>) -> Self { Value::Closure(v) } }
impl<'gc> From<GcCell<'gc, Entity<'gc>>> for Value<'gc> { fn from(v: GcCell<'gc, Entity<'gc>>) -> Self { Value::Entity(v) } }
impl<'gc> Value<'gc> {
    /// Creates a new value from an abstract syntax tree.
    pub fn from_ast(mc: MutationContext<'gc, '_>, value: &ast::Value) -> Self {
        match value {
            ast::Value::Bool(x) => (*x).into(),
            ast::Value::Number(x) => (*x).into(),
            ast::Value::Constant(ast::Constant::E) => std::f64::consts::E.into(),
            ast::Value::Constant(ast::Constant::Pi) => std::f64::consts::PI.into(),
            ast::Value::String(x) => Gc::allocate(mc, x.clone()).into(),
            ast::Value::List(x) => GcCell::allocate(mc, x.iter().map(|x| Value::from_ast(mc, x)).collect::<Vec<_>>()).into(),
        }
    }
    /// Create a new [`Value`] from a [`SimpleValue`].
    pub fn from_simple(mc: MutationContext<'gc, '_>, value: SimpleValue) -> Self {
        match value {
            SimpleValue::Bool(x) => Value::Bool(x),
            SimpleValue::Number(x) => Value::Number(x),
            SimpleValue::String(x) => Value::String(Gc::allocate(mc, x)),
            SimpleValue::List(x) => Value::List(GcCell::allocate(mc, x.into_iter().map(|x| Value::from_simple(mc, x)).collect())),
        }
    }
    /// Creates a shallow copy of this value.
    pub fn shallow_copy(&self, mc: MutationContext<'gc, '_>) -> Value<'gc> {
        match *self {
            Value::Bool(x) => x.into(),
            Value::Number(x) => x.into(),
            Value::String(x) => x.into(),
            Value::Entity(x) => x.into(),
            Value::Closure(x) => x.into(),
            Value::List(x) => GcCell::allocate(mc, x.read().to_owned()).into(),
        }
    }
    /// Returns a value representing this object that implements [`Eq`] such that
    /// two values are equal if and only if they are references to the same object.
    /// This is primarily useful for testing for reference equality of lists.
    pub fn identity(&self) -> Identity<'gc> {
        match self {
            Value::Bool(x) => Identity(&*x as *const bool as *const (), PhantomData),
            Value::Number(x) => Identity(&*x as *const f64 as *const (), PhantomData),
            Value::String(x) => Identity(x.as_ptr() as *const String as *const (), PhantomData),
            Value::List(x) => Identity(x.as_ptr() as *const Vec<Value> as *const (), PhantomData),
            Value::Closure(x) => Identity(x.as_ptr() as *const Closure as *const (), PhantomData),
            Value::Entity(x) => Identity(x.as_ptr() as *const Entity as *const (), PhantomData),
        }
    }
    /// Gets the type of value that is stored.
    pub fn get_type(&self) -> Type {
        match self {
            Value::Bool(_) => Type::Bool,
            Value::Number(_) => Type::Number,
            Value::String(_) => Type::String,
            Value::List(_) => Type::List,
            Value::Closure(_) => Type::Closure,
            Value::Entity(_) => Type::Entity,
        }
    }
    /// Attempts to interpret this value as a bool.
    pub fn to_bool(&self) -> Result<bool, ConversionError> {
        Ok(match self {
            Value::Bool(x) => *x,
            Value::Number(x) => *x != 0.0 && !x.is_nan(),
            Value::String(x) => !x.is_empty(),
            x => return Err(ConversionError { got: x.get_type(), expected: Type::Bool }),
        })
    }
    /// Attempts to interpret this value as a number.
    pub fn to_number(&self) -> Result<f64, ConversionError> {
        Ok(match self {
            Value::Number(x) => *x,
            Value::String(x) => x.parse().map_err(|_| ConversionError { got: Type::String, expected: Type::Number })?,
            x => return Err(ConversionError { got: x.get_type(), expected: Type::Number }),
        })
    }
    /// Attempts to interpret this value as a string.
    pub fn to_string(&self, mc: MutationContext<'gc, '_>) -> Result<Gc<'gc, String>, ConversionError> {
        Ok(match self {
            Value::String(x) => *x,
            Value::Number(x) => Gc::allocate(mc, x.to_string()),
            x => return Err(ConversionError { got: x.get_type(), expected: Type::String }),
        })
    }
    /// Attempts to interpret this value as a list.
    pub fn to_list(&self, _mc: MutationContext<'gc, '_>) -> Result<GcCell<'gc, Vec<Value<'gc>>>, ConversionError> {
        match self {
            Value::List(x) => Ok(*x),
            x => Err(ConversionError { got: x.get_type(), expected: Type::List }.into()),
        }
    }
    /// Attempts to interpret this value as a closure.
    pub fn to_closure(&self, _mc: MutationContext<'gc, '_>) -> Result<GcCell<'gc, Closure<'gc>>, ConversionError> {
        match self {
            Value::Closure(x) => Ok(*x),
            x => Err(ConversionError { got: x.get_type(), expected: Type::Closure }.into()),
        }
    }
    /// Attempts to interpret this value as an entity.
    pub fn to_entity(&self, _mc: MutationContext<'gc, '_>) -> Result<GcCell<'gc, Entity<'gc>>, ConversionError> {
        match self {
            Value::Entity(x) => Ok(*x),
            x => Err(ConversionError { got: x.get_type(), expected: Type::Entity }.into()),
        }
    }
}

/// Information about a closure/lambda function.
#[derive(Collect)]
#[collect(no_drop)]
pub struct Closure<'gc> {
    pub pos: usize,
    pub params: Vec<String>,
    pub captures: SymbolTable<'gc>,
}
impl fmt::Debug for Closure<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[Closure({})]", self.pos)
    }
}

/// Information about an entity (sprite or stage).
#[derive(Collect)]
#[collect(no_drop)]
pub struct Entity<'gc> {
    pub name: String,
    pub fields: SymbolTable<'gc>,
    pub alive: bool,
}
impl fmt::Debug for Entity<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[Entity({}, {})]", self.name, if self.alive { "alive" } else { "dead" })
    }
}

/// Represents a shared mutable resource.
/// 
/// This is effectively equivalent to [`GcCell<T>`] except that it performs no dynamic allocation
/// for the [`Shared::Unique`] case, which is assumed to be significantly more likely than [`Shared::Aliased`].
#[derive(Collect)]
#[collect(no_drop)]
pub enum Shared<'gc, T: 'gc + Collect + Copy> {
    /// A shared resource which has only (this) single unique handle.
    Unique(T),
    /// One of several handles to a single shared resource.
    Aliased(GcCell<'gc, T>),
}
impl<'gc, T: 'gc + Collect + Copy> Shared<'gc, T> {
    /// Sets the value of the shared resource.
    pub fn set(&mut self, mc: MutationContext<'gc, '_>, value: T) {
        match self {
            Shared::Unique(x) => *x = value,
            Shared::Aliased(x) => *x.write(mc) = value,
        }
    }
    /// Gets a copy of the shared resource's currently stored value.
    pub fn get(&self) -> T {
        match self {
            Shared::Unique(x) => *x,
            Shared::Aliased(x) => *x.read(),
        }
    }
    /// Creates an aliasing instance of [`Shared`] to the same resource as this one.
    /// If this instance is the [`Shared::Unique`] variant, transitions to [`Shared::Aliased`] and returns a second handle.
    /// Otherwise, this simple returns an additional handle to the aliased shared resource.
    pub fn alias(&mut self, mc: MutationContext<'gc, '_>) -> Self {
        match self {
            Shared::Unique(x) => {
                let res = GcCell::allocate(mc, *x);
                *self = Shared::Aliased(res);
                Shared::Aliased(res)
            }
            Shared::Aliased(x) => Shared::Aliased(*x),
        }
    }
}
impl<'gc, T: Collect + Copy> From<T> for Shared<'gc, T> { fn from(value: T) -> Self { Shared::Unique(value) } }

/// Holds a collection of variables in an execution context.
/// 
/// [`SymbolTable`] has utilities to extract variables from an abstract syntax tree, or to explicitly define variables.
/// Simple methods are provided to perform value lookups in the table.
/// To perform hierarchical value lookups, use the higher-level utility [`LookupGroup`].
#[derive(Default, Collect)]
#[collect(no_drop)]
pub struct SymbolTable<'gc>(BTreeMap<String, Shared<'gc, Value<'gc>>>);
impl<'gc> SymbolTable<'gc> {
    /// Creates a symbol table containing all the provided variable definitions.
    pub fn from_ast(mc: MutationContext<'gc, '_>, vars: &[ast::VariableDef]) -> Self {
        Self(vars.iter().map(|x| (x.trans_name.clone(), Value::from_ast(mc, &x.value).into())).collect())
    }
    /// Sets the value of an existing variable (as if by [`Shared::set`]) or defines it if it does not exist.
    /// If the variable does not exist, creates a [`Shared::Unique`] instance for the new `value`.
    /// If you would prefer to always create a new, non-aliased value, consider using [`SymbolTable::redefine_or_define`] instead.
    pub fn set_or_define(&mut self, mc: MutationContext<'gc, '_>, var: &str, value: Value<'gc>) {
        match self.0.get_mut(var) {
            Some(x) => x.set(mc, value),
            None => { self.0.insert(var.to_owned(), value.into()); }
        }
    }
    /// Defines or redefines a value in the symbol table to a new instance of [`Shared<Value>`].
    /// Note that this is not the same as [`SymbolTable::set_or_define`], which sets a value on a potentially aliased variable.
    /// If a variable named `var` already existed and was [`Shared::Aliased`], its value is not modified.
    pub fn redefine_or_define(&mut self, var: &str, value: Shared<'gc, Value<'gc>>) {
        self.0.insert(var.to_owned(), value);
    }
    /// Looks up the given variable in the symbol table.
    /// If a variable with the given name does not exist, returns [`None`].
    pub fn lookup(&self, var: &str) -> Option<&Shared<'gc, Value<'gc>>> {
        self.0.get(var)
    }
    /// Equivalent to [`SymbolTable::lookup`] except that it returns a mutable reference.
    pub fn lookup_mut(&mut self, var: &str) -> Option<&mut Shared<'gc, Value<'gc>>> {
        self.0.get_mut(var)
    }
    /// Iterates over the key value pairs stored in the symbol table.
    pub fn iter(&self) -> symbol_table::Iter<'gc, '_> {
        symbol_table::Iter(self.0.iter())
    }
    /// Iterates over the key value pairs stored in the symbol table.
    pub fn iter_mut(&mut self) -> symbol_table::IterMut<'gc, '_> {
        symbol_table::IterMut(self.0.iter_mut())
    }
}
impl<'gc> IntoIterator for SymbolTable<'gc> {
    type Item = (String, Shared<'gc, Value<'gc>>);
    type IntoIter = symbol_table::IntoIter<'gc>;
    fn into_iter(self) -> Self::IntoIter { symbol_table::IntoIter(self.0.into_iter()) }
}
pub mod symbol_table {
    //! Special types for working with a [`SymbolTable`].
    use super::*;
    pub struct IntoIter<'gc>(pub(crate) std::collections::btree_map::IntoIter<String, Shared<'gc, Value<'gc>>>);
    pub struct Iter<'gc, 'a>(pub(crate) std::collections::btree_map::Iter<'a, String, Shared<'gc, Value<'gc>>>);
    pub struct IterMut<'gc, 'a>(pub(crate) std::collections::btree_map::IterMut<'a, String, Shared<'gc, Value<'gc>>>);
    impl<'gc> Iterator for IntoIter<'gc> { type Item = (String, Shared<'gc, Value<'gc>>); fn next(&mut self) -> Option<Self::Item> { self.0.next() } }
    impl<'gc, 'a> Iterator for Iter<'gc, 'a> { type Item = (&'a String, &'a Shared<'gc, Value<'gc>>); fn next(&mut self) -> Option<Self::Item> { self.0.next() } }
    impl<'gc, 'a> Iterator for IterMut<'gc, 'a> { type Item = (&'a String, &'a mut Shared<'gc, Value<'gc>>); fn next(&mut self) -> Option<Self::Item> { self.0.next() } }
}

/// A collection of symbol tables with hierarchical context searching.
pub struct LookupGroup<'gc, 'a, 'b>(&'a mut [&'b mut SymbolTable<'gc>]);
impl<'gc, 'a, 'b> LookupGroup<'gc, 'a, 'b> {
    /// Creates a new lookup group.
    /// The first symbol table is intended to be the most-global, and subsequent tables are increasingly more-local.
    /// Panics if `tables` is empty.
    pub fn new(tables: &'a mut [&'b mut SymbolTable<'gc>]) -> Self {
        debug_assert!(!tables.is_empty());
        Self(tables)
    }
    /// Searches for the given variable in this group of lookup tables,
    /// starting with the last (most-local) table and working towards the first (most-global) table.
    /// Returns a reference to the value if it is found, otherwise returns [`None`].
    pub fn lookup(&self, var: &str) -> Option<&Shared<'gc, Value<'gc>>> {
        for src in self.0.iter().rev() {
            if let Some(val) = src.lookup(var) {
                return Some(val);
            }
        }
        None
    }
    /// As [`LookupGroup::lookup`], but returns a mutable reference.
    pub fn lookup_mut(&mut self, var: &str) -> Option<&mut Shared<'gc, Value<'gc>>> {
        for src in self.0.iter_mut().rev() {
            if let Some(val) = src.lookup_mut(var) {
                return Some(val);
            }
        }
        None
    }
    /// Performs a lookup for the given variable.
    /// If it already exists, assigns it a new value.
    /// Otherwise, defines it in the last (most-local) context equivalently to [`SymbolTable::set_or_define`].
    pub fn set_or_define(&mut self, mc: MutationContext<'gc, '_>, var: &str, value: Value<'gc>) {
        match self.lookup_mut(var) {
            Some(x) => x.set(mc, value),
            None => self.0.last_mut().unwrap().set_or_define(mc, var, value),
        }
    }
    /// Gets a reference to the last (most-local) context.
    pub fn locals(&mut self) -> &SymbolTable<'gc> {
        self.0.last().unwrap()
    }
    /// Gets a mutable reference to the last (most-local) context.
    pub fn locals_mut(&mut self) -> &mut SymbolTable<'gc> {
        self.0.last_mut().unwrap()
    }
}

/// Global information about the execution state of an entire project.
#[derive(Collect)]
#[collect(no_drop)]
pub struct GlobalContext<'gc> {
    pub proj_name: String,
    pub globals: SymbolTable<'gc>,
    pub entities: Vec<GcCell<'gc, Entity<'gc>>>,
}
impl<'gc> GlobalContext<'gc> {
    pub fn from_ast(mc: MutationContext<'gc, '_>, role: &ast::Role) -> Self {
        Self {
            proj_name: role.name.clone(),
            globals: SymbolTable::from_ast(mc, &role.globals),
            entities: role.entities.iter().map(|entity| GcCell::allocate(mc, Entity {
                name: entity.trans_name.clone(),
                fields: SymbolTable::from_ast(mc, &entity.fields),
                alive: true,
            })).collect(),
        }
    }
}

/// The result of a successful call to [`System::poll_async`].
pub enum AsyncPoll<'gc> {
    /// The async operation completed with the given value.
    Completed(Value<'gc>),
    /// The async operation is still pending and has not completed.
    Pending,
}

/// Types of [`System`] resources, grouped into feature categories.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SystemFeature {
    Time,
}
/// An error resulting from improper use of [`System`] resources.
#[derive(Debug)]
pub enum SystemError {
    /// Attempt to use a feature which is not supported or not implemented.
    NotSupported { feature: SystemFeature },
    /// Unknown system error with a description string.
    Other { description: String },
}

/// Represents all the features of an implementing system.
/// 
/// This type encodes any features that cannot be performed without platform-specific resources.
/// 
/// When implementing [`System`] for some type, you may prefer to not support one or more features.
/// This can be accomplished by returning the [`SystemError::NotSupported`] variant for the relevant [`SystemFeature`].
pub trait System: 'static {
    /// Key type used to refer to the result of an async operation.
    type AsyncKey: Collect + 'static;

    /// Polls for the completion of an async operation.
    /// If [`AsyncPoll::Completed`] is returned, the system is allowed to invalidate the requested `key`, which will not be used again.
    fn poll_async<'gc>(&mut self, mc: MutationContext<'gc, '_>, key: &Self::AsyncKey) -> Result<AsyncPoll<'gc>, SystemError>;

    /// Gets the current time in milliseconds.
    /// This is not required to represent the actual real-world time; e.g., this could simply measure uptime.
    /// Subsequent values are required to be non-decreasing.
    fn time_ms(&self) -> Result<u64, SystemError>;
}

#[cfg(any(test, feature = "std"))]
mod std_system {
    extern crate std as real_std;
    use real_std::time::Instant;
    use super::*;

    /// A type implementing the [`System`] trait which supports all features.
    /// This requires the [`std`](crate) feature flag.
    pub struct StdSystem {
        start_time: Instant,
    }
    impl StdSystem {
        pub fn new() -> Self {
            Self {
                start_time: Instant::now(),
            }
        }
    }
    impl System for StdSystem {
        type AsyncKey = ();
        fn poll_async<'gc>(&mut self, _mc: MutationContext<'gc, '_>, _key: &Self::AsyncKey) -> Result<AsyncPoll<'gc>, SystemError> {
            unimplemented!();
        }
        fn time_ms(&self) -> Result<u64, SystemError> {
            Ok(self.start_time.elapsed().as_millis() as u64)
        }
    }
}
#[cfg(any(test, feature = "std"))]
pub use std_system::*;
