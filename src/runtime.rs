use std::prelude::v1::*;
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::marker::PhantomData;
use std::rc::{Rc, Weak};
use std::fmt;

use rand::distributions::uniform::{SampleUniform, SampleRange};

use crate::*;
use crate::gc::*;
use crate::json::*;

#[derive(Debug)]
pub enum FromJsonError {
    HadNull, HadBadNumber,
}
#[derive(Debug)]
pub enum ToJsonError {
    HadBadNumber(f64),
}

#[derive(Debug, PartialEq)]
pub enum SimpleValue {
    Bool(bool),
    Number(f64),
    String(String),
    List(Vec<SimpleValue>),
}
impl SimpleValue {
    /// Retrieves the value of the [`SimpleValue::Bool`] variant, or [`None`] if that is not the current variant.
    pub fn as_bool(&self) -> Option<bool> { match self { SimpleValue::Bool(x) => Some(*x), _ => None } }
    /// Retrieves the value of the [`SimpleValue::Number`] variant, or [`None`] if that is not the current variant.
    pub fn as_number(&self) -> Option<f64> { match self { SimpleValue::Number(x) => Some(*x), _ => None } }
    /// Retrieves the value of the [`SimpleValue::String`] variant, or [`None`] if that is not the current variant.
    pub fn as_str(&self) -> Option<&str> { match self { SimpleValue::String(x) => Some(x), _ => None } }
    /// Retrieves the value of the [`SimpleValue::List`] variant, or [`None`] if that is not the current variant.
    pub fn as_list(&self) -> Option<&[SimpleValue]> { match self { SimpleValue::List(x) => Some(x), _ => None } }
    /// Retrieves the value of the [`SimpleValue::String`] variant, or [`None`] if that is not the current variant.
    pub fn into_string(self) -> Option<String> { match self { SimpleValue::String(x) => Some(x), _ => None } }
    /// Retrieves the value of the [`SimpleValue::List`] variant, or [`None`] if that is not the current variant.
    pub fn into_list(self) -> Option<Vec<SimpleValue>> { match self { SimpleValue::List(x) => Some(x), _ => None } }

    /// Create a new [`SimpleValue`] from a [`Json`] value.
    /// 
    /// NetsBlox does not allow a concept of null, so [`Json`] values containing [`Json::Null`] will result in [`FromJsonError::HadNull`].
    /// Additionally, `serde_json`'s interface states that [`Json::Number`] values might not be able to be encoded as [`f64`], in which case [`FromJsonError::HadBadNumber`] is returned;
    /// however, based on their source code, this should only be possible with special feature flags passed in to allow arbitrary precision floating point.
    pub fn from_json(value: Json) -> Result<Self, FromJsonError> {
        Ok(match value {
            Json::Null => return Err(FromJsonError::HadNull),
            Json::Bool(x) => x.into(),
            Json::Number(x) => x.as_f64().ok_or(FromJsonError::HadBadNumber)?.into(),
            Json::String(x) => x.into(),
            Json::Array(x) => x.into_iter().map(SimpleValue::from_json).collect::<Result<Vec<_>,_>>()?.into(),
            Json::Object(x) => x.into_iter().map(|(k, v)| Ok(vec![ k.into(), SimpleValue::from_json(v)? ].into())).collect::<Result<Vec<_>,_>>()?.into(),
        })
    }
    /// Convert a [`SimpleValue`] into [`Json`].
    /// 
    /// [`Json`] does not allow numbers to be infinite or nan, which is the only failure case for this conversion.
    pub fn into_json(self) -> Result<Json, ToJsonError> {
        Ok(match self {
            SimpleValue::Bool(x) => Json::Bool(x),
            SimpleValue::Number(x) => match serde_json::Number::from_f64(x) {
                Some(x) => Json::Number(x),
                None => return Err(ToJsonError::HadBadNumber(x)),
            }
            SimpleValue::String(x) => Json::String(x),
            SimpleValue::List(x) => Json::Array(x.into_iter().map(SimpleValue::into_json).collect::<Result<_,_>>()?),
        })
    }
}
impl From<bool> for SimpleValue { fn from(v: bool) -> Self { Self::Bool(v) } }
impl From<f64> for SimpleValue { fn from(v: f64) -> Self { Self::Number(v) } }
impl From<i64> for SimpleValue { fn from(v: i64) -> Self { Self::Number(v as f64) } }
impl From<String> for SimpleValue { fn from(v: String) -> Self { Self::String(v) } }
impl From<Vec<SimpleValue>> for SimpleValue { fn from(v: Vec<SimpleValue>) -> Self { Self::List(v) } }

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

/// An error from converting a [`Value`] to a [`SimpleValue`].
#[derive(Debug)]
pub enum SimplifyError {
    /// The value was or contained a type that cannot be exported as a [`SimpleValue`].
    HadComplexType(Type),
    /// The value contained a cycle, which [`SimpleValue`] forbids.
    HadCycle,
}

/// A value representing the identity of a [`Value`].
#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq,)]
pub struct Identity<'gc>(*const (), PhantomData<&'gc Value<'gc>>);

/// Any primitive value.
#[derive(Clone, Copy, Collect)]
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
    List(GcCell<'gc, VecDeque<Value<'gc>>>),
    /// A closure/lambda function. This contains information about the closure's bytecode location, parameters, and captures from the parent scope.
    Closure(GcCell<'gc, Closure<'gc>>),
    /// A reference to an [`Entity`] in the environment.
    Entity(GcCell<'gc, Entity<'gc>>),
}
impl fmt::Debug for Value<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn print<'gc>(value: &Value<'gc>, cache: &mut BTreeSet<Identity<'gc>>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match value {
                Value::Bool(x) => write!(f, "{x}"),
                Value::Number(x) => write!(f, "{x}"),
                Value::String(x) => write!(f, "{:?}", x.as_str()),
                Value::Closure(x) => write!(f, "{:?}", &*x.read()),
                Value::Entity(x) => write!(f, "{:?}", &*x.read()),
                Value::List(x) => {
                    let identity = value.identity();
                    if !cache.insert(identity) { return write!(f, "[...]") }

                    let x = x.read();
                    write!(f, "[")?;
                    for (i, val) in x.iter().enumerate() {
                        print(val, cache, f)?;
                        if i != x.len() - 1 { write!(f, ",")? }
                    }
                    write!(f, "]")?;

                    debug_assert!(cache.contains(&identity));
                    cache.remove(&identity);
                    Ok(())
                }
            }
        }
        let mut cache = Default::default();
        let res = print(self, &mut cache, f);
        debug_assert_eq!(cache.len(), 0);
        res
    }
}
impl<'gc> From<bool> for Value<'gc> { fn from(v: bool) -> Self { Value::Bool(v) } }
impl<'gc> From<f64> for Value<'gc> { fn from(v: f64) -> Self { Value::Number(v) } }
impl<'gc> From<Gc<'gc, String>> for Value<'gc> { fn from(v: Gc<'gc, String>) -> Self { Value::String(v) } }
impl<'gc> From<GcCell<'gc, VecDeque<Value<'gc>>>> for Value<'gc> { fn from(v: GcCell<'gc, VecDeque<Value<'gc>>>) -> Self { Value::List(v) } }
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
            ast::Value::List(x) => GcCell::allocate(mc, x.iter().map(|x| Value::from_ast(mc, x)).collect::<VecDeque<_>>()).into(),
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
    pub fn to_simple(&self) -> Result<SimpleValue, SimplifyError> {
        fn simplify<'gc>(value: &Value<'gc>, cache: &mut BTreeSet<Identity<'gc>>) -> Result<SimpleValue, SimplifyError> {
            Ok(match value {
                Value::Bool(x) => SimpleValue::Bool(*x),
                Value::Number(x) => SimpleValue::Number(*x),
                Value::String(x) => SimpleValue::String(x.as_str().to_owned()),
                Value::Closure(_) | Value::Entity(_) => return Err(SimplifyError::HadComplexType(value.get_type())),
                Value::List(x) => {
                    let identity = value.identity();
                    if !cache.insert(identity) { return Err(SimplifyError::HadCycle) }
                    let res = SimpleValue::List(x.read().iter().map(|x| simplify(x, cache)).collect::<Result<_,_>>()?);
                    debug_assert!(cache.contains(&identity));
                    cache.remove(&identity);
                    res
                }
            })
        }
        let mut cache = Default::default();
        let res = simplify(self, &mut cache);
        debug_assert_eq!(cache.len(), 0);
        res
    }
    /// Returns a value representing this object that implements [`Eq`] such that
    /// two values are equal if and only if they are references to the same object.
    /// This is primarily useful for testing for reference equality of lists.
    pub fn identity(&self) -> Identity<'gc> {
        match self {
            Value::Bool(x) => Identity(x as *const bool as *const (), PhantomData),
            Value::Number(x) => Identity(x as *const f64 as *const (), PhantomData),
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
    pub fn as_list(&self) -> Result<GcCell<'gc, VecDeque<Value<'gc>>>, ConversionError> {
        match self {
            Value::List(x) => Ok(*x),
            x => Err(ConversionError { got: x.get_type(), expected: Type::List }),
        }
    }
    /// Attempts to interpret this value as a closure.
    pub fn as_closure(&self) -> Result<GcCell<'gc, Closure<'gc>>, ConversionError> {
        match self {
            Value::Closure(x) => Ok(*x),
            x => Err(ConversionError { got: x.get_type(), expected: Type::Closure }),
        }
    }
    /// Attempts to interpret this value as an entity.
    pub fn as_entity(&self) -> Result<GcCell<'gc, Entity<'gc>>, ConversionError> {
        match self {
            Value::Entity(x) => Ok(*x),
            x => Err(ConversionError { got: x.get_type(), expected: Type::Entity }),
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
        write!(f, "Closure {:#08x}", self.pos)
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
        write!(f, "{}Entity {:?}", if self.alive { "" } else { "Dead " }, self.name)
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

/// A blocking handle for a [`BarrierCondition`].
#[derive(Debug, Default, Clone, Collect)]
#[collect(require_static)]
pub struct Barrier(Rc<()>);
/// Waits for the destruction of all associated [`Barrier`] handles.
#[derive(Debug, Clone)]
pub struct BarrierCondition(Weak<()>);
impl Barrier {
    /// Creates a new [`Barrier`] which is not related to any other barrier.
    /// A barrier can be cloned to create additional associated, blocking handles for the same condition.
    pub fn new() -> Self {
        Barrier(Rc::new(()))
    }
    /// Constructs a [`BarrierCondition`] object which waits for this barrier handle and all of its associated handles
    /// (created before or after this point) to be destroyed.
    pub fn get_condition(&self) -> BarrierCondition {
        BarrierCondition(Rc::downgrade(&self.0))
    }
}
impl BarrierCondition {
    /// Checks if the condition has been completed, i.e., that all the associated barriers have been destroyed.
    pub fn is_completed(&self) -> bool {
        self.0.strong_count() == 0
    }
}

/// The result of a successful call to [`System::poll_async`].
pub enum AsyncPoll<T> {
    /// The async operation completed with the given value.
    Completed(T),
    /// The async operation is still pending and has not completed.
    Pending,
}

/// A key from the keyboard.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KeyCode {
    /// A normal character key, such as a letter, number, or special symbol.
    Char(char),
    /// The up arrow key.
    Up,
    /// The down arrow key.
    Down,
    /// The left arrow key.
    Left,
    /// The right arrow key.
    Right,
}

/// Types of [`System`] resources, grouped into feature categories.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SystemFeature {
    /// The ability of a process to generate random numbers.
    Random,
    /// The ability of a process to get the current time (not necessarily wall time).
    Time,
    /// The ability of a process to request keyboard input from the user.
    Input,
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
    /// Key type used to await the result of an RPC request.
    type RpcKey: Collect + 'static;
    /// Key type used to await the result of an "ask" block (string input from the user).
    type InputKey: Collect + 'static;
    /// Key type used to await the result of a "send message and wait" block (response from target).
    type ExternReplyKey: Collect + 'static;
    /// Key type used to reply to a message that was sent to this client with the expectation of receiving a response.
    /// This type is required to be [`Clone`] because there can be multiple message handlers for the same message type.
    type InternReplyKey: Collect + 'static + Clone;

    /// Gets a random value sampled from the given `range`, which is assumed to be non-empty.
    /// The input for this generic function is such that it is compatible with [`rand::Rng::gen_range`],
    /// which makes it possible to implement this function with any random provider under the [`rand`] crate standard.
    fn rand<T, R>(&self, range: R) -> Result<T, SystemError> where T: SampleUniform, R: SampleRange<T>;

    /// Gets the current time in milliseconds.
    /// This is not required to represent the actual real-world time; e.g., this could simply measure uptime.
    /// Subsequent values are required to be non-decreasing.
    fn time_ms(&self) -> Result<u64, SystemError>;

    /// Output [`Some`] [`Value`] or [`None`] to perform a Snap!-style clear.
    /// The [`Entity`] making the request is provided for context.
    /// This operation should be infallible, but a no-op solution is sufficient.
    fn print<'gc>(&self, value: Option<Value<'gc>>, entity: &Entity<'gc>);

    /// Request input from the user.
    /// The `prompt` argument is either [`Some`] prompt to display, or [`None`] for no prompt.
    /// If supported, this operation must be non-blocking and eventually terminate and yield a value to [`System::poll_input`].
    fn input<'gc>(&self, prompt: Option<Value<'gc>>, entity: &Entity<'gc>) -> Result<Self::InputKey, SystemError>;
    /// Polls for the completion of an asynchronous call to [`System::input`].
    /// If [`AsyncPoll::Completed`] is returned, the system is allowed to invalidate the requested `key`, which will not be used again.
    fn poll_input(&self, key: &Self::InputKey) -> AsyncPoll<String>;

    /// Requests the system to execute the given RPC.
    /// Returns a key that can be passed to [`System::poll_rpc`] to poll for the result.
    /// If supported, this operation must be non-blocking and eventually terminate and yield a value to [`System::poll_rpc`].
    fn call_rpc(&self, service: String, rpc: String, args: Vec<(String, Json)>) -> Result<Self::RpcKey, SystemError>;
    /// Polls for the completion of an asynchronous call to [`System::call_rpc`].
    /// If [`AsyncPoll::Completed`] is returned, the system is allowed to invalidate the requested `key`, which will not be used again.
    fn poll_rpc(&self, key: &Self::RpcKey) -> AsyncPoll<Result<Json, String>>;

    /// Sends a message containing a set of named `values` to each of the specified `targets`.
    /// The `expect_reply` value controls whether or not to use a reply mechanism to asynchronously receive a response from the target(s).
    /// In the case that there are multiple targets, only the first reply (if any) should be used.
    fn send_message(&self, msg_type: String, values: Vec<(String, Json)>, targets: Vec<String>, expect_reply: bool) -> Result<Option<Self::ExternReplyKey>, SystemError>;
    /// Polls for a response from a client initiated by [`System::send_message`].
    /// If the client responds, a value of [`Some(x)`] is returned.
    /// The system may elect to impose a timeout for reply results, in which case [`None`] is returned instead.
    fn poll_reply(&self, key: &Self::ExternReplyKey) -> AsyncPoll<Option<Json>>;
    /// Attempts to receive a message from the message buffer.
    /// This operation is always non-blocking and returns [`None`] if there are no messages in the buffer.
    /// If a message is received, a tuple of form `(msg_type, values, reply_key)` is returned.
    fn receive_message(&self) -> Option<(String, Vec<(String, Json)>, Option<Self::InternReplyKey>)>;
    /// Sends a reply to the sender of a blocking message this client received.
    fn send_reply(&self, key: Self::InternReplyKey, value: Json) -> Result<(), SystemError>;
}

#[cfg(any(test, feature = "std"))]
mod std_system {
    extern crate std as real_std;
    use real_std::time::{Instant, SystemTime, UNIX_EPOCH};
    use real_std::sync::{Arc, Mutex};
    use real_std::sync::mpsc::{Sender, Receiver, channel};
    use real_std::thread;

    use derive_builder::Builder;
    use rand_chacha::ChaChaRng;
    use rand::{Rng, SeedableRng};
    use tokio_tungstenite::tungstenite::Message;
    use futures::{StreamExt, SinkExt};
    use uuid::Uuid;

    use super::*;
    use crate::slotmap::SlotMap;

    const MESSAGE_REPLY_TIMEOUT_MS: u32 = 1500;

    new_key! {
        pub struct RpcKey;
        pub struct InputKey;
    }

    #[derive(Debug, Collect, Clone, PartialOrd, Ord, PartialEq, Eq)]
    #[collect(require_static)]
    pub struct ExternReplyKey {
        request_id: String,
    }
    #[derive(Debug, Collect, Clone)]
    #[collect(require_static)]
    pub struct InternReplyKey {
        src_id: String,
        request_id: String,
    }

    struct Context {
        base_url: String,
        client_id: String,

        project_name: String,
        project_id: String,
        role_name: String,
        role_id: String,
    }
    struct RpcRequest {
        service: String,
        rpc: String,
        args: Vec<(String, Json)>,
        result_key: RpcKey,
    }
    enum OutgoingMessage {
        Normal {
            msg_type: String,
            values: Vec<(String, Json)>,
            targets: Vec<String>,
        },
        Blocking {
            msg_type: String,
            values: Vec<(String, Json)>,
            targets: Vec<String>,
            reply_key: ExternReplyKey,
        },
        Reply {
            value: Json,
            reply_key: InternReplyKey,
        },
    }
    struct IncomingMessage {
        msg_type: String,
        values: Vec<(String, Json)>,
        reply_key: Option<InternReplyKey>,
    }
    struct ReplyEntry {
        timestamp: Instant,
        value: Option<Json>,
    }

    type RpcResults = SlotMap<RpcKey, Option<Result<Json, String>>>;
    type InputResults = SlotMap<InputKey, Option<String>>;
    type MessageReplies = BTreeMap<ExternReplyKey, ReplyEntry>;

    #[derive(Builder)]
    pub struct StdSystemConfig {
        /// A function used to process all "say" and "think" blocks.
        /// The first argument is the actual message value, or [`None`] to clear the output (Snap!-style).
        /// The second argument is a reference to the entity making the request.
        /// The default printer is no-op, effectively ignoring all output requests.
        #[builder(default = "Rc::new(|_, _| ())")]
        print: Rc<dyn for<'gc> Fn(Option<Value<'gc>>, &Entity<'gc>)>,
        /// A function used to request input from the user.
        /// This should be non-blocking, and the provided [`InputKey`]
        /// should be given to [`StdSystem::finish_input`] when the value is entered by the user.
        /// If not specified (default), the system gives an error when processes attempt to request user input.
        #[builder(default = "None", setter(strip_option))]
        input: Option<Rc<dyn for<'gc> Fn(Option<Value<'gc>>, &Entity<'gc>, InputKey)>>,
    }
    impl StdSystemConfig {
        /// Constructs a new default instance of [`StdSystemConfigBuilder`].
        pub fn builder() -> StdSystemConfigBuilder { Default::default() }
    }

    async fn call_rpc_async(context: &Context, client: &reqwest::Client, service: &str, rpc: &str, args: &[(&str, &Json)]) -> Result<Json, String> {
        let time = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_millis();
        let url = format!("{base_url}/services/{service}/{rpc}?uuid={client_id}&projectId={project_id}&roleId={role_id}&t={time}",
            base_url = context.base_url, client_id = context.client_id, project_id = context.project_id, role_id = context.role_id);
        let args: BTreeMap<&str, &Json> = args.iter().copied().collect();

        match client.post(url).json(&args).send().await {
            Ok(res) => {
                let status = res.status();
                match res.text().await {
                    Ok(text) => match status.is_success() {
                        true => Ok(serde_json::from_str(&text).unwrap_or(Json::String(text))),
                        false => Err(text),
                    }
                    Err(_) => Err("Failed to read response body".to_owned()),
                }
            }
            Err(_) => Err(format!("Failed to reach {}", context.base_url)),
        }
    }

    /// A type implementing the [`System`] trait which supports all features.
    /// This requires the [`std`](crate) feature flag.
    pub struct StdSystem {
        config: StdSystemConfig,
        context: Arc<Context>,
        client: Arc<reqwest::Client>,
        start_time: Instant,
        rng: Mutex<ChaChaRng>,

        input_results: Arc<Mutex<InputResults>>,

        rpc_results: Arc<Mutex<RpcResults>>,
        rpc_request_pipe: Sender<RpcRequest>,

        message_replies: Arc<Mutex<MessageReplies>>,
        message_sender: Sender<OutgoingMessage>,
        message_receiver: Receiver<IncomingMessage>,
    }
    impl StdSystem {
        #[tokio::main(flavor = "current_thread")]
        pub async fn new(base_url: String, project_name: Option<&str>, config: StdSystemConfig) -> Self {
            let mut context = Context {
                base_url,
                client_id: format!("vm-{}", names::Generator::default().next().unwrap()),
                project_name: project_name.unwrap_or("untitled").to_owned(),

                project_id: String::new(),
                role_name: String::new(),
                role_id: String::new(),
            };

            let message_replies = Arc::new(Mutex::new(Default::default()));
            let (message_sender, message_receiver) = {
                let (base_url, client_id, project_name, message_replies) = (context.base_url.clone(), context.client_id.clone(), context.project_name.clone(), message_replies.clone());
                let (out_sender, out_receiver) = channel();
                let (in_sender, in_receiver) = channel();

                #[tokio::main(flavor = "multi_thread", worker_threads = 1)]
                async fn handler(base_url: String, client_id: String, project_name: String, message_replies: Arc<Mutex<MessageReplies>>, out_receiver: Receiver<OutgoingMessage>, in_sender: Sender<IncomingMessage>) {
                    let ws_url = if let Some(x) = base_url.strip_prefix("http") { format!("ws{}", x) } else { format!("wss://{}", base_url) };
                    let (ws, _) = tokio_tungstenite::connect_async(ws_url).await.unwrap();
                    let (mut ws_sender, ws_receiver) = ws.split();
                    let (ws_sender_sender, ws_sender_receiver) = async_channel::unbounded();

                    tokio::spawn(async move {
                        while let Ok(msg) = ws_sender_receiver.recv().await {
                            ws_sender.send(msg).await.unwrap();
                        }
                    });

                    let ws_sender_sender_clone = ws_sender_sender.clone();
                    tokio::spawn(async move {
                        ws_receiver.for_each(move |packet| {
                            let ws_sender_sender_clone = ws_sender_sender_clone.clone();
                            let in_sender = in_sender.clone();
                            let message_replies = message_replies.clone();
                            async move {
                                let mut msg = match packet {
                                    Ok(Message::Text(raw)) => match serde_json::from_str::<BTreeMap<String, Json>>(&raw) {
                                        Ok(x) => x,
                                        Err(_) => return,
                                    }
                                    _ => return,
                                };
                                match msg.get("type").and_then(|x| x.as_str()).unwrap_or("unknown") {
                                    "ping" => ws_sender_sender_clone.send(Message::Text(json!({ "type": "pong" }).to_string())).await.unwrap(),
                                    "message" => {
                                        let (msg_type, values) = match (msg.remove("msgType"), msg.remove("content")) {
                                            (Some(Json::String(msg_type)), Some(Json::Object(values))) => (msg_type, values),
                                            _ => return,
                                        };
                                        if msg_type == "__reply__" {
                                            let (value, reply_key) = match ({ values }.remove("body"), msg.remove("requestId")) {
                                                (Some(value), Some(Json::String(request_id))) => (value, ExternReplyKey { request_id }),
                                                _ => return,
                                            };
                                            if let Some(entry) = message_replies.lock().unwrap().get_mut(&reply_key) {
                                                if entry.value.is_none() {
                                                    entry.value = Some(value);
                                                }
                                            }
                                        } else {
                                            let reply_key = match msg.contains_key("requestId") {
                                                true => match (msg.remove("srcId"), msg.remove("requestId")) {
                                                    (Some(Json::String(src_id)), Some(Json::String(request_id))) => Some(InternReplyKey { src_id, request_id }),
                                                    _ => return,
                                                }
                                                false => None,
                                            };
                                            in_sender.send(IncomingMessage { msg_type, values: values.into_iter().collect(), reply_key }).unwrap();
                                        }
                                    }
                                    _ => (),
                                }
                            }
                        }).await;
                    });

                    ws_sender_sender.send(Message::Text(json!({ "type": "set-uuid", "clientId": client_id }).to_string())).await.unwrap();

                    while let Ok(request) = out_receiver.recv() {
                        let msg = match request {
                            OutgoingMessage::Normal { msg_type, values, targets } => json!({
                                "type": "message",
                                "dstId": targets,
                                "srcId": format!("{}@{}", project_name, client_id),
                                "msgType": msg_type,
                                "content": values.into_iter().collect::<serde_json::Map<_,_>>(),
                            }),
                            OutgoingMessage::Blocking { msg_type, values, targets, reply_key } => json!({
                                "type": "message",
                                "dstId": targets,
                                "srcId": format!("{}@{}", project_name, client_id),
                                "msgType": msg_type,
                                "requestId": reply_key.request_id,
                                "content": values.into_iter().collect::<serde_json::Map<_,_>>(),
                            }),
                            OutgoingMessage::Reply { value, reply_key } => json!({
                                "type": "message",
                                "dstId": reply_key.src_id,
                                "msgType": "__reply__",
                                "requestId": reply_key.request_id,
                                "content": { "body": value },
                            }),
                        };
                        ws_sender_sender.send(Message::Text(msg.to_string())).await.unwrap();
                    }
                }
                thread::spawn(move || handler(base_url, client_id, project_name, message_replies, out_receiver, in_sender));

                (out_sender, in_receiver)
            };

            let client = Arc::new(reqwest::Client::builder().build().unwrap());
            let meta = client.post(format!("{}/api/newProject", context.base_url))
                .json(&json!({ "clientId": context.client_id, "roleName": "monad" }))
                .send().await.unwrap()
                .json::<BTreeMap<String, Json>>().await.unwrap();
            context.project_id = meta["projectId"].as_str().unwrap().to_owned();
            context.role_id = meta["roleId"].as_str().unwrap().to_owned();
            context.role_name = meta["roleName"].as_str().unwrap().to_owned();

            let meta = client.post(format!("{}/api/setProjectName", context.base_url))
                .json(&json!({ "projectId": context.project_id, "name": context.project_name }))
                .send().await.unwrap()
                .json::<BTreeMap<String, Json>>().await.unwrap();
            context.project_name = meta["name"].as_str().unwrap().to_owned();

            let context = Arc::new(context);
            let rpc_results = Arc::new(Mutex::new(Default::default()));
            let rpc_request_pipe = {
                let (client, context, rpc_results) = (client.clone(), context.clone(), rpc_results.clone());
                let (sender, receiver) = channel();

                #[tokio::main(flavor = "multi_thread", worker_threads = 1)]
                async fn handler(client: Arc<reqwest::Client>, context: Arc<Context>, rpc_results: Arc<Mutex<RpcResults>>, receiver: Receiver<RpcRequest>) {
                    while let Ok(request) = receiver.recv() {
                        let (client, context, rpc_results) = (client.clone(), context.clone(), rpc_results.clone());
                        tokio::spawn(async move {
                            let res = call_rpc_async(&context, &client, &request.service, &request.rpc, &request.args.iter().map(|x| (x.0.as_str(), &x.1)).collect::<Vec<_>>()).await;
                            assert!(rpc_results.lock().unwrap().get_mut(request.result_key).unwrap().replace(res).is_none());
                        });
                    }
                }
                thread::spawn(move || handler(client, context, rpc_results, receiver));

                sender
            };

            let mut seed: <ChaChaRng as SeedableRng>::Seed = Default::default();
            getrandom::getrandom(&mut seed).expect("failed to generate random seed");

            Self {
                config, context, client,
                start_time: Instant::now(),
                rng: Mutex::new(ChaChaRng::from_seed(seed)),
                input_results: Default::default(),
                rpc_results, rpc_request_pipe,
                message_replies, message_sender, message_receiver,
            }
        }

        /// Asynchronously calls an RPC and returns the result.
        /// This function directly makes requests to NetsBlox, bypassing any RPC hook defined by [`StdSystemConfig`].
        pub async fn call_rpc_async(&self, service: &str, rpc: &str, args: &[(&str, &Json)]) -> Result<Json, String> {
            call_rpc_async(&self.context, &self.client, service, rpc, args).await
        }
        /// Finishes an asynchronous request to get input from the user.
        /// The key provided must only be used once - future usage of the same key will result in a panic.
        pub fn finish_input(&self, key: InputKey, content: String) {
            assert!(self.input_results.lock().unwrap().get_mut(key).unwrap().replace(content).is_none());
        }

        /// Gets the public id of the running system that can be used to send messages to this client.
        pub fn get_public_id(&self) -> String {
            format!("{}@{}", self.context.project_name, self.context.client_id)
        }
    }
    impl System for StdSystem {
        type RpcKey = RpcKey;
        type InputKey = InputKey;
        type ExternReplyKey = ExternReplyKey;
        type InternReplyKey = InternReplyKey;

        fn rand<T, R>(&self, range: R) -> Result<T, SystemError> where T: SampleUniform, R: SampleRange<T> {
            Ok(self.rng.lock().unwrap().gen_range(range))
        }

        fn time_ms(&self) -> Result<u64, SystemError> {
            Ok(self.start_time.elapsed().as_millis() as u64)
        }

        fn print<'gc>(&self, value: Option<Value<'gc>>, entity: &Entity<'gc>) {
            self.config.print.as_ref()(value, entity)
        }

        fn input<'gc>(&self, prompt: Option<Value<'gc>>, entity: &Entity<'gc>) -> Result<Self::InputKey, SystemError> {
            match self.config.input.as_ref() {
                Some(input) => {
                    let key = self.input_results.lock().unwrap().insert(None);
                    input(prompt, entity, key);
                    Ok(key)
                }
                None => Err(SystemError::NotSupported { feature: SystemFeature::Input }),
            }
        }
        fn poll_input(&self, key: &Self::InputKey) -> AsyncPoll<String> {
            let mut input_results = self.input_results.lock().unwrap();
            match input_results.get(*key).unwrap().is_some() {
                true => AsyncPoll::Completed(input_results.remove(*key).unwrap().unwrap()),
                false => AsyncPoll::Pending,
            }
        }

        fn call_rpc(&self, service: String, rpc: String, args: Vec<(String, Json)>) -> Result<Self::RpcKey, SystemError> {
            let result_key = self.rpc_results.lock().unwrap().insert(None);
            self.rpc_request_pipe.send(RpcRequest { service, rpc, args, result_key }).unwrap();
            Ok(result_key)
        }
        fn poll_rpc(&self, key: &Self::RpcKey) -> AsyncPoll<Result<Json, String>> {
            let mut rpc_results = self.rpc_results.lock().unwrap();
            match rpc_results.get(*key).unwrap().is_some() {
                true => AsyncPoll::Completed(rpc_results.remove(*key).unwrap().unwrap()),
                false => AsyncPoll::Pending,
            }
        }

        fn send_message(&self, msg_type: String, values: Vec<(String, Json)>, targets: Vec<String>, expect_reply: bool) -> Result<Option<Self::ExternReplyKey>, SystemError> {
            let (msg, reply_key) = match expect_reply {
                false => (OutgoingMessage::Normal { msg_type, values, targets }, None),
                true => {
                    let reply_key = ExternReplyKey { request_id: Uuid::new_v4().to_string() };
                    self.message_replies.lock().unwrap().insert(reply_key.clone(), ReplyEntry { timestamp: Instant::now(), value: None });
                    (OutgoingMessage::Blocking { msg_type, values, targets, reply_key: reply_key.clone() }, Some(reply_key))
                }
            };
            self.message_sender.send(msg).unwrap();
            Ok(reply_key)
        }
        fn poll_reply(&self, key: &Self::ExternReplyKey) -> AsyncPoll<Option<Json>> {
            let mut message_replies = self.message_replies.lock().unwrap();
            let entry = message_replies.get(key).unwrap();
            if entry.value.is_some() {
                return AsyncPoll::Completed(message_replies.remove(key).unwrap().value);
            }
            if entry.timestamp.elapsed().as_millis() as u32 >= MESSAGE_REPLY_TIMEOUT_MS {
                message_replies.remove(key).unwrap();
                return AsyncPoll::Completed(None);
            }
            AsyncPoll::Pending
        }
        fn send_reply(&self, key: Self::InternReplyKey, value: Json) -> Result<(), SystemError> {
            self.message_sender.send(OutgoingMessage::Reply { value, reply_key: key }).unwrap();
            Ok(())
        }
        fn receive_message(&self) -> Option<(String, Vec<(String, Json)>, Option<Self::InternReplyKey>)> {
            self.message_receiver.try_recv().ok().map(|x| (x.msg_type, x.values, x.reply_key))
        }
    }
}
#[cfg(any(test, feature = "std"))]
pub use std_system::*;
