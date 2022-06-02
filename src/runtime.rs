//! Common types used for execution.

use std::prelude::v1::*;
use std::collections::BTreeMap;
use std::cell::{Cell, RefCell};
use std::rc::{Rc, Weak};
use std::mem;
use std::fmt;

use netsblox_ast as ast;

/// The type of a [`Value`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Type {
    Bool, Number, String, List, Closure,
}

/// A type conversion error on a [`Value`].
#[derive(Debug)]
pub struct ConversionError {
    pub got: Type,
    pub expected: Type,
}

/// A failed [`Weak`] upgrade operation on a [`Value::List`].
#[derive(Debug)]
pub struct ListUpgradeError {
    pub weak: Weak<RefCell<Vec<Value>>>,
}
/// A failed [`Weak`] upgrade operation on a [`Value::Closure`].
#[derive(Debug)]
pub struct ClosureUpgradeError {
    pub weak: Weak<RefCell<Closure>>,
}

/// A failed conversion of a [`Value`] to a list of [`Value`].
#[derive(Debug)]
pub enum ListConversionError {
    ConversionError(ConversionError),
    ListUpgradeError(ListUpgradeError),
}
trivial_from_impl! { ListConversionError: ConversionError, ListUpgradeError }
/// A failed conversion of a [`Value`] to a [`Closure`].
#[derive(Debug)]
pub enum ClosureConversionError {
    ConversionError(ConversionError),
    ClosureUpgradeError(ClosureUpgradeError),
}
trivial_from_impl! { ClosureConversionError: ConversionError, ClosureUpgradeError }

/// A convenience trait for working with [`Value::List`] handles.
pub trait CheckedUpgrade {
    type Success;
    type Error;
    fn checked_upgrade(&self) -> Result<Self::Success, Self::Error>;
}
macro_rules! UpgradeImpl {
    ($inner:ty : $err:ty) => {
        impl CheckedUpgrade for Weak<$inner> {
            type Success = Rc<$inner>;
            type Error = $err;
            fn checked_upgrade(&self) -> Result<Self::Success, Self::Error> {
                match self.upgrade() {
                    Some(x) => Ok(x),
                    None => Err(Self::Error { weak: self.clone() }),
                }
            }
        }
    }
}
UpgradeImpl! { RefCell<Vec<Value>> : ListUpgradeError }
UpgradeImpl! { RefCell<Closure> : ClosureUpgradeError }

/// Information about a closure/lambda function.
/// 
/// Used by [`Value::Closure`].
pub struct Closure {
    pub pos: usize,
    pub params: Vec<String>,
    pub captures: SymbolTable,
}
impl fmt::Debug for Closure {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[Closure]")
    }
}

/// Any primitive value.
/// 
/// This type implements [`Clone`] but not [`Copy`]; however, cloning a `Value` is guaranteed to be nearly-trivial
/// (up to reference counting increments) due to having the same reference-type semantics as Snap! and NetsBlox.
#[derive(Clone, Debug)]
pub enum Value {
    /// A primitive boolean value.
    Bool(bool),
    /// A primitive numeric value.
    /// Snap! and NetsBlox use 64-bit floating point values for all numbers.
    Number(f64),
    /// A primitive string value, which is an immutable reference type.
    /// Each string is weakly-linked to a [`RefPool`] to facilitate string interning if requested.
    String(Rc<String>),
    /// A primitive list type, which is a mutable reference type.
    /// `Value` holds lists by weak reference so that containment cycles do not cause memory leaks.
    /// The (only) owning reference to a list is allocated in a [`RefPool`],
    /// which can perform garbage collection logic upon request.
    List(Weak<RefCell<Vec<Value>>>),
    /// A closure/lambda function.
    /// This contains information about the closure's bytecode location, parameters, and captures from the parent scope.
    /// This must be held by weak reference to avoid creating cycles due to captures.
    Closure(Weak<RefCell<Closure>>),

}
impl Value {
    /// Creates a new value from an abstract syntax tree value.
    /// In the event that `value` is a reference type, it is tied to the provided [`RefPool`].
    /// 
    /// The `intern` flag controls whether to perform interning for string values.
    pub fn from_ast(value: &ast::Value, ref_pool: &mut RefPool, intern: bool) -> Self {
        match value {
            ast::Value::Bool(x) => Value::Bool(*x),
            ast::Value::Number(x) => Value::Number(*x),
            ast::Value::Constant(ast::Constant::E) => Value::Number(std::f64::consts::E),
            ast::Value::Constant(ast::Constant::Pi) => Value::Number(std::f64::consts::PI),
            ast::Value::String(x) => Self::from_string(x.clone(), ref_pool, intern),
            ast::Value::List(x) => Self::from_vec(x.iter().map(|x| Value::from_ast(x, ref_pool, intern)).collect(), ref_pool),
        }
    }
    /// Creates a new [`Value::List`] object with the given values.
    /// The list is allocated in the provided [`RefPool`].
    pub fn from_vec(values: Vec<Value>, ref_pool: &mut RefPool) -> Self {
        let rc = Rc::new(RefCell::new(values));
        let weak = Rc::downgrade(&rc);
        ref_pool.list_pool.push(rc);
        Value::List(weak)
    }
    /// Creates a new [`Value::Closure`] object with the given value.
    /// The closure is allocated in the provided [`RefPool`].
    pub fn from_closure(closure: Closure, ref_pool: &mut RefPool) -> Self {
        let rc = Rc::new(RefCell::new(closure));
        let weak = Rc::downgrade(&rc);
        ref_pool.closure_pool.push(rc);
        Value::Closure(weak)
    }
    /// Creates a new [`Value::String`] object with the given value.
    /// 
    /// The `intern` flag controls whether to perform interning.
    pub fn from_string(value: String, ref_pool: &mut RefPool, intern: bool) -> Self {
        if intern {
            for v in ref_pool.string_pool.iter() {
                if let Some(rc) = v.upgrade() {
                    if *rc == value { return Value::String(rc); }
                }
            }
        }
        let rc = Rc::new(value);
        ref_pool.string_pool.push(Rc::downgrade(&rc));
        Value::String(rc)
    }
    /// Returns a pointer to the underlying allocated memory for this value.
    /// This is meant only for checking reference equality of values (e.g., of lists/strings), and the result should never be dereferenced.
    pub fn alloc_ptr(&self) -> *const () {
        match self {
            Value::Bool(x) => &*x as *const bool as *const (),
            Value::Number(x) => &*x as *const f64 as *const (),
            Value::String(x) => &**x as *const String as *const (),
            Value::List(x) => x.as_ptr() as *const Vec<Value> as *const (),
            Value::Closure(x) => x.as_ptr() as *const Closure as *const (),
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
        }
    }
    /// Attempts to interpret this value as a number.
    pub fn to_number(&self) -> Result<f64, ConversionError> {
        Ok(match self {
            Value::Number(x) => *x,
            Value::String(x) => match x.parse() {
                Ok(x) => x,
                Err(_) => return Err(ConversionError { got: Type::String, expected: Type::Number }),
            }
            x => return Err(ConversionError { got: x.get_type(), expected: Type::Number }),
        })
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
    /// Attempts to interpret this value as a list.
    /// On success, yields an owning [`Rc`] handle to the allocated vector,
    /// as opposed to the [`Weak`] handle normally stored by a [`Value::List`] object.
    pub fn to_list(&self) -> Result<Rc<RefCell<Vec<Value>>>, ListConversionError> {
        match self {
            Value::List(x) => Ok(x.checked_upgrade()?),
            x => Err(ConversionError { got: x.get_type(), expected: Type::List }.into()),
        }
    }
    /// Attempts to interpret this value as a closure.
    /// On success, yields an owning [`Rc`] handle to the closure,
    /// as opposed to the [`Weak`] handle normally stored by a [`Value::Closure`] object.
    pub fn to_closure(&self) -> Result<Rc<RefCell<Closure>>, ClosureConversionError> {
        match self {
            Value::Closure(x) => Ok(x.checked_upgrade()?),
            x => Err(ConversionError { got: x.get_type(), expected: Type::Closure }.into()),
        }
    }
    /// Creates a shallow copy of this value, using the designated [`RefPool`] in the event that this value is a reference type.
    pub fn shallow_copy(&self, ref_pool: &mut RefPool) -> Result<Value, ListUpgradeError> {
        Ok(match self {
            Value::Bool(x) => Value::Bool(*x),
            Value::Number(x) => Value::Number(*x),
            Value::String(x) => Value::String(x.clone()),
            Value::List(x) => Value::from_vec(x.checked_upgrade()?.borrow().to_owned(), ref_pool),
            Value::Closure(x) => Value::Closure(x.clone()),
        })
    }
}
impl From<bool> for Value {
    fn from(val: bool) -> Self { Self::Bool(val) }
}
impl From<f64> for Value {
    fn from(val: f64) -> Self { Self::Number(val) }
}
impl Default for Value {
    fn default() -> Self { Self::Number(0.0) }
}

/// An allocation arena for reference-type values (see [`Value`]).
#[derive(Default)]
pub struct RefPool {
    string_pool: Vec<Weak<String>>,
    list_pool: Vec<Rc<RefCell<Vec<Value>>>>,
    closure_pool: Vec<Rc<RefCell<Closure>>>,
}

/// Represents a shared mutable resource.
/// 
/// This is effectively equivalent to [`Rc<Cell<T>`] except that it performs no dynamic allocation
/// for the [`Shared::Unique`] case, which is assumed to be significantly more likely than [`Shared::Aliased`].
pub enum Shared<T> {
    /// A shared resource which has only (this) single unique handle.
    Unique(T),
    /// One of several handles to a single shared resource.
    Aliased(Rc<Cell<T>>),
}
impl<T> Shared<T> {
    /// Sets the value of the shared resource.
    fn set(&mut self, value: T) {
        match self {
            Shared::Unique(x) => *x = value,
            Shared::Aliased(x) => x.set(value),
        }
    }
}
impl<T> Shared<T> where T: Default {
    /// Creates an aliasing instance of [`Shared`] to the same resource as this one.
    /// If this instance is the [`Shared::Unique`] variant, transitions to [`Shared::Aliased`] and returns a second handle.
    /// Otherwise, this simple returns an additional handle to the aliased shared resource.
    pub fn alias(&mut self) -> Self {
        match self {
            Shared::Unique(x) => {
                let rc = Rc::new(Cell::new(mem::take(x)));
                *self = Shared::Aliased(rc.clone());
                Shared::Aliased(rc)
            }
            Shared::Aliased(x) => Shared::Aliased(x.clone()),
        }
    }
}
impl<T> Shared<T> where T: Default + Clone {
    /// Gets a copy of the shared resource's currently stored value.
    pub fn get_clone(&self) -> T {
        match self {
            Shared::Unique(x) => x.clone(),
            Shared::Aliased(x) => {
                let value = x.take();
                x.set(value.clone());
                value
            }
        }
    }
}
impl<T> From<T> for Shared<T> {
    fn from(value: T) -> Self { Shared::Unique(value) }
}

/// Holds a collection of variables in an execution context.
/// 
/// `SymbolTable` has utilities to extract variables from an abstract syntax tree,
/// or to explicitly define variables.
/// To perform value lookups, use the higher-level utility [`LookupGroup`].
#[derive(Default)]
pub struct SymbolTable(BTreeMap<String, Shared<Value>>);
impl SymbolTable {
    fn from_var_defs(var_defs: &[ast::VariableDef], ref_pool: &mut RefPool) -> Self {
        Self(var_defs.iter().map(|x| (x.trans_name.clone(), Value::from_ast(&x.value, ref_pool, true).into())).collect())
    }
    /// Extracts a symbol table containing all the global variables in the project.
    pub fn from_globals(role: &ast::Role, ref_pool: &mut RefPool) -> Self {
        Self::from_var_defs(&role.globals, ref_pool)
    }
    /// Extracts a symbol table containing all the fields in a given entity.
    pub fn from_fields(entity: &ast::Entity, ref_pool: &mut RefPool) -> Self {
        Self::from_var_defs(&entity.fields, ref_pool)
    }
    /// Sets the value of an existing variable (as if by [`Shared::set`]) or defines it if it does not exist.
    /// If the variable does not exist, creates a [`Shared::Unique`] instance for the new `value`.
    /// If you would prefer to always create a new, non-aliased value, consider using [`SymbolTable::redefine_or_define`] instead.
    pub fn set_or_define(&mut self, var: &str, value: Value) {
        match self.0.get_mut(var) {
            Some(x) => x.set(value),
            None => { self.0.insert(var.to_owned(), value.into()); }
        }
    }
    /// Defines or redefines a value in the symbol table to a new instance of [`Shared::Unique`].
    /// Note that this is not the same as [`SymbolTable::set_or_define`], which sets a value on a potentially aliased variable.
    /// The result of this function is that `var` is always an instance of [`Shared::Unique`].
    /// If a variable named `var` already existed and was [`Shared::Aliased`], its value is not modified.
    pub fn redefine_or_define(&mut self, var: &str, value: Shared<Value>) {
        self.0.insert(var.to_owned(), value);
    }
    /// A convenience function which is equivalent to repeated use of [`SymbolTable::redefine_or_define`] and [`Shared::alias`]
    /// to create a new symbol table with all values aliasing the originals.
    pub fn alias(&mut self) -> SymbolTable {
        let mut res = SymbolTable::default();
        for (k, v) in self.0.iter_mut() {
            res.redefine_or_define(k, v.alias());
        }
        res
    }
}

/// A collection of symbol tables with hierarchical context searching.
pub struct LookupGroup<'a, 'b>(&'a mut [&'b mut SymbolTable]);
impl<'a, 'b> LookupGroup<'a, 'b> {
    /// Creates a new lookup group.
    /// The first symbol table is intended to be the most-global, and subsequent tables are increasingly more-local.
    /// Panics if `tabs` is empty.
    pub(crate) fn new(tabs: &'a mut [&'b mut SymbolTable]) -> Self {
        debug_assert!(!tabs.is_empty());
        Self(tabs)
    }
    /// Searches for the given variable in this group of lookup tables,
    /// starting with the last (most-local) table and working towards the first (most-global) table.
    /// Returns a reference to the value if it is found, otherwise returns `None`.
    pub fn lookup(&self, var: &str) -> Option<&Shared<Value>> {
        for src in self.0.iter().rev() {
            if let Some(val) = src.0.get(var) {
                return Some(val);
            }
        }
        None
    }
    /// As [`LookupGroup::lookup`], but returns a mutable reference.
    pub fn lookup_mut(&mut self, var: &str) -> Option<&mut Shared<Value>> {
        for src in self.0.iter_mut().rev() {
            if let Some(val) = src.0.get_mut(var) {
                return Some(val);
            }
        }
        None
    }
    /// Performs a lookup for the given variable.
    /// If it already exists, assigns it a new value.
    /// Otherwise, defines it in the last (most-local) context equivalently to [`SymbolTable::set_or_define`].
    pub fn set_or_define(&mut self, var: &str, value: Value) {
        match self.lookup_mut(var) {
            Some(x) => x.set(value),
            None => self.0.last_mut().unwrap().set_or_define(var, value),
        }
    }
    /// Gets a mutable reference to the last (most-local) context.
    pub fn locals_mut(&mut self) -> &mut SymbolTable {
        self.0.last_mut().unwrap()
    }
}
