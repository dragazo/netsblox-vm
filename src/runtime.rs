//! Common types used for execution.

use std::prelude::v1::*;
use std::collections::BTreeMap;

use netsblox_ast as ast;
use slotmap::SlotMap;

slotmap::new_key_type! {
    pub struct RefPoolKey;
}

/// Any value type primitive.
/// 
/// `CopyValue` variables are held directly by a [`Process`](crate::process::Process) and are copied when a new reference is needed.
#[derive(Clone, Copy, Debug)]
pub enum CopyValue {
    Bool(bool),
    Number(f64),
}
/// Any reference type primitive.
/// 
/// `RefValue` variables are held indirectly by a [`RefPoolKey`], which is an index into an external [`RefPool`]
/// which is provided from outside of a [`Process`](crate::process::Process).
/// 
/// This type itself is owning. [`Value::RefValue`] is the mechanism for actually sharing references to this type.
#[derive(Debug)]
pub enum RefValue {
    String(String),
    List(Vec<Value>),
}
/// Any primitive type.
/// 
/// Values are always copyable, which is how new references are created.
/// [`CopyValue`] variables receive a direct copy, while [`RefValue`] variables simply copy the reference.
#[derive(Clone, Copy, Debug)]
pub enum Value {
    CopyValue(CopyValue),
    RefValue(RefPoolKey),
}
impl Value {
    /// Creates a new value from an abstract syntax tree value.
    /// In the event that `value` is a reference type, it is allocated in the provided [`RefPool`].
    pub fn from_ast(value: &ast::Value, ref_pool: &mut RefPool) -> Self {
        match value {
            ast::Value::Bool(x) => Value::CopyValue(CopyValue::Bool(*x)),
            ast::Value::Number(x) => Value::CopyValue(CopyValue::Number(*x)),
            ast::Value::Constant(ast::Constant::E) => Value::CopyValue(CopyValue::Number(std::f64::consts::E)),
            ast::Value::Constant(ast::Constant::Pi) => Value::CopyValue(CopyValue::Number(std::f64::consts::PI)),
            ast::Value::String(x) => Self::from_string(x.clone(), ref_pool),
            ast::Value::List(x) => Self::from_vec(x.iter().map(|x| Value::from_ast(x, ref_pool)).collect(), ref_pool),
        }
    }
    /// Creates a new [`RefValue::List`] object with the given values.
    pub fn from_vec(values: Vec<Value>, ref_pool: &mut RefPool) -> Self {
        Value::RefValue(ref_pool.pool.insert(RefValue::List(values)))
    }
    /// Creates a new [`RefValue::String`] object with the given value.
    pub fn from_string(value: String, ref_pool: &mut RefPool) -> Self {
        if ref_pool.intern {
            for (k, v) in ref_pool.pool.iter() {
                match v {
                    RefValue::String(s) if *s == value => return Value::RefValue(k),
                    _ => (),
                }
            }
        }
        Value::RefValue(ref_pool.pool.insert(RefValue::String(value)))
    }
    /// Checks if this value is truthy, using the provided [`RefPool`] in the event that this value is of reference type.
    /// If the value is a reference type but is not found in `ref_pool`, returns `Err` with the offending key.
    pub fn is_truthy(&self, ref_pool: &RefPool) -> Result<bool, RefPoolKey> {
        Ok(match self {
            Value::CopyValue(CopyValue::Bool(x)) => *x,
            Value::CopyValue(CopyValue::Number(x)) => *x != 0.0 && !x.is_nan(),
            Value::RefValue(key) => match ref_pool.get(*key) {
                None => return Err(*key),
                Some(x) => match x {
                    RefValue::List(_) => true,
                    RefValue::String(x) => !x.is_empty(),
                }
            }
        })
    }
}

impl From<bool> for CopyValue {
    fn from(val: bool) -> Self {
        Self::Bool(val)
    }
}
impl From<f64> for CopyValue {
    fn from(val: f64) -> Self {
        Self::Number(val)
    }
}
impl<T: Into<CopyValue>> From<T> for Value {
    fn from(val: T) -> Self {
        Self::CopyValue(val.into())
    }
}

pub struct RefPool {
    pool: SlotMap<RefPoolKey, RefValue>,
    intern: bool,
}
impl RefPool {
    pub fn new(intern: bool) -> Self {
        Self { pool: Default::default(), intern }
    }
    pub fn get(&self, key: RefPoolKey) -> Option<&RefValue> {
        self.pool.get(key)
    }
}

/// Holds a collection of variables in an execution context.
#[derive(Default, Debug)]
pub struct SymbolTable(BTreeMap<String, Value>);
impl SymbolTable {
    fn from_var_defs(var_defs: &[ast::VariableDef], ref_pool: &mut RefPool) -> Self {
        Self(var_defs.iter().map(|x| (x.trans_name.clone(), Value::from_ast(&x.value, ref_pool))).collect())
    }
    /// Extracts a symbol table containing all the global variables in the project.
    pub fn from_globals(role: &ast::Role, ref_pool: &mut RefPool) -> Self {
        Self::from_var_defs(&role.globals, ref_pool)
    }
    /// Extracts a symbol table containing all the fields in a given entity.
    pub fn from_fields(entity: &ast::Sprite, ref_pool: &mut RefPool) -> Self {
        Self::from_var_defs(&entity.fields, ref_pool)
    }
    /// Sets the value of an existing variable or defines it if it does not exist.
    pub fn set_or_define(&mut self, var: &str, value: Value) {
        match self.0.get_mut(var) {
            Some(x) => *x = value,
            None => { self.0.insert(var.to_owned(), value); }
        }
    }
}

/// A collection of symbol tables with hierarchical context searching.
#[derive(Debug)]
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
    pub fn lookup(&self, var: &str) -> Option<Value> {
        for src in self.0.iter().rev() {
            if let Some(val) = src.0.get(var) {
                return Some(*val);
            }
        }
        None
    }
    /// As [`LookupGroup::lookup`], but returns a mutable reference.
    pub fn lookup_mut(&mut self, var: &str) -> Option<&mut Value> {
        for src in self.0.iter_mut().rev() {
            if let Some(val) = src.0.get_mut(var) {
                return Some(val);
            }
        }
        None
    }
    /// Performs a lookup for the given variable.
    /// If it already exists, assigns it a new value.
    /// Otherwise, defines it in the last (most-local) context.
    pub fn set_or_define(&mut self, var: &str, value: Value) {
        match self.lookup_mut(var) {
            Some(x) => *x = value,
            None => self.0.last_mut().unwrap().set_or_define(var, value),
        }
    }
}
