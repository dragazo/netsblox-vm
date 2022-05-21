//! Common types used for execution.

use std::prelude::v1::*;
use std::collections::BTreeMap;
use std::cell::RefCell;
use std::rc::{Rc, Weak};

use netsblox_ast as ast;
use slotmap::SlotMap;

slotmap::new_key_type! {
    pub struct RefPoolListKey;
}

/// The type of a variable.
#[derive(Clone, Copy, Debug)]
pub enum Type {
    Bool,
    Number,
    String,
    List,
}

/// A type conversion error.
pub struct ConversionError {
    pub got: Type,
    pub expected: Type,
}

/// Any primitive type.
#[derive(Clone, Debug)]
pub enum Value {
    Bool(bool),
    Number(f64),
    String(Rc<String>),
    List(Weak<RefCell<Vec<Value>>>),
}
impl Value {
    /// Creates a new value from an abstract syntax tree value.
    /// In the event that `value` is a reference type, it is allocated in the provided [`RefPool`].
    pub fn from_ast(value: &ast::Value, ref_pool: &mut RefPool) -> Self {
        match value {
            ast::Value::Bool(x) => Value::Bool(*x),
            ast::Value::Number(x) => Value::Number(*x),
            ast::Value::Constant(ast::Constant::E) => Value::Number(std::f64::consts::E),
            ast::Value::Constant(ast::Constant::Pi) => Value::Number(std::f64::consts::PI),
            ast::Value::String(x) => Self::from_string(x.clone(), ref_pool),
            ast::Value::List(x) => Self::from_vec(x.iter().map(|x| Value::from_ast(x, ref_pool)).collect(), ref_pool),
        }
    }
    /// Creates a new [`Value::List`] object with the given values.
    pub fn from_vec(values: Vec<Value>, ref_pool: &mut RefPool) -> Self {
        let rc = Rc::new(RefCell::new(values));
        let weak = Rc::downgrade(&rc);
        ref_pool.list_pool.push(rc);
        Value::List(weak)
    }
    /// Creates a new [`Value::String`] object with the given value.
    pub fn from_string(value: String, ref_pool: &mut RefPool) -> Self {
        if ref_pool.intern {
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
    /// Gets the type of value that is stored.
    pub fn get_type(&self) -> Type {
        match self {
            Value::Bool(_) => Type::Bool,
            Value::Number(_) => Type::Number,
            Value::String(_) => Type::String,
            Value::List(_) => Type::List,
        }
    }
    /// Attempts to interpret this value as a number.
    pub fn to_number(&self) -> Result<f64, ConversionError> {
        Ok(match self {
            Value::Bool(_) => return Err(ConversionError { got: Type::Bool, expected: Type::Number }),
            Value::List(_) => return Err(ConversionError { got: Type::List, expected: Type::Number }),
            Value::String(x) => match x.parse() {
                Err(_) => return Err(ConversionError { got: Type::String, expected: Type::Number }),
                Ok(x) => x,
            }
            Value::Number(x) => *x,
        })
    }
    /// Attempts to interpret this value as a bool.
    pub fn to_bool(&self) -> Result<bool, ConversionError> {
        Ok(match self {
            Value::Bool(x) => *x,
            Value::Number(x) => *x != 0.0 && !x.is_nan(),
            Value::List(_) => return Err(ConversionError { got: Type::List, expected: Type::Bool }),
            Value::String(x) => !x.is_empty(),
        })
    }
}
impl From<bool> for Value {
    fn from(val: bool) -> Self {
        Self::Bool(val)
    }
}
impl From<f64> for Value {
    fn from(val: f64) -> Self {
        Self::Number(val)
    }
}

pub struct RefPool {
    string_pool: Vec<Weak<String>>,
    list_pool: Vec<Rc<RefCell<Vec<Value>>>>,
    intern: bool,
}
impl RefPool {
    pub fn new(intern: bool) -> Self {
        Self {
            string_pool: Default::default(),
            list_pool: Default::default(),
            intern,
        }
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
    pub fn lookup(&self, var: &str) -> Option<&Value> {
        for src in self.0.iter().rev() {
            if let Some(val) = src.0.get(var) {
                return Some(val);
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
