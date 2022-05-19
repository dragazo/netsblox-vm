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
#[derive(Clone, Copy)]
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
pub enum RefValue {
    String(String),
    List(Vec<Value>),
}
/// Any primitive type.
/// 
/// Values are always copyable, which is how new references are created.
/// [`CopyValue`] variables receive a direct copy, while [`RefValue`] variables simply copy the reference.
#[derive(Clone, Copy)]
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
            ast::Value::String(x) => {
                if ref_pool.intern {
                    for (k, v) in ref_pool.pool.iter() {
                        match v {
                            RefValue::String(s) if s == x => return Value::RefValue(k),
                            _ => (),
                        }
                    }
                }
                Value::RefValue(ref_pool.pool.insert(RefValue::String(x.clone())))
            }
            ast::Value::List(x) => {
                let values = x.iter().map(|x| Value::from_ast(x, ref_pool)).collect();
                Value::RefValue(ref_pool.pool.insert(RefValue::List(values)))
            }
        }
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
}

#[derive(Default)]
pub struct SymbolTable(BTreeMap<String, Value>);
impl SymbolTable {
    pub fn set_or_define(&mut self, var: &str, value: Value) {
        match self.0.get_mut(var) {
            Some(x) => *x = value,
            None => { self.0.insert(var.to_owned(), value); }
        }
    }
}

pub struct LookupGroup<'a, 'b>(pub &'a mut [&'b mut SymbolTable]);
impl<'a, 'b> LookupGroup<'a, 'b> {
    pub fn new(tabs: &'a mut [&'b mut SymbolTable]) -> Self {
        assert!(!tabs.is_empty());
        Self(tabs)
    }
    pub fn lookup(&self, var: &str) -> Option<&Value> {
        for src in self.0.iter() {
            if let Some(val) = src.0.get(var) {
                return Some(val);
            }
        }
        None
    }
    pub fn lookup_mut(&mut self, var: &str) -> Option<&mut Value> {
        for src in self.0.iter_mut() {
            if let Some(val) = src.0.get_mut(var) {
                return Some(val);
            }
        }
        None
    }
    pub(crate) fn set_or_define_last_context(&mut self, var: &str, value: Value) {
        self.0.last_mut().unwrap().set_or_define(var, value)
    }
}
