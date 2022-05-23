//! Utilities for executing generated [`ByteCode`](crate::bytecode::ByteCode).

use std::prelude::v1::*;
use std::collections::BTreeMap;
use std::cell::RefCell;
use std::rc::Rc;
use std::iter;

use crate::bytecode::*;
use crate::runtime::*;

struct RcUpgradeError;

/// An execution error from a [`Process`] (see [`Process::step`]).
/// 
/// Each error variant contains a field called `pos` which is the [`ByteCode`] index at the time of the error.
/// By using the [`Locations`] information from [`ByteCode::compile`], it is possible to determine which
/// script/function generated the error.
#[derive(Debug)]
pub enum ExecError {
    /// A variable lookup operation failed.
    /// `name` holds the name of the variable that was expected.
    UndefinedVariable { name: String, pos: usize },
    /// An upgrade operation on a [`Weak`](std::rc::Weak) handle failed.
    /// Proper usage of this crate should never generate this error.
    /// The most likely cause is that a [`RefPool`] instance was improperly used.
    RcUpgradeError { pos: usize },
    /// The result of a failed type conversion.
    ConversionError { got: Type, expected: Type, pos: usize },
    /// Exceeded the maximum call depth.
    /// This can be configured by [`Process::new`].
    CallDepthLimit { limit: usize, pos: usize },
}

trait ErrAt {
    fn err_at(self, pos: usize) -> ExecError;
}
impl ErrAt for ConversionError {
    fn err_at(self, pos: usize) -> ExecError {
        ExecError::ConversionError { got: self.got, expected: self.expected, pos }
    }
}
impl ErrAt for RcUpgradeError {
    fn err_at(self, pos: usize) -> ExecError {
        ExecError::RcUpgradeError { pos }
    }
}
impl ErrAt for ArithmeticError {
    fn err_at(self, pos: usize) -> ExecError {
        match self {
            ArithmeticError::ConversionError(e) => e.err_at(pos),
            ArithmeticError::RcUpgradeError => RcUpgradeError.err_at(pos),
        }
    }
}

enum ArithmeticError {
    ConversionError(ConversionError),
    RcUpgradeError,
}
impl From<ConversionError> for ArithmeticError {
    fn from(e: ConversionError) -> Self {
        Self::ConversionError(e)
    }
}
impl From<RcUpgradeError> for ArithmeticError {
    fn from(_: RcUpgradeError) -> Self {
        Self::RcUpgradeError
    }
}

/// Result of stepping through a [`Process`].
pub enum StepType {
    /// The process was not running.
    Idle,
    /// The process executed an instruction successfully and does not need to yield.
    Normal,
    /// The process has signaled a yield point so that other code can run.
    /// Many yield results may occur back-to-back, such as while awaiting an asynchronous result.
    /// 
    /// Yielding is primarily needed for executing an entire semi-concurrent project so that scripts can appear to run simultaneously.
    /// If instead you are explicitly only using a single sandboxed process, this can be treated equivalently to [`StepType::Normal`].
    Yield,
    /// The process has successfully terminated with the given return value, or `None` if terminated by an (error-less) abort
    Terminate(Option<Value>),
}

/// A [`ByteCode`] execution primitive.
/// 
/// A `Process` is a self-contained thread of execution; it maintains its own state machine for executing instructions step by step.
/// Global variables, entity fields, and several external features are hosted separately and passed into [`Process::step`].
pub struct Process {
    code: Rc<ByteCode>,
    pos: usize,
    running: bool,
    max_call_depth: usize,
    call_stack: Vec<(usize, SymbolTable)>, // tuples of (ret pos, locals)
    value_stack: Vec<Value>,
}
impl Process {
    /// Creates a new process with the given code.
    /// The new process is initially idle; [`Process::initialize`] can be used to begin execution at a specific location (see [`Locations`]).
    pub fn new(code: Rc<ByteCode>, max_call_depth: usize) -> Self {
        Self {
            code,
            pos: 0,
            running: false,
            max_call_depth,
            call_stack: vec![],
            value_stack: vec![],
        }
    }
    /// Checks if the process is currently running.
    /// Note that the process will not run on its own (see [`Process::step`]).
    pub fn is_running(&self) -> bool {
        self.running
    }
    /// Gets a reference to the [`ByteCode`] object that the process was built from.
    pub fn get_code(&self) -> &Rc<ByteCode> {
        &self.code
    }
    /// Prepares the process to execute code at the given [`ByteCode`] position
    /// and with the given context of local variables.
    /// Any previous process state is wiped when performing this action.
    pub fn initialize(&mut self, start_pos: usize, context: SymbolTable) {
        self.pos = start_pos;
        self.running = true;
        self.call_stack.clear();
        self.call_stack.push((usize::MAX, context));
        self.value_stack.clear();
    }
    /// Executes a single instruction with the given execution context.
    /// The return value can be used to determine what additional effects the script has requested,
    /// as well as retrieving the return value or execution error in the event that the process terminates.
    /// 
    /// The process transitions to the idle state (see [`Process::is_running`]) upon failing with `Err` or
    /// succeeding with [`StepType::Terminate`].
    pub fn step(&mut self, ref_pool: &mut RefPool, globals: &mut SymbolTable, fields: &mut SymbolTable) -> Result<StepType, ExecError> {
        let res = self.step_impl(ref_pool, globals, fields);
        if let Ok(StepType::Terminate(_)) | Err(_) = res {
            self.running = false;
        }
        res
    }
    fn step_impl(&mut self, ref_pool: &mut RefPool, globals: &mut SymbolTable, fields: &mut SymbolTable) -> Result<StepType, ExecError> {
        if !self.running { return Ok(StepType::Idle); }
        let (_, locals) = self.call_stack.last_mut().unwrap();
        let mut context = [globals, fields, locals];
        let mut context = LookupGroup::new(&mut context);

        macro_rules! lookup_var {
            ($var:expr) => {{
                let var = $var;
                match context.lookup(var) {
                    Some(x) => x,
                    None => return Err(ExecError::UndefinedVariable { name: var.into(), pos: self.pos }),
                }
            }}
        }

        match &self.code.0[self.pos] {
            Instruction::Illegal => panic!(),

            Instruction::Yield => {
                self.pos += 1;
                return Ok(StepType::Yield);
            }

            Instruction::PushValue { value } => {
                self.value_stack.push(Value::from_ast(value, ref_pool, true));
                self.pos += 1;
            }
            Instruction::PushVariable { var } => {
                self.value_stack.push(lookup_var!(var).clone());
                self.pos += 1;
            }
            Instruction::DupeValue { top_index } => {
                let val = self.value_stack[self.value_stack.len() - 1 - top_index].clone();
                self.value_stack.push(val);
                self.pos += 1;
            }
            Instruction::SwapValues { top_index_1, top_index_2 } => {
                let len = self.value_stack.len();
                self.value_stack.swap(len - 1 - top_index_1, len - 1 - top_index_2);
                self.pos += 1;
            }
            Instruction::PopValues { count } => {
                let len = self.value_stack.len();
                self.value_stack.drain(len - count..);
                debug_assert_eq!(self.value_stack.len(), len - count);
                self.pos += 1;
            }

            Instruction::MakeList { len } => {
                let mut vals = Vec::with_capacity(*len);
                for _ in 0..*len {
                    vals.push(self.value_stack.pop().unwrap());
                }
                vals.reverse();
                self.value_stack.push(Value::from_vec(vals, ref_pool));
                self.pos += 1;
            }
            Instruction::MakeListRange => {
                let b = self.value_stack.pop().unwrap().to_number().map_err(|e| e.err_at(self.pos))?;
                let mut a = self.value_stack.pop().unwrap().to_number().map_err(|e| e.err_at(self.pos))?;

                let mut res = vec![];
                if a.is_finite() && b.is_finite() {
                    if a <= b {
                        while a <= b {
                            res.push(a.into());
                            a += 1.0;
                        }
                    } else {
                        while a >= b {
                            res.push(a.into());
                            a -= 1.0;
                        }
                    }
                }

                self.value_stack.push(Value::from_vec(res, ref_pool));
                self.pos += 1;
            }
            Instruction::ListPush => {
                let val = self.value_stack.pop().unwrap();
                let list = self.value_stack.pop().unwrap();
                match list {
                    Value::List(x) => match x.upgrade() {
                        Some(x) => x.borrow_mut().push(val),
                        None => return Err(RcUpgradeError.err_at(self.pos)),
                    }
                    x => return Err(ConversionError { got: x.get_type(), expected: Type::List }.err_at(self.pos)),
                }
                self.pos += 1;
            }

            Instruction::BinaryOp { op } => {
                let b = self.value_stack.pop().unwrap();
                let a = self.value_stack.pop().unwrap();
                self.value_stack.push(ops::binary_op(&a, &b, ref_pool, *op).map_err(|e| e.err_at(self.pos))?);
                self.pos += 1;
            }
            Instruction::UnaryOp { op } => {
                let x = self.value_stack.pop().unwrap();
                self.value_stack.push(ops::unary_op(&x, ref_pool, *op).map_err(|e| e.err_at(self.pos))?);
                self.pos += 1;
            }

            Instruction::Assign { vars } => {
                let value = self.value_stack.pop().unwrap();
                for var in vars {
                    context.set_or_define(var, value.clone());
                }
                self.pos += 1;
            }
            Instruction::BinaryOpAssign { var, op } => {
                let b = self.value_stack.pop().unwrap();
                let a = lookup_var!(var).clone();
                context.set_or_define(var, ops::binary_op(&a, &b, ref_pool, *op).map_err(|e| e.err_at(self.pos))?);
                self.pos += 1;
            }

            Instruction::Jump { to } => self.pos = *to,
            Instruction::ConditionalJump { to, when } => {
                let value = self.value_stack.pop().unwrap();
                self.pos = if value.to_bool().map_err(|e| e.err_at(self.pos))? == *when { *to } else { self.pos + 1 };
            }

            Instruction::Call { pos, params } => {
                if self.call_stack.len() >= self.max_call_depth {
                    return Err(ExecError::CallDepthLimit { limit: self.max_call_depth, pos: self.pos });
                }

                let mut context = SymbolTable::default();
                for var in params.iter().rev() {
                    context.set_or_define(var, self.value_stack.pop().unwrap());
                }
                self.call_stack.push((self.pos + 1, context));
                self.pos = *pos;
            }
            Instruction::Return => {
                let (pos, _) = self.call_stack.pop().unwrap();
                if self.call_stack.is_empty() {
                    debug_assert_eq!(self.value_stack.len(), 1);
                    debug_assert_eq!(pos, usize::MAX);
                    return Ok(StepType::Terminate(Some(self.value_stack.pop().unwrap())));
                } else {
                    self.pos = pos;
                }
            }
        }

        Ok(StepType::Normal)
    }
}

mod ops {
    use super::*;

    fn as_list(v: &Value) -> Result<Option<Rc<RefCell<Vec<Value>>>>, RcUpgradeError> {
        Ok(match v {
            Value::List(v) => match v.upgrade() {
                Some(rc) => Some(rc),
                None => return Err(RcUpgradeError),
            }
            _ => None,
        })
    }
    fn as_matrix(v: &Value) -> Result<Option<Rc<RefCell<Vec<Value>>>>, RcUpgradeError> {
        Ok(match as_list(v)? {
            Some(vals) => {
                let good = match vals.borrow().as_slice() {
                    [] => false,
                    [first, ..] => as_list(first)?.is_some(),
                };
                if good { Some(vals) } else { None }
            }
            None => None,
        })
    }

    const DEG_TO_RAD: f64 = std::f64::consts::PI / 180.0;

    fn binary_op_impl(a: &Value, b: &Value, matrix_mode: bool, cache: &mut BTreeMap<(*const (), *const (), bool), Value>, ref_pool: &mut RefPool, scalar_op: fn(&Value, &Value, &mut RefPool) -> Result<Value, ArithmeticError>) -> Result<Value, ArithmeticError> {
        let cache_key = (a.alloc_ptr(), b.alloc_ptr(), matrix_mode);
        Ok(match cache.get(&cache_key) {
            Some(x) => x.clone(),
            None => {
                let checker = if matrix_mode { as_matrix } else { as_list };
                match (checker(a)?, checker(b)?) {
                    (Some(a), Some(b)) => {
                        let (a, b) = (a.borrow(), b.borrow());
                        let real_res = Value::from_vec(Vec::with_capacity(a.len().min(b.len())), ref_pool);
                        cache.insert(cache_key, real_res.clone());
                        let res = as_list(&real_res)?.unwrap();
                        let mut res = res.borrow_mut();
                        for (a, b) in iter::zip(&*a, &*b) {
                            res.push(binary_op_impl(a, b, matrix_mode, cache, ref_pool, scalar_op)?);
                        }
                        real_res
                    }
                    (Some(a), None) => {
                        let a = a.borrow();
                        let real_res = Value::from_vec(Vec::with_capacity(a.len()), ref_pool);
                        cache.insert(cache_key, real_res.clone());
                        let res = as_list(&real_res)?.unwrap();
                        let mut res = res.borrow_mut();
                        for a in &*a {
                            res.push(binary_op_impl(a, b, matrix_mode, cache, ref_pool, scalar_op)?);
                        }
                        real_res
                    }
                    (None, Some(b)) => {
                        let b = b.borrow();
                        let real_res = Value::from_vec(Vec::with_capacity(b.len()), ref_pool);
                        cache.insert(cache_key, real_res.clone());
                        let res = as_list(&real_res)?.unwrap();
                        let mut res = res.borrow_mut();
                        for b in &*b {
                            res.push(binary_op_impl(a, b, matrix_mode, cache, ref_pool, scalar_op)?);
                        }
                        real_res
                    }
                    (None, None) => if matrix_mode { binary_op_impl(a, b, false, cache, ref_pool, scalar_op)? } else { scalar_op(a, b, ref_pool)? }
                }
            }
        })
    }
    pub(super) fn binary_op(a: &Value, b: &Value, ref_pool: &mut RefPool, op: BinaryOp) -> Result<Value, ArithmeticError> {
        match op {
            BinaryOp::Add     => binary_op_impl(a, b, true, &mut Default::default(), ref_pool, |a, b, _| Ok((a.to_number()? + b.to_number()?).into())),
            BinaryOp::Sub     => binary_op_impl(a, b, true, &mut Default::default(), ref_pool, |a, b, _| Ok((a.to_number()? - b.to_number()?).into())),
            BinaryOp::Mul     => binary_op_impl(a, b, true, &mut Default::default(), ref_pool, |a, b, _| Ok((a.to_number()? * b.to_number()?).into())),
            BinaryOp::Div     => binary_op_impl(a, b, true, &mut Default::default(), ref_pool, |a, b, _| Ok((a.to_number()? / b.to_number()?).into())),
            BinaryOp::Pow     => binary_op_impl(a, b, true, &mut Default::default(), ref_pool, |a, b, _| Ok(libm::pow(a.to_number()?, b.to_number()?).into())),
            BinaryOp::Greater => binary_op_impl(a, b, true, &mut Default::default(), ref_pool, |a, b, _| Ok((a.to_number()? > b.to_number()?).into())),
            BinaryOp::Less    => binary_op_impl(a, b, true, &mut Default::default(), ref_pool, |a, b, _| Ok((a.to_number()? < b.to_number()?).into())),
        }
    }

    fn unary_op_impl(x: &Value, cache: &mut BTreeMap<*const (), Value>, ref_pool: &mut RefPool, scalar_op: fn(&Value, &mut RefPool) -> Result<Value, ArithmeticError>) -> Result<Value, ArithmeticError> {
        let cache_key = x.alloc_ptr();
        Ok(match cache.get(&cache_key) {
            Some(x) => x.clone(),
            None => match as_list(x)? {
                Some(x) => {
                    let x = x.borrow();
                    let real_res = Value::from_vec(Vec::with_capacity(x.len()), ref_pool);
                    cache.insert(cache_key, real_res.clone());
                    let res = as_list(&real_res)?.unwrap();
                    let mut res = res.borrow_mut();
                    for x in &*x {
                        res.push(unary_op_impl(x, cache, ref_pool, scalar_op)?);
                    }
                    real_res
                }
                None => scalar_op(x, ref_pool)?,
            }
        })
    }
    pub(super) fn unary_op(x: &Value, ref_pool: &mut RefPool, op: UnaryOp) -> Result<Value, ArithmeticError> {
        match op {
            UnaryOp::Abs => unary_op_impl(x, &mut Default::default(), ref_pool, |x, _| Ok(libm::fabs(x.to_number()?).into())),
            UnaryOp::Neg => unary_op_impl(x, &mut Default::default(), ref_pool, |x, _| Ok((-x.to_number()?).into())),
            UnaryOp::Sin => unary_op_impl(x, &mut Default::default(), ref_pool, |x, _| Ok(libm::sin(x.to_number()? * DEG_TO_RAD).into())),
            UnaryOp::Cos => unary_op_impl(x, &mut Default::default(), ref_pool, |x, _| Ok(libm::cos(x.to_number()? * DEG_TO_RAD).into())),
            UnaryOp::Tan => unary_op_impl(x, &mut Default::default(), ref_pool, |x, _| Ok(libm::tan(x.to_number()? * DEG_TO_RAD).into())),
        }
    }
}
