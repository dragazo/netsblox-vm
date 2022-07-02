//! [`ByteCode`] execution utilities.
//! 
//! Because the NetsBlox runtime allows for the creation of cycles, all program-accessible objects must be garbage collected.
//! To do this, we use the `gc-arena` crate, which allows a simple and correct mechanism for provably disjoint garbage collected runtime environments.
//! However, `gc-arena` makes this guarantee by forbidding garbage collected objects from leaving the arena.
//! Thus, many types in this module, such as  [`Value`] and [`Process`], are branded with an invariant `'gc` lifetime and can only be access by callback.
//! Some utilities are provided to export these values from the runtime environment if needed.

use std::prelude::v1::*;
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;
use std::iter;

use derive_builder::Builder;

use crate::gc::*;
use crate::json::*;
use crate::runtime::*;
use crate::bytecode::*;

/// An execution error from a [`Process`] (see [`Process::step`]).
/// 
/// This consists of an [`ErrorCause`] value describing the cause, as well as the bytecode location of the error.
/// By using the [`Locations`] information from [`ByteCode::compile`], it is possible to determine which script/function generated the error.
#[derive(Debug)]
pub struct ExecError {
    pub cause: ErrorCause,
    pub pos: usize,
}
/// The cause/explanation of an [`ExecError`].
#[derive(Debug)]
pub enum ErrorCause {
    /// A variable lookup operation failed. `name` holds the name of the variable that was expected.
    UndefinedVariable { name: String },
    /// The result of a failed type conversion.
    ConversionError { got: Type, expected: Type },
    /// Attempt to index a list with a non-integer numeric value, `index`.
    IndexNotInteger { index: f64 },
    /// An indexing operation on a list had an out of bounds index, `index`, on a list of size `list_len`. Note that Snap!/NetsBlox use 1-based indexing.
    IndexOutOfBounds { index: f64, list_len: usize },
    /// Exceeded the maximum call depth. This can be configured by [`Process::new`].
    CallDepthLimit { limit: usize },
    /// Attempt to call a closure which required `expected` arguments, but `got` arguments were supplied.
    ClosureArgCount { expected: usize, got: usize },
    /// An operation resulted in an error generated by the [`System`].
    SystemError { error: SystemError },
    /// Attempt to parse an invalid JSON-encoded string.
    NotJson { value: String },
    /// Attempt to parse a JSON-encoded string that contained a null value.
    JsonHadNull { value: String },
    /// Attempt to parse a JSON-encoded string that contained an number that could not be encoded as [`f64`].
    JsonHadBadNumber { value: String },
    /// Attempt to interpret an invalid unicode code point (number) as a character.
    InvalidUnicode { value: f64 },
}
impl From<ConversionError> for ErrorCause { fn from(e: ConversionError) -> Self { Self::ConversionError { got: e.got, expected: e.expected } } }
impl From<SystemError> for ErrorCause { fn from(error: SystemError) -> Self { Self::SystemError { error } } }

/// Result of stepping through a [`Process`].
pub enum ProcessStep<'gc> {
    /// The process was not running.
    Idle,
    /// The process executed an instruction successfully and does not need to yield.
    Normal,
    /// The process has signaled a yield point so that other code can run.
    /// Many yield results may occur back-to-back, such as while awaiting an asynchronous result.
    /// 
    /// Yielding is needed for executing an entire project's scripts so that they can appear to run simultaneously.
    /// If instead you are explicitly only using a single sandboxed process, this can be treated equivalently to [`ProcessStep::Normal`].
    Yield,
    /// The process has successfully terminated with the given return value, or [`None`] if terminated by an (error-less) abort,
    /// such as a stop script command or the death of the process's associated entity.
    Terminate { result: Option<Value<'gc>> },
    /// The process has requested to broadcast a message to all entities, which may trigger other code to execute.
    Broadcast { msg_type: Gc<'gc, String>, barrier: Option<Barrier> },
}

/// Settings to use for a [`Process`].
#[derive(Builder, Clone, Copy, Collect)]
#[builder(no_std)]
#[collect(require_static)]
pub struct Settings {
    /// The maximum depth of the call stack (default `1024`).
    #[builder(default = "1024")]
    max_call_depth: usize,
}

#[derive(Collect)]
#[collect(require_static)]
struct ReturnPoint {
    pos: usize,
    warp_counter: usize,
    value_stack_size: usize,
}

#[derive(Collect)]
#[collect(require_static)]
enum Defer<S: System> {
    Async { key: S::AsyncKey, aft_pos: usize },
    Barrier { condition: BarrierCondition, aft_pos: usize },
}

/// A [`ByteCode`] execution primitive.
/// 
/// A [`Process`] is a self-contained thread of execution.
/// It maintains its own state machine for executing instructions step by step.
#[derive(Collect)]
#[collect(no_drop)]
pub struct Process<'gc, S: System> {
    code: Rc<ByteCode>,
    start_pos: usize,
    global_context: GcCell<'gc, GlobalContext<'gc>>,
    entity: GcCell<'gc, Entity<'gc>>,
    settings: Settings,
    pos: usize,
    running: bool,
    barrier: Option<Barrier>,
    warp_counter: usize,
    call_stack: Vec<(ReturnPoint, SymbolTable<'gc>)>, // tuples of (ret pos, locals)
    value_stack: Vec<Value<'gc>>,
    defer: Option<Defer<S>>,
}
impl<'gc, S: System> Process<'gc, S> {
    /// Creates a new [`Process`] that is tied to a given `start_pos` (entry point) in the [`ByteCode`] and associated with the specified `entity`.
    /// The created process is initialized to an idle (non-running) state; use [`Process::initialize`] to begin execution.
    pub fn new(code: Rc<ByteCode>, start_pos: usize, global_context: GcCell<'gc, GlobalContext<'gc>>, entity: GcCell<'gc, Entity<'gc>>, settings: Settings) -> Self {
        Self {
            code, start_pos, global_context, entity, settings,
            running: false,
            barrier: None,
            pos: 0,
            warp_counter: 0,
            call_stack: vec![],
            value_stack: vec![],
            defer: None,
        }
    }
    /// Checks if the process is currently running.
    /// Note that the process will not run on its own (see [`Process::step`]).
    pub fn is_running(&self) -> bool {
        self.running
    }
    /// Prepares the process to execute starting at the main entry point (see [`Process::new`]) with the provided input local variables.
    /// A [`Barrier`] may also be set, which will be destroyed upon termination, either due to completion or an error.
    /// 
    /// Any previous process state is wiped when performing this action.
    pub fn initialize(&mut self, locals: SymbolTable<'gc>, barrier: Option<Barrier>) {
        self.pos = self.start_pos;
        self.running = true;
        self.barrier = barrier;
        self.warp_counter = 0;
        self.call_stack.clear();
        self.call_stack.push((ReturnPoint { pos: usize::MAX, warp_counter: 0, value_stack_size: 0 }, locals));
        self.value_stack.clear();
        self.defer = None;
    }
    /// Executes a single bytecode instruction.
    /// The return value can be used to determine what additional effects the script has requested,
    /// as well as to retrieve the return value or execution error in the event that the process terminates.
    /// 
    /// The process transitions to the idle state (see [`Process::is_running`]) upon failing with [`Err`] or succeeding with [`ProcessStep::Terminate`].
    pub fn step(&mut self, mc: MutationContext<'gc, '_>, system: &mut S) -> Result<ProcessStep<'gc>, ExecError> {
        let res = self.step_impl(mc, system);
        if let Ok(ProcessStep::Terminate { .. }) | Err(_) = res {
            self.running = false;
            self.barrier = None;
        }
        res.map_err(|cause| ExecError { cause, pos: self.pos })
    }
    fn step_impl(&mut self, mc: MutationContext<'gc, '_>, system: &mut S) -> Result<ProcessStep<'gc>, ErrorCause> {
        match &self.defer {
            None => (),
            Some(Defer::Async { key, aft_pos }) => match system.poll_async(mc, key)? {
                AsyncPoll::Completed(x) => {
                    self.value_stack.push(x);
                    self.pos = *aft_pos;
                    self.defer = None;
                }
                AsyncPoll::Pending => return Ok(ProcessStep::Yield),
            }
            Some(Defer::Barrier { condition, aft_pos }) => match condition.is_completed() {
                true => {
                    self.pos = *aft_pos;
                    self.defer = None;
                }
                false => return Ok(ProcessStep::Yield),
            }
        }

        let mut entity = self.entity.write(mc);
        if !entity.alive { return Ok(ProcessStep::Terminate { result: None }) }

        let mut global_context = self.global_context.write(mc);
        let mut context = [&mut global_context.globals, &mut entity.fields, &mut self.call_stack.last_mut().unwrap().1];
        let mut context = LookupGroup::new(&mut context);

        macro_rules! lookup_var {
            ($var:expr => $m:ident) => {{
                let var = $var;
                match context.$m(var) {
                    Some(x) => x,
                    None => return Err(ErrorCause::UndefinedVariable { name: var.into() }),
                }
            }};
            ($var:expr) => {lookup_var!($var => lookup)};
            (mut $var:expr) => {lookup_var!($var => lookup_mut)};
        }

        match &self.code.0[self.pos] {
            Instruction::Illegal => panic!(),

            Instruction::Yield => {
                self.pos += 1;
                if self.warp_counter == 0 { return Ok(ProcessStep::Yield) }
            }
            Instruction::WarpStart => {
                self.warp_counter += 1;
                self.pos += 1;
            }
            Instruction::WarpStop => {
                self.warp_counter -= 1;
                self.pos += 1;
            }

            Instruction::PushValue { value } => {
                self.value_stack.push(Value::from_ast(mc, value));
                self.pos += 1;
            }
            Instruction::PushVariable { var } => {
                self.value_stack.push(lookup_var!(var).get());
                self.pos += 1;
            }
            Instruction::DupeValue { top_index } => {
                let val = self.value_stack[self.value_stack.len() - 1 - top_index];
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

            Instruction::ShallowCopy => {
                let val = self.value_stack.pop().unwrap();
                self.value_stack.push(val.shallow_copy(mc));
                self.pos += 1;
            }

            Instruction::MakeList { len } => {
                let mut vals = Vec::with_capacity(*len);
                for _ in 0..*len {
                    vals.push(self.value_stack.pop().unwrap());
                }
                vals.reverse();
                self.value_stack.push(GcCell::allocate(mc, vals).into());
                self.pos += 1;
            }
            Instruction::ListLen => {
                let list = self.value_stack.pop().unwrap().to_list(mc)?;
                self.value_stack.push((list.read().len() as f64).into());
                self.pos += 1;
            }
            Instruction::ListIndex => {
                let index = self.value_stack.pop().unwrap();
                let list = self.value_stack.pop().unwrap();
                self.value_stack.push(ops::index_list(mc, &list, &index)?);
                self.pos += 1;
            }
            Instruction::ListLastIndex => {
                let list = self.value_stack.pop().unwrap().to_list(mc)?;
                self.value_stack.push(match list.read().last() {
                    Some(x) => *x,
                    None => return Err(ErrorCause::IndexOutOfBounds { index: 0.0, list_len: 0 }),
                });
                self.pos += 1;
            }
            Instruction::MakeListRange => {
                let b = self.value_stack.pop().unwrap().to_number()?;
                let mut a = self.value_stack.pop().unwrap().to_number()?;

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

                self.value_stack.push(GcCell::allocate(mc, res).into());
                self.pos += 1;
            }
            Instruction::ListPush => {
                let val = self.value_stack.pop().unwrap();
                let list = self.value_stack.pop().unwrap().to_list(mc)?;
                list.write(mc).push(val);
                self.pos += 1;
            }
            Instruction::ListIndexAssign => {
                let value = self.value_stack.pop().unwrap();
                let index = self.value_stack.pop().unwrap();
                let list = self.value_stack.pop().unwrap().to_list(mc)?;
                let mut list = list.write(mc);
                let index = ops::prep_list_index(&index, list.len())?;
                list[index] = value;
                self.pos += 1;
            }

            Instruction::Strcat { args } => {
                let mut values = Vec::with_capacity(*args);
                for _ in 0..*args {
                    values.push(self.value_stack.pop().unwrap());
                }
                let mut res = String::new();
                for value in values.iter().rev() {
                    res += value.to_string(mc)?.as_str();
                }
                self.value_stack.push(Gc::allocate(mc, res).into());
                self.pos += 1;
            }

            Instruction::BinaryOp { op } => {
                let b = self.value_stack.pop().unwrap();
                let a = self.value_stack.pop().unwrap();
                self.value_stack.push(ops::binary_op(mc, &a, &b, *op)?);
                self.pos += 1;
            }
            Instruction::Eq => {
                let b = self.value_stack.pop().unwrap();
                let a = self.value_stack.pop().unwrap();
                self.value_stack.push(ops::check_eq(&a, &b).into());
                self.pos += 1;
            }
            Instruction::UnaryOp { op } => {
                let x = self.value_stack.pop().unwrap();
                self.value_stack.push(ops::unary_op(mc, &x, *op)?);
                self.pos += 1;
            }

            Instruction::DeclareLocals { vars } => {
                let locals = context.locals_mut();
                for var in vars {
                    locals.redefine_or_define(var, Shared::Unique(0.0.into()));
                }
                self.pos += 1;
            }
            Instruction::Assign { var } => {
                let value = self.value_stack.pop().unwrap();
                context.set_or_define(mc, var, value);
                self.pos += 1;
            }
            Instruction::BinaryOpAssign { var, op } => {
                let b = self.value_stack.pop().unwrap();
                let a = lookup_var!(var).get();
                context.set_or_define(mc, var, ops::binary_op(mc, &a, &b, *op)?);
                self.pos += 1;
            }

            Instruction::Jump { to } => self.pos = *to,
            Instruction::ConditionalJump { to, when } => {
                let value = self.value_stack.pop().unwrap();
                self.pos = if value.to_bool()? == *when { *to } else { self.pos + 1 };
            }

            Instruction::Call { pos, params } => {
                if self.call_stack.len() >= self.settings.max_call_depth {
                    return Err(ErrorCause::CallDepthLimit { limit: self.settings.max_call_depth });
                }

                let mut locals = SymbolTable::default();
                for var in params.iter().rev() {
                    locals.redefine_or_define(var, self.value_stack.pop().unwrap().into());
                }
                self.call_stack.push((ReturnPoint { pos: self.pos + 1, warp_counter: self.warp_counter, value_stack_size: self.value_stack.len() }, locals));
                self.pos = *pos;
            }
            Instruction::MakeClosure { pos, params, captures } => {
                let mut caps = SymbolTable::default();
                for var in captures {
                    caps.redefine_or_define(var, lookup_var!(mut var).alias(mc));
                }
                self.value_stack.push(GcCell::allocate(mc, Closure { pos: *pos, params: params.clone(), captures: caps }).into());
                self.pos += 1;
            }
            Instruction::CallClosure { args } => {
                let closure = self.value_stack.pop().unwrap().to_closure(mc)?;
                let mut closure = closure.write(mc);
                if closure.params.len() != *args {
                    return Err(ErrorCause::ClosureArgCount { expected: closure.params.len(), got: *args });
                }

                let mut locals = SymbolTable::default();
                for (k, v) in closure.captures.iter_mut() {
                    locals.redefine_or_define(k, v.alias(mc));
                }
                for var in closure.params.iter().rev() {
                    locals.redefine_or_define(var, self.value_stack.pop().unwrap().into());
                }
                self.call_stack.push((ReturnPoint { pos: self.pos + 1, warp_counter: self.warp_counter, value_stack_size: self.value_stack.len() }, locals));
                self.pos = closure.pos;
            }
            Instruction::Return => {
                let (return_point, _) = self.call_stack.pop().unwrap();
                let return_value = self.value_stack.pop().unwrap();
                self.value_stack.drain(return_point.value_stack_size..);
                debug_assert_eq!(self.value_stack.len(), return_point.value_stack_size);
                self.value_stack.push(return_value);

                if self.call_stack.is_empty() {
                    debug_assert_eq!(self.value_stack.len(), 1);
                    debug_assert_eq!(return_point.pos, usize::MAX);
                    debug_assert_eq!(return_point.warp_counter, 0);
                    debug_assert_eq!(return_point.value_stack_size, 0);
                    return Ok(ProcessStep::Terminate { result: Some(self.value_stack.pop().unwrap()) });
                } else {
                    self.pos = return_point.pos;
                    self.warp_counter = return_point.warp_counter;
                }
            }
            Instruction::Broadcast { wait } => {
                let msg_type = self.value_stack.pop().unwrap().to_string(mc)?;
                let barrier = match *wait {
                    false => {
                        self.pos += 1;
                        None
                    }
                    true => {
                        let barrier = Barrier::new();
                        self.defer = Some(Defer::Barrier { condition: barrier.get_condition(), aft_pos: self.pos + 1 });
                        Some(barrier)
                    }
                };
                return Ok(ProcessStep::Broadcast { msg_type, barrier });
            }
        }

        Ok(ProcessStep::Normal)
    }
}

mod ops {
    use super::*;

    fn as_list<'gc>(v: &Value<'gc>) -> Option<GcCell<'gc, Vec<Value<'gc>>>> {
        match v {
            Value::List(v) => Some(*v),
            _ => None
        }
    }
    fn as_matrix<'gc>(v: &Value<'gc>) -> Option<GcCell<'gc, Vec<Value<'gc>>>> {
        let vals = as_list(v)?;
        let good = match vals.read().as_slice() {
            [] => false,
            [first, ..] => as_list(first).is_some(),
        };
        if good { Some(vals) } else { None }
    }

    pub(super) fn prep_list_index<'gc>(index: &Value<'gc>, list_len: usize) -> Result<usize, ErrorCause> {
        let raw_index = index.to_number()?;
        if raw_index < 1.0 || raw_index > list_len as f64 { return Err(ErrorCause::IndexOutOfBounds { index: raw_index, list_len }.into()) }
        let index = raw_index as u64;
        if index as f64 != raw_index { return Err(ErrorCause::IndexNotInteger { index: raw_index }.into()) }
        Ok(index as usize - 1)
    }

    const DEG_TO_RAD: f64 = std::f64::consts::PI / 180.0;

    fn binary_op_impl<'gc>(mc: MutationContext<'gc, '_>, a: &Value<'gc>, b: &Value<'gc>, matrix_mode: bool, cache: &mut BTreeMap<(Identity<'gc>, Identity<'gc>, bool), Value<'gc>>, scalar_op: fn(MutationContext<'gc, '_>, &Value<'gc>, &Value<'gc>) -> Result<Value<'gc>, ErrorCause>) -> Result<Value<'gc>, ErrorCause> {
        let cache_key = (a.identity(), b.identity(), matrix_mode);
        Ok(match cache.get(&cache_key) {
            Some(x) => *x,
            None => {
                let checker = if matrix_mode { as_matrix } else { as_list };
                match (checker(a), checker(b)) {
                    (Some(a), Some(b)) => {
                        let (a, b) = (a.read(), b.read());
                        let real_res = GcCell::allocate(mc, Vec::with_capacity(a.len().min(b.len()))).into();
                        cache.insert(cache_key, real_res);
                        let res = as_list(&real_res).unwrap();
                        let mut res = res.write(mc);
                        for (a, b) in iter::zip(&*a, &*b) {
                            res.push(binary_op_impl(mc, a, b, matrix_mode, cache, scalar_op)?);
                        }
                        real_res
                    }
                    (Some(a), None) => {
                        let a = a.read();
                        let real_res = GcCell::allocate(mc, Vec::with_capacity(a.len())).into();
                        cache.insert(cache_key, real_res);
                        let res = as_list(&real_res).unwrap();
                        let mut res = res.write(mc);
                        for a in &*a {
                            res.push(binary_op_impl(mc, a, b, matrix_mode, cache, scalar_op)?);
                        }
                        real_res
                    }
                    (None, Some(b)) => {
                        let b = b.read();
                        let real_res = GcCell::allocate(mc, Vec::with_capacity(b.len())).into();
                        cache.insert(cache_key, real_res);
                        let res = as_list(&real_res).unwrap();
                        let mut res = res.write(mc);
                        for b in &*b {
                            res.push(binary_op_impl(mc, a, b, matrix_mode, cache, scalar_op)?);
                        }
                        real_res
                    }
                    (None, None) => if matrix_mode { binary_op_impl(mc, a, b, false, cache, scalar_op)? } else { scalar_op(mc, a, b)? }
                }
            }
        })
    }
    pub(super) fn binary_op<'gc, 'a>(mc: MutationContext<'gc, '_>, a: &'a Value<'gc>, b: &'a Value<'gc>, op: BinaryOp) -> Result<Value<'gc>, ErrorCause> {
        let mut cache = Default::default();
        match op {
            BinaryOp::Add     => binary_op_impl(mc, a, b, true, &mut cache, |_, a, b| Ok((a.to_number()? + b.to_number()?).into())),
            BinaryOp::Sub     => binary_op_impl(mc, a, b, true, &mut cache, |_, a, b| Ok((a.to_number()? - b.to_number()?).into())),
            BinaryOp::Mul     => binary_op_impl(mc, a, b, true, &mut cache, |_, a, b| Ok((a.to_number()? * b.to_number()?).into())),
            BinaryOp::Div     => binary_op_impl(mc, a, b, true, &mut cache, |_, a, b| Ok((a.to_number()? / b.to_number()?).into())),
            BinaryOp::Pow     => binary_op_impl(mc, a, b, true, &mut cache, |_, a, b| Ok(libm::pow(a.to_number()?, b.to_number()?).into())),
            BinaryOp::Log     => binary_op_impl(mc, a, b, true, &mut cache, |_, a, b| Ok((libm::log2(b.to_number()?) / libm::log2(a.to_number()?)).into())),
            BinaryOp::Greater => binary_op_impl(mc, a, b, true, &mut cache, |_, a, b| Ok((a.to_number()? > b.to_number()?).into())),
            BinaryOp::Less    => binary_op_impl(mc, a, b, true, &mut cache, |_, a, b| Ok((a.to_number()? < b.to_number()?).into())),
            BinaryOp::Mod     => binary_op_impl(mc, a, b, true, &mut cache, |_, a, b| {
                let (a, b) = (a.to_number()?, b.to_number()?);
                Ok(if a.is_sign_positive() == b.is_sign_positive() { a % b } else { b + (a % -b) }.into())
            }),

            BinaryOp::SplitCustom => binary_op_impl(mc, a, b, true, &mut cache, |mc, a, b| {
                let (text, pattern) = (a.to_string(mc)?, b.to_string(mc)?);
                Ok(GcCell::allocate(mc, text.split(pattern.as_str()).map(|x| Gc::allocate(mc, x.to_owned()).into()).collect::<Vec<_>>()).into())
            }),
        }
    }

    fn unary_op_impl<'gc>(mc: MutationContext<'gc, '_>, x: &Value<'gc>, cache: &mut BTreeMap<Identity<'gc>, Value<'gc>>, scalar_op: &dyn Fn(MutationContext<'gc, '_>, &Value<'gc>) -> Result<Value<'gc>, ErrorCause>) -> Result<Value<'gc>, ErrorCause> {
        let cache_key = x.identity();
        Ok(match cache.get(&cache_key) {
            Some(x) => *x,
            None => match as_list(x) {
                Some(x) => {
                    let x = x.read();
                    let real_res = GcCell::allocate(mc, Vec::with_capacity(x.len())).into();
                    cache.insert(cache_key, real_res);
                    let res = as_list(&real_res).unwrap();
                    let mut res = res.write(mc);
                    for x in &*x {
                        res.push(unary_op_impl(mc, x, cache, scalar_op)?);
                    }
                    real_res
                }
                None => scalar_op(mc, x)?,
            }
        })
    }
    pub(super) fn unary_op<'gc>(mc: MutationContext<'gc, '_>, x: &Value<'gc>, op: UnaryOp) -> Result<Value<'gc>, ErrorCause> {
        let mut cache = Default::default();
        match op {
            UnaryOp::ToBool => unary_op_impl(mc, x, &mut cache, &|_, x| Ok(x.to_bool()?.into())),
            UnaryOp::Not    => unary_op_impl(mc, x, &mut cache, &|_, x| Ok((!x.to_bool()?).into())),
            UnaryOp::Abs    => unary_op_impl(mc, x, &mut cache, &|_, x| Ok(libm::fabs(x.to_number()?).into())),
            UnaryOp::Neg    => unary_op_impl(mc, x, &mut cache, &|_, x| Ok((-x.to_number()?).into())),
            UnaryOp::Sqrt   => unary_op_impl(mc, x, &mut cache, &|_, x| Ok(libm::sqrt(x.to_number()?).into())),
            UnaryOp::Round  => unary_op_impl(mc, x, &mut cache, &|_, x| Ok(libm::round(x.to_number()?).into())),
            UnaryOp::Floor  => unary_op_impl(mc, x, &mut cache, &|_, x| Ok(libm::floor(x.to_number()?).into())),
            UnaryOp::Ceil   => unary_op_impl(mc, x, &mut cache, &|_, x| Ok(libm::ceil(x.to_number()?).into())),
            UnaryOp::Sin    => unary_op_impl(mc, x, &mut cache, &|_, x| Ok(libm::sin(x.to_number()? * DEG_TO_RAD).into())),
            UnaryOp::Cos    => unary_op_impl(mc, x, &mut cache, &|_, x| Ok(libm::cos(x.to_number()? * DEG_TO_RAD).into())),
            UnaryOp::Tan    => unary_op_impl(mc, x, &mut cache, &|_, x| Ok(libm::tan(x.to_number()? * DEG_TO_RAD).into())),
            UnaryOp::Asin   => unary_op_impl(mc, x, &mut cache, &|_, x| Ok((libm::asin(x.to_number()?) / DEG_TO_RAD).into())),
            UnaryOp::Acos   => unary_op_impl(mc, x, &mut cache, &|_, x| Ok((libm::acos(x.to_number()?) / DEG_TO_RAD).into())),
            UnaryOp::Atan   => unary_op_impl(mc, x, &mut cache, &|_, x| Ok((libm::atan(x.to_number()?) / DEG_TO_RAD).into())),
            UnaryOp::Strlen => unary_op_impl(mc, x, &mut cache, &|_, x| Ok((x.to_string(mc)?.chars().count() as f64).into())),

            UnaryOp::SplitLetter => unary_op_impl(mc, x, &mut cache, &|mc, x| {
                Ok(GcCell::allocate(mc, x.to_string(mc)?.chars().map(|x| Gc::allocate(mc, x.to_string()).into()).collect::<Vec<_>>()).into())
            }),
            UnaryOp::SplitWord => unary_op_impl(mc, x, &mut cache, &|mc, x| {
                Ok(GcCell::allocate(mc, x.to_string(mc)?.split_whitespace().map(|x| Gc::allocate(mc, x.to_owned()).into()).collect::<Vec<_>>()).into())
            }),
            UnaryOp::SplitTab => unary_op_impl(mc, x, &mut cache, &|mc, x| {
                Ok(GcCell::allocate(mc, x.to_string(mc)?.split('\t').map(|x| Gc::allocate(mc, x.to_owned()).into()).collect::<Vec<_>>()).into())
            }),
            UnaryOp::SplitCR => unary_op_impl(mc, x, &mut cache, &|mc, x| {
                Ok(GcCell::allocate(mc, x.to_string(mc)?.split('\r').map(|x| Gc::allocate(mc, x.to_owned()).into()).collect::<Vec<_>>()).into())
            }),
            UnaryOp::SplitLF => unary_op_impl(mc, x, &mut cache, &|mc, x| {
                Ok(GcCell::allocate(mc, x.to_string(mc)?.lines().map(|x| Gc::allocate(mc, x.to_owned()).into()).collect::<Vec<_>>()).into())
            }),
            UnaryOp::SplitCsv => unary_op_impl(mc, x, &mut cache, &|mc, x| {
                let lines = x.to_string(mc)?.lines().map(|line| GcCell::allocate(mc, line.split(',').map(|x| Gc::allocate(mc, x.to_owned()).into()).collect::<Vec<_>>()).into()).collect::<Vec<_>>();
                Ok(match lines.len() {
                    1 => lines.into_iter().next().unwrap(),
                    _ => GcCell::allocate(mc, lines).into(),
                })
            }),
            UnaryOp::SplitJson => unary_op_impl(mc, x, &mut cache, &|mc, x| {
                let value = x.to_string(mc)?;
                match serde_json::from_str::<Json>(value.as_str()) {
                    Ok(json) => match SimpleValue::try_from(json) {
                        Ok(x) => Ok(Value::from_simple(mc, x)),
                        Err(JsonError::HadNull) => Err(ErrorCause::JsonHadNull { value: (*value).clone() }),
                        Err(JsonError::HadBadNumber) => Err(ErrorCause::JsonHadBadNumber { value: (*value).clone() }),
                    }
                    Err(_) => Err(ErrorCause::NotJson { value: (*value).clone() }),
                }
            }),

            UnaryOp::UnicodeToChar => unary_op_impl(mc, x, &mut cache, &|mc, x| {
                let fnum = x.to_number()?;
                if fnum < 0.0 || fnum > u32::MAX as f64 { return Err(ErrorCause::InvalidUnicode { value: fnum }) }
                let num = fnum as u32;
                if num as f64 != fnum { return Err(ErrorCause::InvalidUnicode { value: fnum }) }
                match char::from_u32(num) {
                    Some(ch) => Ok(Gc::allocate(mc, ch.to_string()).into()),
                    None => Err(ErrorCause::InvalidUnicode { value: fnum }),
                }
            }),
            UnaryOp::CharToUnicode => unary_op_impl(mc, x, &mut cache, &|mc, x| {
                let src = x.to_string(mc)?;
                let values: Vec<_> = src.chars().map(|ch| (ch as u32 as f64).into()).collect();
                Ok(match values.len() {
                    1 => values.into_iter().next().unwrap(),
                    _ => GcCell::allocate(mc, values).into(),
                })
            }),
        }
    }
    pub(super) fn index_list<'gc>(mc: MutationContext<'gc, '_>, list: &Value<'gc>, index: &Value<'gc>) -> Result<Value<'gc>, ErrorCause> {
        let list = list.to_list(mc)?;
        let list = list.read();
        unary_op_impl(mc, index, &mut Default::default(), &|_, x| Ok(list[prep_list_index(x, list.len())?]))
    }

    fn check_eq_impl<'gc>(a: &Value<'gc>, b: &Value<'gc>, cache: &mut BTreeSet<(Identity<'gc>, Identity<'gc>)>) -> bool {
        // if already cached, that cmp handles overall check, so no-op with true (if we ever get a false, the whole thing is false)
        if !cache.insert((a.identity(), b.identity())) { return true }

        match (a, b) {
            (Value::Bool(a), Value::Bool(b)) => *a == *b,
            (Value::Bool(_), _) | (_, Value::Bool(_)) => false,

            (Value::Number(a), Value::Number(b)) => *a == *b,
            (Value::String(a), Value::String(b)) => a.to_lowercase() == b.to_lowercase(),
            (Value::Number(n), Value::String(s)) | (Value::String(s), Value::Number(n)) => match s.parse::<f64>() {
                Ok(s) => s == *n,
                Err(_) => **s == n.to_string(),
            }

            (Value::Closure(a), Value::Closure(b)) => a.as_ptr() == b.as_ptr(),
            (Value::Closure(_), _) | (_, Value::Closure(_)) => false,

            (Value::List(a), Value::List(b)) => {
                let (a, b) = (a.read(), b.read());
                if a.len() != b.len() { return false }
                for (a, b) in iter::zip(&*a, &*b) {
                    if !check_eq_impl(a, b, cache) { return false }
                }
                true
            }
            (Value::List(_), _) | (_, Value::List(_)) => false,

            (Value::Entity(a), Value::Entity(b)) => a.as_ptr() == b.as_ptr(),
            (Value::Entity(_), _) | (_, Value::Entity(_)) => false,
        }
    }
    pub(super) fn check_eq<'gc, 'a>(a: &'a Value<'gc>, b: &'a Value<'gc>) -> bool {
        check_eq_impl(a, b, &mut Default::default())
    }
}
