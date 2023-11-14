//! [`ByteCode`] execution utilities.
//! 
//! Because the NetsBlox runtime allows for the creation of cycles, all program-accessible objects must be garbage collected.
//! To do this, we use the `gc-arena` crate, which allows a simple and correct mechanism for provably disjoint garbage collected runtime environments.
//! However, `gc-arena` makes this guarantee by forbidding garbage collected objects from leaving the arena.
//! Thus, many types in this module, such as  [`Value`] and [`Process`], are branded with an invariant `'gc` lifetime and can only be access by callback.
//! Some utilities are provided to export these values from the runtime environment if needed.

use alloc::rc::Rc;
use alloc::vec::Vec;
use alloc::string::{String, ToString};
use alloc::collections::{BTreeMap, BTreeSet, VecDeque, vec_deque::Iter as VecDequeIter};
use alloc::borrow::ToOwned;

use core::iter::{self, Cycle};
use core::cmp::Ordering;

use unicase::UniCase;

#[cfg(feature = "serde")]
use serde::Serialize;

use crate::*;
use crate::gc::*;
use crate::json::*;
use crate::runtime::*;
use crate::bytecode::*;
use crate::util::*;

fn empty_string() -> Rc<String> {
    #[cfg(feature = "std")]
    {
        std::thread_local! {
            static VALUE: Rc<String> = Rc::new(String::new());
        }
        VALUE.with(|x| x.clone())
    }
    #[cfg(not(feature = "std"))]
    {
        Rc::new(String::new())
    }
}

/// A variable entry in the structure expected by the standard js extension.
#[cfg_attr(feature = "serde", derive(Serialize))]
#[derive(Debug, Clone)]
pub struct VarEntry {
    pub name: String,
    pub value: String,
}
/// A trace entry in the structure expected by the standard js extension.
#[cfg_attr(feature = "serde", derive(Serialize))]
#[derive(Debug, Clone)]
pub struct TraceEntry {
    pub location: String,
    pub locals: Vec<VarEntry>,
}
/// A error message in the structure expected by the standard js extension.
#[cfg_attr(feature = "serde", derive(Serialize))]
#[derive(Debug, Clone)]
pub struct ErrorSummary {
    pub cause: String,
    pub entity: String,
    pub globals: Vec<VarEntry>,
    pub fields: Vec<VarEntry>,
    pub trace: Vec<TraceEntry>,
}
impl ErrorSummary {
    pub fn extract<C: CustomTypes<S>, S: System<C>>(error: &ExecError<C, S>, process: &Process<C, S>, locations: &Locations) -> Self {
        let raw_entity = process.call_stack.last().unwrap().entity;
        let entity = raw_entity.borrow().name.as_str().to_owned();
        let cause = format!("{:?}", error.cause);

        fn summarize_symbols<C: CustomTypes<S>, S: System<C>>(symbols: &SymbolTable<'_, C, S>) -> Vec<VarEntry> {
            let mut res = Vec::with_capacity(symbols.len());
            for (k, v) in symbols {
                res.push(VarEntry { name: k.clone(), value: format!("{:?}", &*v.get()) });
            }
            res
        }
        let globals = summarize_symbols(&process.global_context.borrow().globals);
        let fields = summarize_symbols(&raw_entity.borrow().fields);

        let mut trace = Vec::with_capacity(process.call_stack.len());
        for (pos, locals) in iter::zip(process.call_stack[1..].iter().map(|x| x.called_from).chain(iter::once(error.pos)), process.call_stack.iter().map(|x| &x.locals)) {
            if let Some(location) = locations.lookup(pos) {
                trace.push(TraceEntry { location, locals: summarize_symbols(locals) });
            }
        }

        Self { entity, cause, globals, fields, trace }
    }
}

/// An execution error from a [`Process`] (see [`Process::step`]).
///
/// This consists of an [`ErrorCause`] value describing the cause, as well as the bytecode location of the error.
/// By using the [`Locations`] information from [`ByteCode::compile`], it is possible to determine
/// a human-readable error location in the original program.
#[derive(Educe)]
#[educe(Debug)]
pub struct ExecError<C: CustomTypes<S>, S: System<C>> {
    pub cause: ErrorCause<C, S>,
    pub pos: usize,
}

/// Result of stepping through a [`Process`].
#[derive(Educe)]
#[educe(Debug)]
pub enum ProcessStep<'gc, C: CustomTypes<S>, S: System<C>> {
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
    Terminate { result: Option<Value<'gc, C, S>> },
    /// The process has requested to broadcast a message to all entities (if `target` is `None`) or to a specific `target`, which may trigger other code to execute.
    Broadcast { msg_type: String, barrier: Option<Barrier>, targets: Option<Vec<Gc<'gc, RefLock<Entity<'gc, C, S>>>>> },
    /// The process has requested to create or destroy a new watcher for a variable.
    /// If `create` is true, the process is requesting to register the given watcher.
    /// If `create` if false, the process is requesting to remove a watcher which is equivalent to the given watcher.
    /// In either case, it is up the handler of this step mode to deduplicate watchers to the same variable, if needed.
    /// The existence of a watcher is invisible to a process, so it is perfectly valid for implementors to simply ignore all watcher requests.
    Watcher { create: bool, watcher: Watcher<'gc, C, S> },
    /// The process has requested to fork a new process that starts with the given parameters.
    Fork { pos: usize, locals: SymbolTable<'gc, C, S>, entity: Gc<'gc, RefLock<Entity<'gc, C, S>>> },
    /// The process has created a new clone of an existing entity.
    /// The clone has already been created, so this is just an informational flag for any logging or other initialization logic.
    /// Projects use this event to bind new scripts to the clone, which is an aspect of projects but not processes or entities.
    CreatedClone { new_entity: Gc<'gc, RefLock<Entity<'gc, C, S>>> },
    /// The process has requested to pause execution of the (entire) project.
    /// This can be useful for student debugging (similar to breakpoints), but can be ignored by the executor if desired.
    Pause,
}

/// An entry in the call stack of a [`Process`].
/// 
/// This contains information about the call origin and local variables defined in the called context.
#[derive(Collect)]
#[collect(no_drop, bound = "")]
pub struct CallStackEntry<'gc, C: CustomTypes<S>, S: System<C>> {
    #[collect(require_static)] pub called_from: usize,
    #[collect(require_static)]     return_to: usize,
                               pub entity: Gc<'gc, RefLock<Entity<'gc, C, S>>>,
                               pub locals: SymbolTable<'gc, C, S>,

    #[collect(require_static)]     warp_counter: usize,
    #[collect(require_static)]     value_stack_size: usize,
    #[collect(require_static)]     handler_stack_size: usize,
}

struct Handler {
    pos: usize,
    var: String,
    warp_counter: usize,
    call_stack_size: usize,
    value_stack_size: usize,
}

enum Defer<C: CustomTypes<S>, S: System<C>> {
    Request { key: S::RequestKey, aft_pos: usize, action: RequestAction },
    Command { key: S::CommandKey, aft_pos: usize },
    MessageReply { key: S::ExternReplyKey, aft_pos: usize },
    Barrier { condition: BarrierCondition, aft_pos: usize },
    Sleep { until: u64, aft_pos: usize },
}
#[derive(Clone, Copy)]
enum RequestAction {
    Rpc, Syscall, Input, Push,
}

/// A collection of context info for starting a new [`Process`].
#[derive(Collect, Educe)]
#[collect(no_drop, bound = "")]
#[educe(Clone)]
pub struct ProcContext<'gc, C: CustomTypes<S>, S: System<C>> {
                               pub global_context: Gc<'gc, RefLock<GlobalContext<'gc, C, S>>>,
                               pub entity: Gc<'gc, RefLock<Entity<'gc, C, S>>>,
                               pub locals: SymbolTable<'gc, C, S>,
    #[collect(require_static)] pub start_pos: usize,
    #[collect(require_static)] pub barrier: Option<Barrier>,
    #[collect(require_static)] pub reply_key: Option<S::InternReplyKey>,
    #[collect(require_static)] pub local_message: Option<String>,
}

/// A [`ByteCode`] execution primitive.
/// 
/// A [`Process`] is a self-contained thread of execution.
/// It maintains its own state machine for executing instructions step by step.
#[derive(Collect)]
#[collect(no_drop, bound = "")]
pub struct Process<'gc, C: CustomTypes<S>, S: System<C>> {
                               pub global_context: Gc<'gc, RefLock<GlobalContext<'gc, C, S>>>,
    #[collect(require_static)] pub state: C::ProcessState,
    #[collect(require_static)]     pos: usize,
    #[collect(require_static)]     barrier: Option<Barrier>,
    #[collect(require_static)]     reply_key: Option<S::InternReplyKey>,
    #[collect(require_static)]     warp_counter: usize,
                                   call_stack: Vec<CallStackEntry<'gc, C, S>>,
                                   value_stack: Vec<Value<'gc, C, S>>,
    #[collect(require_static)]     handler_stack: Vec<Handler>,
    #[collect(require_static)]     defer: Option<Defer<C, S>>,
                                   last_syscall_error: Option<Value<'gc, C, S>>,
                                   last_rpc_error: Option<Value<'gc, C, S>>,
                                   last_answer: Option<Value<'gc, C, S>>,
                                   last_message: Option<Value<'gc, C, S>>,
}
impl<'gc, C: CustomTypes<S>, S: System<C>> Process<'gc, C, S> {
    /// Creates a new [`Process`] with the given starting context.
    pub fn new(context: ProcContext<'gc, C, S>) -> Self {
        Self {
            global_context: context.global_context,
            barrier: context.barrier,
            reply_key: context.reply_key,
            pos: context.start_pos,
            warp_counter: 0,
            state: C::ProcessState::from(&*context.entity.borrow()),
            call_stack: vec![CallStackEntry {
                called_from: usize::MAX,
                return_to: usize::MAX,
                warp_counter: 0,
                value_stack_size: 0,
                handler_stack_size: 0,
                locals: context.locals,
                entity: context.entity,
            }],
            value_stack: vec![],
            handler_stack: vec![],
            defer: None,
            last_syscall_error: None,
            last_rpc_error: None,
            last_answer: None,
            last_message: context.local_message.map(|x| Rc::new(x).into()),
        }
    }
    /// Checks if the process is currently running.
    /// Note that the process will not run on its own (see [`Process::step`]).
    pub fn is_running(&self) -> bool {
        self.pos != usize::MAX
    }
    /// Gets a reference to the current call stack.
    /// This is a sequence of every call frame, including the current context entity, local variables in scope, and other hidden state information.
    /// Due to the delicate state involved, a mutable option is not supported.
    pub fn get_call_stack(&self) -> &[CallStackEntry<'gc, C, S>] {
        &self.call_stack
    }
    /// Executes a single bytecode instruction.
    /// The return value can be used to determine what additional effects the script has requested,
    /// as well as to retrieve the return value or execution error in the event that the process terminates.
    /// 
    /// The process transitions to the idle state (see [`Process::is_running`]) upon failing with [`Err`] or succeeding with [`ProcessStep::Terminate`].
    /// 
    /// This function is not re-entrant, so calling it from the mutable handle of, e.g., [`Config`] will likely lead to panics.
    pub fn step(&mut self, mc: &Mutation<'gc>) -> Result<ProcessStep<'gc, C, S>, ExecError<C, S>> {
        if !self.is_running() {
            return Ok(ProcessStep::Idle);
        }

        let mut res = self.step_impl(mc).map_err(|cause| ExecError { cause, pos: self.pos });
        if let Err(err) = &res {
            if let Some(Handler { pos, var, warp_counter, call_stack_size, value_stack_size }) = self.handler_stack.last() {
                self.warp_counter = *warp_counter;
                self.call_stack.drain(*call_stack_size..);
                self.value_stack.drain(*value_stack_size..);
                debug_assert_eq!(self.call_stack.len(), *call_stack_size);
                debug_assert_eq!(self.value_stack.len(), *value_stack_size);

                let msg = match &err.cause {
                    ErrorCause::Custom { msg } => msg.clone(),
                    x => format!("{x:?}"),
                };
                self.call_stack.last_mut().unwrap().locals.define_or_redefine(var, Shared::Unique(Value::String(Rc::new(msg))));
                self.pos = *pos;
                res = Ok(ProcessStep::Normal);
            }
        }

        if let Ok(ProcessStep::Terminate { .. }) | Err(_) = &res {
            self.pos = usize::MAX;
            self.barrier = None;
            self.reply_key = None;
            self.defer = None;
        }

        res
    }
    fn step_impl(&mut self, mc: &Mutation<'gc>) -> Result<ProcessStep<'gc, C, S>, ErrorCause<C, S>> {
        fn process_result<'gc, C: CustomTypes<S>, S: System<C>, T>(result: Result<T, String>, error_scheme: ErrorScheme, stack: Option<&mut Vec<Value<'gc, C, S>>>, last_ok: Option<&mut Option<Value<'gc, C, S>>>, last_err: Option<&mut Option<Value<'gc, C, S>>>, to_value: fn(T) -> Option<Value<'gc, C, S>>) -> Result<(), ErrorCause<C, S>> {
            match result {
                Ok(x) => match to_value(x) {
                    Some(x) => {
                        if let Some(last_err) = last_err { *last_err = None }
                        match (last_ok, stack) {
                            (Some(last_ok), Some(stack)) => {
                                *last_ok = Some(x.clone());
                                stack.push(x);
                            }
                            (Some(last_ok), None) => *last_ok = Some(x),
                            (None, Some(stack)) => stack.push(x),
                            (None, None) => (),
                        }
                    }
                    None => assert!(last_ok.is_none() && stack.is_none()),
                }
                Err(x) => match error_scheme {
                    ErrorScheme::Soft => {
                        let x = Value::String(Rc::new(x));

                        if let Some(last_ok) = last_ok { *last_ok = None }
                        match (last_err, stack) {
                            (Some(last_err), Some(stack)) => {
                                *last_err = Some(x.clone());
                                stack.push(x);
                            }
                            (Some(last_err), None) => *last_err = Some(x),
                            (None, Some(stack)) => stack.push(x),
                            (None, None) => (),
                        }
                    }
                    ErrorScheme::Hard => return Err(ErrorCause::Promoted { error: x }),
                }
            }
            Ok(())
        }
        fn prep_call_closure<'gc, C: CustomTypes<S>, S: System<C>>(mc: &Mutation<'gc>, value_stack: &mut Vec<Value<'gc, C, S>>, args: usize) -> Result<(usize, SymbolTable<'gc, C, S>), ErrorCause<C, S>> {
            let mut values = value_stack.drain(value_stack.len() - (args + 1)..);
            let closure = values.next().unwrap().as_closure()?;
            let mut closure = closure.borrow_mut(mc);
            if closure.params.len() != args {
                return Err(ErrorCause::ClosureArgCount { expected: closure.params.len(), got: args });
            }

            let mut locals = SymbolTable::default();
            for (k, v) in closure.captures.iter_mut() {
                locals.define_or_redefine(k, v.alias(mc));
            }
            for (var, value) in iter::zip(&closure.params, values) {
                locals.define_or_redefine(var, value.into());
            }

            Ok((closure.pos, locals))
        }

        let system = self.global_context.borrow().system.clone();
        match self.defer.take() {
            None => (),
            Some(Defer::Request { key, aft_pos, action }) => match system.poll_request(mc, &key, self)? {
                AsyncResult::Completed(x) => {
                    let settings = &self.global_context.borrow().settings;
                    match action {
                        RequestAction::Syscall => process_result(x, settings.syscall_error_scheme, Some(&mut self.value_stack), None, Some(&mut self.last_syscall_error), Some)?,
                        RequestAction::Rpc => process_result(x, settings.rpc_error_scheme, Some(&mut self.value_stack), None, Some(&mut self.last_rpc_error), Some)?,
                        RequestAction::Input => process_result(x, ErrorScheme::Hard, None, Some(&mut self.last_answer), None, Some)?,
                        RequestAction::Push => process_result(x, ErrorScheme::Hard, Some(&mut self.value_stack), None, None, Some)?,
                    }
                    self.pos = aft_pos;
                }
                AsyncResult::Pending => {
                    self.defer = Some(Defer::Request { key, aft_pos, action });
                    return Ok(ProcessStep::Yield);
                }
                AsyncResult::Consumed => panic!(),
            }
            Some(Defer::Command { key, aft_pos }) => match system.poll_command(mc, &key, self)? {
                AsyncResult::Completed(x) => {
                    process_result(x, ErrorScheme::Hard, None, None, None, |_| None)?;
                    self.pos = aft_pos;
                }
                AsyncResult::Pending => {
                    self.defer = Some(Defer::Command { key, aft_pos });
                    return Ok(ProcessStep::Yield);
                }
                AsyncResult::Consumed => panic!(),
            }
            Some(Defer::MessageReply { key, aft_pos }) => match system.poll_reply(&key) {
                AsyncResult::Completed(x) => {
                    let value = match x {
                        Some(x) => Value::from_simple(mc, SimpleValue::from_netsblox_json(x)?),
                        None => empty_string().into(),
                    };
                    self.value_stack.push(value);
                    self.pos = aft_pos;
                }
                AsyncResult::Pending => {
                    self.defer = Some(Defer::MessageReply { key, aft_pos });
                    return Ok(ProcessStep::Yield);
                }
                AsyncResult::Consumed => panic!(),
            }
            Some(Defer::Barrier { condition, aft_pos }) => match condition.is_completed() {
                true => {
                    self.pos = aft_pos;
                }
                false => {
                    self.defer = Some(Defer::Barrier { condition, aft_pos });
                    return Ok(ProcessStep::Yield);
                }
            }
            Some(Defer::Sleep { until, aft_pos }) => match system.time(Precision::Low).to_arbitrary_ms()? >= until {
                true => {
                    self.pos = aft_pos;
                }
                false => {
                    self.defer = Some(Defer::Sleep { until, aft_pos });
                    return Ok(ProcessStep::Yield);
                }
            }
        }

        let mut global_context_raw = self.global_context.borrow_mut(mc);
        let global_context = &mut *global_context_raw;

        macro_rules! lookup_var {
            ($var:expr => $m:ident) => {{
                let var = $var;
                let local_frame = self.call_stack.last_mut().unwrap();
                match LookupGroup::new(&mut [&mut global_context.globals, &mut local_frame.entity.borrow_mut(mc).fields, &mut local_frame.locals]).$m(var) {
                    Some(x) => x,
                    None => return Err(ErrorCause::UndefinedVariable { name: var.into() }),
                }
            }};
            ($var:expr) => {lookup_var!($var => lookup)};
            (mut $var:expr) => {lookup_var!($var => lookup_mut)};
        }

        let (ins, aft_pos) = Instruction::read(&global_context.bytecode.code, &global_context.bytecode.data, self.pos);
        match ins {
            Instruction::Yield => {
                self.pos = aft_pos;
                if self.warp_counter == 0 { return Ok(ProcessStep::Yield) }
            }
            Instruction::WarpStart => {
                self.warp_counter += 1;
                self.pos = aft_pos;
            }
            Instruction::WarpStop => {
                self.warp_counter -= 1;
                self.pos = aft_pos;
            }

            Instruction::PushBool { value } => {
                self.value_stack.push(value.into());
                self.pos = aft_pos;
            }
            Instruction::PushInt { value } => {
                self.value_stack.push(Number::new(value as f64)?.into());
                self.pos = aft_pos;
            }
            Instruction::PushNumber { value } => {
                self.value_stack.push(Number::new(value)?.into());
                self.pos = aft_pos;
            }
            Instruction::PushColor { value } => {
                let Color { r, g, b, a } = value;
                self.value_stack.push(Number::new(u32::from_be_bytes([a, r, g ,b]) as f64)?.into());
                self.pos = aft_pos;
            }
            Instruction::PushString { value } => {
                self.value_stack.push(Value::String(Rc::new(value.to_owned())));
                self.pos = aft_pos;
            }
            Instruction::PushVariable { var } => {
                self.value_stack.push(lookup_var!(var).get().clone());
                self.pos = aft_pos;
            }
            Instruction::PushEntity { name } => match global_context.entities.iter().find(|&x| x.0 == name) {
                Some(x) => {
                    self.value_stack.push(Value::Entity(x.1));
                    self.pos = aft_pos;
                }
                None => return Err(ErrorCause::UndefinedEntity { name: name.into() }),
            }
            Instruction::PushSelf => {
                self.value_stack.push(self.call_stack.last().unwrap().entity.into());
                self.pos = aft_pos;
            }
            Instruction::PopValue => {
                self.value_stack.pop().unwrap();
                self.pos = aft_pos;
            }

            Instruction::DupeValue { top_index } => {
                let val = self.value_stack[self.value_stack.len() - 1 - top_index as usize].clone();
                self.value_stack.push(val);
                self.pos = aft_pos;
            }
            Instruction::SwapValues { top_index_1, top_index_2 } => {
                let len = self.value_stack.len();
                self.value_stack.swap(len - 1 - top_index_1 as usize, len - 1 - top_index_2 as usize);
                self.pos = aft_pos;
            }

            Instruction::TypeQuery { ty } => {
                let val = self.value_stack.pop().unwrap();
                self.value_stack.push((val.get_type() == ty.to_type()).into());
                self.pos = aft_pos;
            }
            Instruction::ToBool => {
                let val = self.value_stack.pop().unwrap();
                self.value_stack.push(val.as_bool()?.into());
                self.pos = aft_pos;
            }
            Instruction::ToNumber => {
                let val = self.value_stack.pop().unwrap();
                self.value_stack.push(val.as_number()?.into());
                self.pos = aft_pos;
            }

            Instruction::ListCons => {
                let mut res = self.value_stack.pop().unwrap().as_list()?.borrow().clone();
                res.push_front(self.value_stack.pop().unwrap());
                self.value_stack.push(Gc::new(mc, RefLock::new(res)).into());
                self.pos = aft_pos;
            }
            Instruction::ListCdr => {
                let mut res = self.value_stack.pop().unwrap().as_list()?.borrow().clone();
                if res.is_empty() { return Err(ErrorCause::IndexOutOfBounds { index: 1, len: 0 }) }
                res.pop_front().unwrap();
                self.value_stack.push(Gc::new(mc, RefLock::new(res)).into());
                self.pos = aft_pos;
            }

            Instruction::ListFind => {
                let list = self.value_stack.pop().unwrap().as_list()?;
                let value = self.value_stack.pop().unwrap();
                let res = ops::find(list, &value)?.map(|i| i + 1).unwrap_or(0);
                self.value_stack.push(Number::new(res as f64)?.into());
                self.pos = aft_pos;
            }
            Instruction::ListContains => {
                let value = self.value_stack.pop().unwrap();
                let list = self.value_stack.pop().unwrap().as_list()?;
                self.value_stack.push(ops::find(list, &value)?.is_some().into());
                self.pos = aft_pos;
            }

            Instruction::ListIsEmpty => {
                let list = self.value_stack.pop().unwrap().as_list()?;
                self.value_stack.push(list.borrow().is_empty().into());
                self.pos = aft_pos;
            }
            Instruction::ListLength => {
                let list = self.value_stack.pop().unwrap().as_list()?;
                self.value_stack.push(Number::new(list.borrow().len() as f64)?.into());
                self.pos = aft_pos;
            }
            Instruction::ListDims => {
                let list = self.value_stack.pop().unwrap();
                self.value_stack.push(Gc::new(mc, RefLock::new(ops::dimensions(&list)?.into_iter().map(|x| Ok(Number::new(x as f64)?.into())).collect::<Result<VecDeque<_>, NumberError>>()?)).into());
                self.pos = aft_pos;
            }
            Instruction::ListRank => {
                let list = self.value_stack.pop().unwrap();
                self.value_stack.push(Number::new(ops::dimensions(&list)?.len() as f64)?.into());
                self.pos = aft_pos;
            }

            Instruction::ListRev => {
                let list = self.value_stack.pop().unwrap().as_list()?;
                self.value_stack.push(Gc::new(mc, RefLock::new(list.borrow().iter().rev().cloned().collect::<VecDeque<_>>())).into());
                self.pos = aft_pos;
            }
            Instruction::ListFlatten => {
                let list = self.value_stack.pop().unwrap();
                self.value_stack.push(Gc::new(mc, RefLock::new(ops::flatten(&list)?)).into());
                self.pos = aft_pos;
            }
            Instruction::ListReshape { len } => {
                let raw_dims: Vec<_> = match len {
                    VariadicLen::Fixed(len) => {
                        let stack_size = self.value_stack.len();
                        self.value_stack.drain(stack_size - len..).collect()
                    }
                    VariadicLen::Dynamic => self.value_stack.pop().unwrap().as_list()?.borrow().iter().cloned().collect(),
                };
                let src = self.value_stack.pop().unwrap();

                let mut dims = Vec::with_capacity(raw_dims.len());
                for dim in raw_dims {
                    let dim = dim.as_number()?.get();
                    if dim < 0.0 || dim > usize::MAX as f64 { return Err(ErrorCause::InvalidSize { value: dim }) }
                    let int_dim = dim as usize;
                    if int_dim as f64 != dim { return Err(ErrorCause::InvalidSize { value: dim }) }
                    dims.push(int_dim);
                }

                self.value_stack.push(ops::reshape(mc, &src, &dims)?);
                self.pos = aft_pos;
            }
            Instruction::ListCartesianProduct { len } => {
                let sources: Vec<_> = match len {
                    VariadicLen::Fixed(len) => {
                        let stack_size = self.value_stack.len();
                        self.value_stack.drain(stack_size - len..).map(|x| x.as_list()).collect::<Result<_,_>>()?
                    }
                    VariadicLen::Dynamic => self.value_stack.pop().unwrap().as_list()?.borrow().iter().map(|x| x.as_list()).collect::<Result<_,_>>()?,
                };
                self.value_stack.push(Gc::new(mc, RefLock::new(ops::cartesian_product(mc, &sources))).into());
                self.pos = aft_pos;
            }

            Instruction::ListJson => {
                let value = self.value_stack.pop().unwrap().to_simple()?.into_json()?;
                self.value_stack.push(Rc::new(value.to_string()).into());
                self.pos = aft_pos;
            }
            Instruction::ListCsv => {
                let value = self.value_stack.pop().unwrap();
                self.value_stack.push(Rc::new(ops::to_csv(&value)?).into());
                self.pos = aft_pos;
            }
            Instruction::ListColumns => {
                let value = self.value_stack.pop().unwrap();
                self.value_stack.push(ops::columns(mc, &value)?);
                self.pos = aft_pos;
            }
            Instruction::ListLines => {
                let value = self.value_stack.pop().unwrap().as_list()?;
                let value = value.borrow();

                let mut values = value.iter();
                let res = match values.next() {
                    Some(x) => {
                        let mut res = x.as_string()?.into_owned();
                        for x in values {
                            res.push('\n');
                            res.push_str(x.as_string()?.as_ref());
                        }
                        Rc::new(res)
                    }
                    None => empty_string(),
                };

                self.value_stack.push(res.into());
                self.pos = aft_pos;
            }

            Instruction::ListInsert => {
                let list = self.value_stack.pop().unwrap().as_list()?;
                let index = self.value_stack.pop().unwrap();
                let val = self.value_stack.pop().unwrap();
                let mut list = list.borrow_mut(mc);

                let index = ops::prep_index(&index, list.len() + 1)?;
                list.insert(index, val);
                self.pos = aft_pos;
            }
            Instruction::ListInsertLast => {
                let list = self.value_stack.pop().unwrap().as_list()?;
                let val = self.value_stack.pop().unwrap();
                list.borrow_mut(mc).push_back(val);
                self.pos = aft_pos;
            }
            Instruction::ListInsertRandom => {
                let list = self.value_stack.pop().unwrap().as_list()?;
                let val = self.value_stack.pop().unwrap();
                let mut list = list.borrow_mut(mc);

                let index = ops::prep_rand_index(&*system, list.len() + 1)?;
                list.insert(index, val);
                self.pos = aft_pos;
            }

            Instruction::ListGet => {
                let list = self.value_stack.pop().unwrap();
                let index = self.value_stack.pop().unwrap();
                self.value_stack.push(ops::index_list(mc, &*system, &list, &index)?);
                self.pos = aft_pos;
            }
            Instruction::ListGetLast => {
                let list = self.value_stack.pop().unwrap().as_list()?;
                self.value_stack.push(match list.borrow().back() {
                    Some(x) => x.clone(),
                    None => return Err(ErrorCause::IndexOutOfBounds { index: 1, len: 0 }),
                });
                self.pos = aft_pos;
            }
            Instruction::ListGetRandom => {
                let list = self.value_stack.pop().unwrap().as_list()?;
                let list = list.borrow();
                let index = ops::prep_rand_index(&*system, list.len())?;
                self.value_stack.push(list[index].clone());
                self.pos = aft_pos;
            }

            Instruction::ListAssign => {
                let value = self.value_stack.pop().unwrap();
                let list = self.value_stack.pop().unwrap().as_list()?;
                let index = self.value_stack.pop().unwrap();
                let mut list = list.borrow_mut(mc);

                let index = ops::prep_index(&index, list.len())?;
                list[index] = value;
                self.pos = aft_pos;
            }
            Instruction::ListAssignLast => {
                let value = self.value_stack.pop().unwrap();
                let list = self.value_stack.pop().unwrap().as_list()?;
                let mut list = list.borrow_mut(mc);
                if list.is_empty() { return Err(ErrorCause::IndexOutOfBounds { index: 1, len: 0 }); }
                *list.back_mut().unwrap() = value;
                self.pos = aft_pos;
            }
            Instruction::ListAssignRandom => {
                let value = self.value_stack.pop().unwrap();
                let list = self.value_stack.pop().unwrap().as_list()?;
                let mut list = list.borrow_mut(mc);

                let index = ops::prep_rand_index(&*system, list.len())?;
                list[index] = value;
                self.pos = aft_pos;
            }

            Instruction::ListRemove => {
                let list = self.value_stack.pop().unwrap().as_list()?;
                let index = self.value_stack.pop().unwrap();
                let mut list = list.borrow_mut(mc);
                let index = ops::prep_index(&index, list.len())?;
                list.remove(index);
                self.pos = aft_pos;
            }
            Instruction::ListRemoveLast => {
                let list = self.value_stack.pop().unwrap().as_list()?;
                let mut list = list.borrow_mut(mc);
                if list.is_empty() { return Err(ErrorCause::IndexOutOfBounds { index: 1, len: 0 }) }
                list.pop_back().unwrap();
                self.pos = aft_pos;
            }
            Instruction::ListRemoveAll => {
                self.value_stack.pop().unwrap().as_list()?.borrow_mut(mc).clear();
                self.pos = aft_pos;
            }

            Instruction::ListPopFirstOrElse { goto } => match self.value_stack.pop().unwrap().as_list()?.borrow_mut(mc).pop_front() {
                Some(value) => {
                    self.value_stack.push(value);
                    self.pos = aft_pos;
                }
                None => self.pos = goto,
            }

            Instruction::BinaryOp { op } => {
                let b = self.value_stack.pop().unwrap();
                let a = self.value_stack.pop().unwrap();
                self.value_stack.push(ops::binary_op(mc, &*system, &a, &b, op)?);
                self.pos = aft_pos;
            }
            Instruction::VariadicOp { op, len } => {
                type CombineEmpty<'gc, C, S> = fn(&Mutation<'gc>) -> Result<Value<'gc, C, S>, ErrorCause<C, S>>;
                fn combine_as_binary<'gc, C: CustomTypes<S>, S: System<C>>(mc: &Mutation<'gc>, system: &S, values: &mut dyn Iterator<Item = &Value<'gc, C, S>>, combine_op: BinaryOp, singleton_op: UnaryOp, empty_case: CombineEmpty<'gc, C, S>) -> Result<Value<'gc, C, S>, ErrorCause<C, S>> {
                    match values.next() {
                        Some(first) => match values.next() {
                            Some(second) => {
                                let mut acc = ops::binary_op(mc, system, first, second, combine_op)?;
                                for item in values {
                                    acc = ops::binary_op(mc, system, &acc, item, combine_op)?;
                                }
                                Ok(acc)
                            }
                            None => ops::unary_op(mc, system, first, singleton_op),
                        }
                        None => empty_case(mc),
                    }
                }
                fn combine_by_relation<'gc, C: CustomTypes<S>, S: System<C>>(values: &mut dyn Iterator<Item = &Value<'gc, C, S>>, relation: Relation) -> Result<Value<'gc, C, S>, ErrorCause<C, S>> {
                    let mut res = match values.next() {
                        None => return Err(ErrorCause::EmptyList),
                        Some(x) => x,
                    };
                    for other in values {
                        if ops::check_relation(other, res, relation)? {
                            res = other;
                        }
                    }
                    Ok(res.clone())
                }

                type Combine<'gc, C, S, I> = fn(&Mutation<'gc>, &S, I) -> Result<Value<'gc, C, S>, ErrorCause<C, S>>;
                let combine: Combine<'gc, C, S, &mut dyn Iterator<Item = &Value<'gc, C, S>>> = match op {
                    VariadicOp::Add => |mc, system, values| combine_as_binary(mc, system, values, BinaryOp::Add, UnaryOp::ToNumber, |_| Ok(Number::new(0.0)?.into())),
                    VariadicOp::Mul => |mc, system, values| combine_as_binary(mc, system, values, BinaryOp::Mul, UnaryOp::ToNumber, |_| Ok(Number::new(1.0)?.into())),
                    VariadicOp::Min => |_, _, values| combine_by_relation(values, Relation::Less),
                    VariadicOp::Max => |_, _, values| combine_by_relation(values, Relation::Greater),
                    VariadicOp::StrCat => |_, _, values| {
                        let mut acc = String::new();
                        for item in values {
                            core::fmt::write(&mut acc, format_args!("{item}")).unwrap();
                        }
                        Ok(Rc::new(acc).into())
                    },
                    VariadicOp::MakeList => |mc, _, values| {
                        Ok(Gc::new(mc, RefLock::new(values.cloned().collect::<VecDeque<_>>())).into())
                    },
                    VariadicOp::ListCat => |mc, _, values| {
                        let mut acc = VecDeque::new();
                        for item in values {
                            acc.extend(item.as_list()?.borrow().iter().cloned());
                        }
                        Ok(Gc::new(mc, RefLock::new(acc)).into())
                    },
                };

                let res = match len {
                    VariadicLen::Fixed(len) => {
                        let stack_size = self.value_stack.len();
                        let res = combine(mc, &*system, &mut self.value_stack[stack_size - len..].iter())?;
                        self.value_stack.drain(stack_size - len..);
                        res
                    }
                    VariadicLen::Dynamic => {
                        let src = self.value_stack.pop().unwrap().as_list()?;
                        let src = src.borrow();
                        combine(mc, &*system, &mut src.iter())?
                    }
                };
                self.value_stack.push(res);
                self.pos = aft_pos;
            }
            Instruction::Cmp { relation } => {
                let b = self.value_stack.pop().unwrap();
                let a = self.value_stack.pop().unwrap();
                self.value_stack.push(ops::check_relation(&a, &b, relation)?.into());
                self.pos = aft_pos;
            }
            Instruction::Identical => {
                let b = self.value_stack.pop().unwrap();
                let a = self.value_stack.pop().unwrap();
                self.value_stack.push(ops::identical(&a, &b).into());
                self.pos = aft_pos;
            }
            Instruction::UnaryOp { op } => {
                let x = self.value_stack.pop().unwrap();
                self.value_stack.push(ops::unary_op(mc, &*system, &x, op)?);
                self.pos = aft_pos;
            }

            Instruction::DeclareLocal { var } => {
                self.call_stack.last_mut().unwrap().locals.define_if_undefined(var, || Shared::Unique(Number::new(0.0).unwrap().into()));
                self.pos = aft_pos;
            }
            Instruction::InitUpvar { var } => {
                let target = lookup_var!(var).get().clone();
                let target = target.as_string()?;
                let (parent_scope, current_scope) = match self.call_stack.as_mut_slice() {
                    [] => unreachable!(),
                    [_] => return Err(ErrorCause::UpvarAtRoot),
                    [.., x, y] => (x, y),
                };
                let parent_def = match parent_scope.locals.lookup_mut(target.as_ref()) {
                    Some(x) => x,
                    None => return Err(ErrorCause::UndefinedVariable { name: var.into() }),
                };
                current_scope.locals.define_or_redefine(var, parent_def.alias(mc));
                self.pos = aft_pos;
            }
            Instruction::Assign { var } => {
                let value = self.value_stack.pop().unwrap();
                lookup_var!(mut var).set(mc, value);
                self.pos = aft_pos;
            }
            Instruction::BinaryOpAssign { var, op } => {
                let b = self.value_stack.pop().unwrap();
                let a = lookup_var!(var).get().clone();
                lookup_var!(mut var).set(mc, ops::binary_op(mc, &*system, &a, &b, op)?);
                self.pos = aft_pos;
            }

            Instruction::Watcher { create, var } => {
                let watcher = Watcher {
                    entity: Gc::downgrade(self.call_stack.last().unwrap().entity),
                    name: var.to_owned(),
                    value: Gc::downgrade(lookup_var!(mut var).alias_inner(mc)),
                };
                self.pos = aft_pos;
                return Ok(ProcessStep::Watcher { create, watcher });
            }
            Instruction::Pause => {
                self.pos = aft_pos;
                return Ok(ProcessStep::Pause);
            }

            Instruction::Jump { to } => self.pos = to,
            Instruction::ConditionalJump { to, when } => {
                let value = self.value_stack.pop().unwrap();
                self.pos = if value.as_bool()? == when { to } else { aft_pos };
            }

            Instruction::Call { pos, tokens } => {
                let limit = global_context.settings.max_call_depth;
                if self.call_stack.len() >= limit {
                    return Err(ErrorCause::CallDepthLimit { limit });
                }

                let params = lossless_split(tokens).collect::<Vec<_>>();
                let params_count = params.len();

                let mut locals = SymbolTable::default();
                for (var, val) in iter::zip(params.into_iter(), self.value_stack.drain(self.value_stack.len() - params_count..)) {
                    locals.define_or_redefine(var, val.into());
                }

                self.call_stack.push(CallStackEntry {
                    called_from: self.pos,
                    return_to: aft_pos,
                    warp_counter: self.warp_counter,
                    value_stack_size: self.value_stack.len(),
                    handler_stack_size: self.handler_stack.len(),
                    entity: self.call_stack.last().unwrap().entity,
                    locals,
                });
                self.pos = pos;
            }
            Instruction::MakeClosure { pos, params, tokens } => {
                let mut tokens = lossless_split(tokens);
                let params = (&mut tokens).take(params).map(ToOwned::to_owned).collect::<Vec<_>>();
                let captures = tokens.collect::<Vec<_>>();

                let mut caps = SymbolTable::default();
                for &var in captures.iter() {
                    caps.define_or_redefine(var, lookup_var!(mut var).alias(mc));
                }
                self.value_stack.push(Gc::new(mc, RefLock::new(Closure { pos, params, captures: caps })).into());
                self.pos = aft_pos;
            }
            Instruction::CallClosure { new_entity, args } => {
                let (closure_pos, locals) = prep_call_closure(mc, &mut self.value_stack, args)?;
                let entity = match new_entity {
                    false => self.call_stack.last().unwrap().entity,
                    true => self.value_stack.pop().unwrap().as_entity()?,
                };

                self.call_stack.push(CallStackEntry {
                    called_from: self.pos,
                    return_to: aft_pos,
                    warp_counter: self.warp_counter,
                    value_stack_size: self.value_stack.len(),
                    handler_stack_size: self.handler_stack.len(),
                    locals,
                    entity,
                });
                self.pos = closure_pos;
            }
            Instruction::ForkClosure { args } => {
                let (closure_pos, locals) = prep_call_closure(mc, &mut self.value_stack, args)?;
                self.pos = aft_pos;
                return Ok(ProcessStep::Fork { pos: closure_pos, locals, entity: self.call_stack.last().unwrap().entity });
            }
            Instruction::Return => {
                let CallStackEntry { called_from, return_to, warp_counter, value_stack_size, handler_stack_size, .. } = self.call_stack.last().unwrap();
                let return_value = self.value_stack.pop().unwrap();

                self.pos = *return_to;
                self.warp_counter = *warp_counter;
                self.value_stack.drain(value_stack_size..);
                self.handler_stack.drain(handler_stack_size..);
                debug_assert_eq!(self.value_stack.len(), *value_stack_size);
                debug_assert_eq!(self.handler_stack.len(), *handler_stack_size);

                self.value_stack.push(return_value);

                if self.call_stack.len() > 1 {
                    self.call_stack.pop();
                } else {
                    debug_assert_eq!(self.value_stack.len(), 1);
                    debug_assert_eq!(*called_from, usize::MAX);
                    debug_assert_eq!(*return_to, usize::MAX);
                    debug_assert_eq!(*warp_counter, 0);
                    debug_assert_eq!(*value_stack_size, 0);
                    debug_assert_eq!(*handler_stack_size, 0);
                    return Ok(ProcessStep::Terminate { result: Some(self.value_stack.pop().unwrap()) });
                }
            }
            Instruction::PushHandler { pos, var } => {
                self.handler_stack.push(Handler {
                    pos,
                    var: var.to_owned(),
                    warp_counter: self.warp_counter,
                    call_stack_size: self.call_stack.len(),
                    value_stack_size: self.value_stack.len(),
                });
                self.pos = aft_pos;
            }
            Instruction::PopHandler => {
                self.handler_stack.pop().unwrap();
                self.pos = aft_pos;
            }
            Instruction::Throw => {
                let msg = self.value_stack.pop().unwrap().as_string()?.into_owned();
                return Err(ErrorCause::Custom { msg });
            }
            Instruction::CallRpc { tokens } => {
                let mut tokens = lossless_split(tokens);
                let service = tokens.next().unwrap().to_owned();
                let rpc = tokens.next().unwrap().to_owned();

                let arg_names = tokens.map(ToOwned::to_owned).collect::<Vec<_>>();
                let arg_count = arg_names.len();
                let args = iter::zip(arg_names, self.value_stack.drain(self.value_stack.len() - arg_count..)).collect();

                drop(global_context_raw);
                self.defer = Some(Defer::Request {
                    key: system.perform_request(mc, Request::Rpc { service, rpc, args }, self)?,
                    action: RequestAction::Rpc,
                    aft_pos
                });
            }
            Instruction::PushRpcError => {
                self.value_stack.push(self.last_rpc_error.clone().unwrap_or_else(|| empty_string().into()));
                self.pos = aft_pos;
            }
            Instruction::Syscall { len } => {
                let args = match len {
                    VariadicLen::Fixed(len) => {
                        let stack_size = self.value_stack.len();
                        self.value_stack.drain(stack_size - len..).collect()
                    }
                    VariadicLen::Dynamic => self.value_stack.pop().unwrap().as_list()?.borrow().iter().cloned().collect(),
                };
                let name = self.value_stack.pop().unwrap().as_string()?.into_owned();

                drop(global_context_raw);
                self.defer = Some(Defer::Request {
                    key: system.perform_request(mc, Request::Syscall { name, args }, self)?,
                    action: RequestAction::Syscall,
                    aft_pos
                });
            }
            Instruction::PushSyscallError => {
                self.value_stack.push(self.last_syscall_error.clone().unwrap_or_else(|| empty_string().into()));
                self.pos = aft_pos;
            }
            Instruction::SendLocalMessage { wait, target } => {
                let targets = match target {
                    false => None,
                    true => Some(match self.value_stack.pop().unwrap() {
                        Value::List(x) => x.borrow().iter().map(Value::as_entity).collect::<Result<_,_>>()?,
                        x => vec![x.as_entity()?],
                    }),
                };
                let msg_type = self.value_stack.pop().unwrap().as_string()?.into_owned();
                let barrier = match wait {
                    false => {
                        self.pos = aft_pos;
                        None
                    }
                    true => {
                        let barrier = Barrier::new();
                        self.defer = Some(Defer::Barrier { condition: barrier.get_condition(), aft_pos });
                        Some(barrier)
                    }
                };
                return Ok(ProcessStep::Broadcast { msg_type, barrier, targets });
            }
            Instruction::PushLocalMessage => {
                self.value_stack.push(self.last_message.clone().unwrap_or_else(|| empty_string().into()));
                self.pos = aft_pos;
            }
            Instruction::Print { style } => {
                let value = self.value_stack.pop().unwrap();
                let is_empty = match &value { Value::String(x) => x.is_empty(), _ => false };

                drop(global_context_raw);
                self.defer = Some(Defer::Command {
                    key: system.perform_command(mc, Command::Print { style, value: if is_empty { None } else { Some(value) } }, self)?,
                    aft_pos,
                });
            }
            Instruction::Ask => {
                let prompt = self.value_stack.pop().unwrap();
                let is_empty = match &prompt { Value::String(x) => x.is_empty(), _ => false };

                drop(global_context_raw);
                self.defer = Some(Defer::Request {
                    key: system.perform_request(mc, Request::Input { prompt: if is_empty { None } else { Some(prompt) } }, self)?,
                    action: RequestAction::Input,
                    aft_pos
                });
            }
            Instruction::PushAnswer => {
                self.value_stack.push(self.last_answer.clone().unwrap_or_else(|| empty_string().into()));
                self.pos = aft_pos;
            }
            Instruction::ResetTimer => {
                let t = system.time(Precision::Medium).to_arbitrary_ms()?;
                global_context.timer_start = t;
                self.pos = aft_pos;
            }
            Instruction::PushTimer => {
                let t = system.time(Precision::Low).to_arbitrary_ms()?;
                self.value_stack.push(Number::new(t.saturating_sub(global_context.timer_start) as f64 / 1000.0)?.into());
                self.pos = aft_pos;
            }
            Instruction::Sleep => {
                let ms = self.value_stack.pop().unwrap().as_number()?.get() * 1000.0;
                if ms <= 0.0 {
                    self.pos = aft_pos;
                    return Ok(ProcessStep::Yield);
                }
                self.defer = Some(Defer::Sleep { until: system.time(Precision::Medium).to_arbitrary_ms()? + ms as u64, aft_pos });
            }
            Instruction::PushRealTime { query } => {
                let t = system.time(Precision::High).to_real_local()?;
                let v = match query {
                    TimeQuery::UnixTimestampMs => (t.unix_timestamp_nanos() / 1000000) as f64,
                    TimeQuery::Year => t.year() as f64,
                    TimeQuery::Month => t.month() as u8 as f64,
                    TimeQuery::Date => t.day() as f64,
                    TimeQuery::DayOfWeek => t.date().weekday().number_from_sunday() as f64,
                    TimeQuery::Hour => t.hour() as f64,
                    TimeQuery::Minute => t.minute() as f64,
                    TimeQuery::Second => t.second() as f64,
                };
                self.value_stack.push(Number::new(v)?.into());
                self.pos = aft_pos;
            }
            Instruction::SendNetworkMessage { tokens, expect_reply } => {
                let mut tokens = lossless_split(tokens);
                let msg_type = tokens.next().unwrap();

                let targets = match self.value_stack.pop().unwrap() {
                    Value::String(x) => vec![x.as_str().to_owned()],
                    Value::List(x) => {
                        let x = x.borrow();
                        let mut res = Vec::with_capacity(x.len());
                        for val in x.iter() {
                            match val {
                                Value::String(x) => res.push(x.as_str().to_owned()),
                                x => return Err(ErrorCause::VariadicConversionError { got: x.get_type(), expected: Type::String }),
                            }
                        }
                        res
                    }
                    x => return Err(ErrorCause::VariadicConversionError { got: x.get_type(), expected: Type::String }),
                };

                let values = {
                    let field_names = tokens.map(ToOwned::to_owned).collect::<Vec<_>>();
                    let field_count = field_names.len();
                    iter::zip(field_names.into_iter(), self.value_stack.drain(self.value_stack.len() - field_count..)).map(|(k, v)| Ok((k, v.to_simple()?.into_netsblox_json()?))).collect::<Result<_,ErrorCause<C, S>>>()?
                };

                match system.send_message(msg_type.into(), values, targets, expect_reply)? {
                    Some(key) => self.defer = Some(Defer::MessageReply { key, aft_pos }),
                    None => self.pos = aft_pos,
                }
            }
            Instruction::SendNetworkReply => {
                let value = self.value_stack.pop().unwrap().to_simple()?.into_netsblox_json()?;
                if let Some(key) = self.reply_key.take() {
                    system.send_reply(key, value)?;
                }
                self.pos = aft_pos;
            }
            Instruction::PushProperty { prop } => {
                drop(global_context_raw);
                self.defer = Some(Defer::Request {
                    key: system.perform_request(mc, Request::Property { prop }, self)?,
                    action: RequestAction::Push,
                    aft_pos
                });
            }
            Instruction::SetProperty { prop } => {
                let value = self.value_stack.pop().unwrap();

                drop(global_context_raw);
                self.defer = Some(Defer::Command {
                    key: system.perform_command(mc, Command::SetProperty { prop, value }, self)?,
                    aft_pos,
                });
            }
            Instruction::ChangeProperty { prop } => {
                let delta = self.value_stack.pop().unwrap();

                drop(global_context_raw);
                self.defer = Some(Defer::Command {
                    key: system.perform_command(mc, Command::ChangeProperty { prop, delta }, self)?,
                    aft_pos,
                });
            }
            Instruction::PushCostume => {
                let entity = self.call_stack.last().unwrap().entity.borrow();
                self.value_stack.push(entity.costume.clone().map(|x| Value::Image(x)).unwrap_or_else(|| Value::String(empty_string())));
                self.pos = aft_pos;
            }
            Instruction::PushCostumeNumber => {
                let entity = self.call_stack.last().unwrap().entity.borrow();
                let res = entity.costume.as_ref().and_then(|x| entity.costume_list.iter().enumerate().find(|c| Rc::ptr_eq(x, &c.1.1))).map(|x| x.0 + 1).unwrap_or(0);
                self.value_stack.push(Value::Number(Number::new(res as f64)?));
                self.pos = aft_pos;
            }
            Instruction::PushCostumeList => {
                let entity = self.call_stack.last().unwrap().entity.borrow();
                self.value_stack.push(Value::List(Gc::new(mc, RefLock::new(entity.costume_list.iter().map(|x| Value::Image(x.1.clone())).collect()))));
                self.pos = aft_pos;
            }
            Instruction::SetCostume => {
                let mut entity_raw = self.call_stack.last().unwrap().entity.borrow_mut(mc);
                let entity = &mut *entity_raw;

                let new_costume = match self.value_stack.pop().unwrap() {
                    Value::Image(x) => Some(x),
                    Value::String(x) => match x.as_str() {
                        "" => None,
                        x => match entity.costume_list.iter().find(|&c| c.0 == x) {
                            Some(c) => Some(c.1.clone()),
                            None => return Err(ErrorCause::UndefinedCostume { name: x.into() }),
                        }
                    }
                    x => return Err(ErrorCause::ConversionError { got: x.get_type(), expected: Type::Image }),
                };

                if new_costume.as_ref().map(Rc::as_ptr) != entity.costume.as_ref().map(Rc::as_ptr) {
                    entity.costume = new_costume;

                    drop(entity_raw);
                    drop(global_context_raw);
                    self.defer = Some(Defer::Command {
                        key: system.perform_command(mc, Command::SetCostume, self)?,
                        aft_pos,
                    });
                } else {
                    self.pos = aft_pos;
                }
            }
            Instruction::NextCostume => {
                let mut entity_raw = self.call_stack.last().unwrap().entity.borrow_mut(mc);
                let entity = &mut *entity_raw;

                match entity.costume.as_ref().and_then(|x| entity.costume_list.iter().enumerate().find(|c| Rc::ptr_eq(x, &c.1.1))).map(|x| x.0) {
                    Some(idx) => {
                        let new_costume = Some(entity.costume_list[(idx + 1) % entity.costume_list.len()].1.clone());

                        if new_costume.as_ref().map(Rc::as_ptr) != entity.costume.as_ref().map(Rc::as_ptr) {
                            entity.costume = new_costume;

                            drop(entity_raw);
                            drop(global_context_raw);
                            self.defer = Some(Defer::Command {
                                key: system.perform_command(mc, Command::SetCostume, self)?,
                                aft_pos,
                            });
                        } else {
                            self.pos = aft_pos;
                        }
                    }
                    None => self.pos = aft_pos,
                }
            }
            Instruction::Clone => {
                let target_cell = self.value_stack.pop().unwrap().as_entity()?;
                let target = target_cell.borrow();
                let new_entity = Gc::new(mc, RefLock::new(Entity {
                    name: target.name.clone(),
                    sound_list: target.sound_list.clone(),
                    costume_list: target.costume_list.clone(),
                    costume: target.costume.clone(),
                    state: C::EntityState::from(EntityKind::Clone { parent: &*target }),
                    alive: true,
                    original: Some(target.original.unwrap_or(target_cell)),
                    fields: target.fields.clone(),
                }));
                self.value_stack.push(new_entity.into());
                self.pos = aft_pos;
                return Ok(ProcessStep::CreatedClone { new_entity });
            }
            Instruction::ClearEffects => {
                drop(global_context_raw);
                self.defer = Some(Defer::Command {
                    key: system.perform_command(mc, Command::ClearEffects, self)?,
                    aft_pos,
                });
            }
            Instruction::ClearDrawings => {
                drop(global_context_raw);
                self.defer = Some(Defer::Command {
                    key: system.perform_command(mc, Command::ClearDrawings, self)?,
                    aft_pos,
                });
            }
            Instruction::GotoXY => {
                let y = self.value_stack.pop().unwrap().as_number()?;
                let x = self.value_stack.pop().unwrap().as_number()?;

                drop(global_context_raw);
                self.defer = Some(Defer::Command {
                    key: system.perform_command(mc, Command::GotoXY { x, y }, self)?,
                    aft_pos,
                });
            }
            Instruction::Goto => match self.value_stack.pop().unwrap() {
                Value::List(target) => {
                    let target = target.borrow();
                    if target.len() != 2 { return Err(ErrorCause::InvalidListLength { expected: 2, got: target.len() }); }
                    let (x, y) = (target[0].as_number()?, target[1].as_number()?);

                    drop(global_context_raw);
                    self.defer = Some(Defer::Command {
                        key: system.perform_command(mc, Command::GotoXY { x, y }, self)?,
                        aft_pos,
                    });
                }
                Value::Entity(target) => {
                    let target = target.borrow();

                    drop(global_context_raw);
                    self.defer = Some(Defer::Command {
                        key: system.perform_command(mc, Command::GotoEntity { target: &*target }, self)?,
                        aft_pos,
                    });
                }
                target => return Err(ErrorCause::ConversionError { got: target.get_type(), expected: Type::Entity }),
            }
            Instruction::PointTowardsXY => {
                let x = self.value_stack.pop().unwrap().as_number()?;
                let y = self.value_stack.pop().unwrap().as_number()?;

                drop(global_context_raw);
                self.defer = Some(Defer::Command {
                    key: system.perform_command(mc, Command::PointTowardsXY { x, y }, self)?,
                    aft_pos,
                });
            }
            Instruction::PointTowards => match self.value_stack.pop().unwrap() {
                Value::List(target) => {
                    let target = target.borrow();
                    if target.len() != 2 { return Err(ErrorCause::InvalidListLength { expected: 2, got: target.len() }); }
                    let (x, y) = (target[0].as_number()?, target[1].as_number()?);

                    drop(global_context_raw);
                    self.defer = Some(Defer::Command {
                        key: system.perform_command(mc, Command::PointTowardsXY { x, y }, self)?,
                        aft_pos,
                    });
                }
                Value::Entity(target) => {
                    let target = target.borrow();

                    drop(global_context_raw);
                    self.defer = Some(Defer::Command {
                        key: system.perform_command(mc, Command::PointTowardsEntity { target: &*target }, self)?,
                        aft_pos,
                    });
                }
                target => return Err(ErrorCause::ConversionError { got: target.get_type(), expected: Type::Entity }),
            }
            Instruction::Forward => {
                let distance = self.value_stack.pop().unwrap().as_number()?;

                drop(global_context_raw);
                self.defer = Some(Defer::Command {
                    key: system.perform_command(mc, Command::Forward { distance }, self)?,
                    aft_pos,
                });
            }
            Instruction::UnknownBlock { name, args } => {
                let name = name.to_owned();
                let args = self.value_stack.drain(self.value_stack.len() - args..).collect();

                drop(global_context_raw);
                self.defer = Some(Defer::Request {
                    key: system.perform_request(mc, Request::UnknownBlock { name, args }, self)?,
                    action: RequestAction::Push,
                    aft_pos
                });
            }
        }

        Ok(ProcessStep::Normal)
    }
}

mod ops {
    use super::*;

    fn as_list<'gc, C: CustomTypes<S>, S: System<C>>(v: &Value<'gc, C, S>) -> Option<Gc<'gc, RefLock<VecDeque<Value<'gc, C, S>>>>> {
        v.as_list().ok()
    }
    fn as_matrix<'gc, C: CustomTypes<S>, S: System<C>>(v: &Value<'gc, C, S>) -> Option<Gc<'gc, RefLock<VecDeque<Value<'gc, C, S>>>>> {
        let vals = as_list(v)?;
        let good = match vals.borrow().front() {
            None => false,
            Some(first) => as_list(first).is_some(),
        };
        if good { Some(vals) } else { None }
    }

    pub(super) fn prep_index<C: CustomTypes<S>, S: System<C>>(index: &Value<'_, C, S>, len: usize) -> Result<usize, ErrorCause<C, S>> {
        let raw_index = index.as_number()?.get();
        let index = raw_index as i64;
        if index as f64 != raw_index { return Err(ErrorCause::IndexNotInteger { index: raw_index }) }
        if index < 1 || index > len as i64 { return Err(ErrorCause::IndexOutOfBounds { index, len }) }
        Ok(index as usize - 1)
    }
    pub(super) fn prep_rand_index<C: CustomTypes<S>, S: System<C>>(system: &S, len: usize) -> Result<usize, ErrorCause<C, S>> {
        if len == 0 { return Err(ErrorCause::IndexOutOfBounds { index: 1, len: 0 }) }
        Ok(system.rand(0..len))
    }

    pub(super) fn flatten<'gc, C: CustomTypes<S>, S: System<C>>(value: &Value<'gc, C, S>) -> Result<VecDeque<Value<'gc, C, S>>, ErrorCause<C, S>> {
        fn flatten_impl<'gc, C: CustomTypes<S>, S: System<C>>(value: &Value<'gc, C, S>, dest: &mut VecDeque<Value<'gc, C, S>>, cache: &mut BTreeSet<Identity<'gc, C, S>>) -> Result<(), ErrorCause<C, S>> {
            match value {
                Value::List(values) => {
                    let key = value.identity();
                    if !cache.insert(key) { return Err(ErrorCause::CyclicValue) }
                    for value in values.borrow().iter() {
                        flatten_impl(value, dest, cache)?;
                    }
                    cache.remove(&key);
                }
                _ => dest.push_back(value.clone()),
            }
            Ok(())
        }
        let mut res = Default::default();
        let mut cache = Default::default();
        flatten_impl(value, &mut res, &mut cache)?;
        debug_assert_eq!(cache.len(), 0);
        Ok(res)
    }
    pub(super) fn dimensions<C: CustomTypes<S>, S: System<C>>(value: &Value<'_, C, S>) -> Result<Vec<usize>, ErrorCause<C, S>> {
        fn dimensions_impl<'gc, C: CustomTypes<S>, S: System<C>>(value: &Value<'gc, C, S>, depth: usize, res: &mut Vec<usize>, cache: &mut BTreeSet<Identity<'gc, C, S>>) -> Result<(), ErrorCause<C, S>> {
            debug_assert!(depth <= res.len());

            if let Value::List(values) = value {
                if depth == res.len() { res.push(0); }

                let key = value.identity();
                if !cache.insert(key) { return Err(ErrorCause::CyclicValue) }

                let values = values.borrow();
                res[depth] = res[depth].max(values.len());
                for value in values.iter() {
                    dimensions_impl(value, depth + 1, res, cache)?;
                }

                cache.remove(&key);
            }
            Ok(())
        }
        let mut res = Default::default();
        let mut cache = Default::default();
        dimensions_impl(value, 0, &mut res, &mut cache)?;
        debug_assert_eq!(cache.len(), 0);
        Ok(res)
    }
    pub(super) fn reshape<'gc, C: CustomTypes<S>, S: System<C>>(mc: &Mutation<'gc>, src: &Value<'gc, C, S>, dims: &[usize]) -> Result<Value<'gc, C, S>, ErrorCause<C, S>> {
        let src = ops::flatten(src)?;
        if src.is_empty() {
            return Err(ErrorCause::EmptyList);
        }

        fn reshape_impl<'gc, C: CustomTypes<S>, S: System<C>>(mc: &Mutation<'gc>, src: &mut Cycle<VecDequeIter<Value<'gc, C, S>>>, dims: &[usize]) -> Value<'gc, C, S> {
            match dims {
                [] => src.next().unwrap().clone(),
                [first, rest @ ..] => Gc::new(mc, RefLock::new((0..*first).map(|_| reshape_impl(mc, src, rest)).collect::<VecDeque<_>>())).into(),
            }
        }
        Ok(reshape_impl(mc, &mut src.iter().cycle(), dims))
    }
    pub(super) fn columns<'gc, C: CustomTypes<S>, S: System<C>>(mc: &Mutation<'gc>, src: &Value<'gc, C, S>) -> Result<Value<'gc, C, S>, ErrorCause<C, S>> {
        let src = src.as_list()?;
        let src = src.borrow();

        let columns = src.iter().map(|x| match x {
            Value::List(x) => x.borrow().len(),
            _ => 1,
        }).max().unwrap_or(0);

        let mut res = VecDeque::with_capacity(columns);
        for column in 0..columns {
            let mut inner = VecDeque::with_capacity(src.len());
            for row in src.iter() {
                inner.push_back(match row {
                    Value::List(x) => x.borrow().get(column).cloned().unwrap_or_else(|| Value::String(empty_string())),
                    _ => row.clone(),
                });
            }
            res.push_back(Value::List(Gc::new(mc, RefLock::new(inner))));
        }
        Ok(Gc::new(mc, RefLock::new(res)).into())
    }
    pub(super) fn cartesian_product<'gc, C: CustomTypes<S>, S: System<C>>(mc: &Mutation<'gc>, sources: &[Gc<'gc, RefLock<VecDeque<Value<'gc, C, S>>>>]) -> VecDeque<Value<'gc, C, S>> {
        if sources.is_empty() { return Default::default() }

        fn cartesian_product_impl<'gc, C: CustomTypes<S>, S: System<C>>(mc: &Mutation<'gc>, res: &mut VecDeque<Value<'gc, C, S>>, partial: &mut VecDeque<Value<'gc, C, S>>, sources: &[Gc<'gc, RefLock<VecDeque<Value<'gc, C, S>>>>]) {
            match sources {
                [] => res.push_back(Gc::new(mc, RefLock::new(partial.clone())).into()),
                [first, rest @ ..] => for item in first.borrow().iter() {
                    partial.push_back(item.clone());
                    cartesian_product_impl(mc, res, partial, rest);
                    partial.pop_back();
                }
            }
        }
        let mut res = VecDeque::with_capacity(sources.iter().fold(1, |a, b| a * b.borrow().len()));
        let mut partial = VecDeque::with_capacity(sources.len());
        cartesian_product_impl(mc, &mut res, &mut partial, sources);
        res
    }
    pub(super) fn from_csv<'gc, C: CustomTypes<S>, S: System<C>>(mc: &Mutation<'gc>, value: &str) -> Result<VecDeque<Value<'gc, C, S>>, ErrorCause<C, S>> {
        let mut src = value.chars();
        let mut table = VecDeque::new();

        if value.is_empty() { return Ok(table); }

        'next_vector: loop {
            let mut vector = VecDeque::new();

            'next_scalar: loop {
                let mut scalar = String::new();
                let mut in_quote = false;

                loop {
                    macro_rules! finish {
                        (scalar) => {{
                            vector.push_back(Value::String(Rc::new(scalar)));
                            continue 'next_scalar;
                        }};
                        (vector) => {{
                            vector.push_back(Rc::new(scalar).into());
                            table.push_back(Gc::new(mc, RefLock::new(vector)).into());
                            continue 'next_vector;
                        }};
                        (table) => {{
                            vector.push_back(Rc::new(scalar).into());
                            table.push_back(Gc::new(mc, RefLock::new(vector)).into());
                            return Ok(table);
                        }}
                    }

                    match src.next() {
                        Some('"') if !in_quote => match scalar.is_empty() {
                            true => in_quote = true,
                            false => return Err(ErrorCause::NotCsv { value: value.to_owned() }),
                        }
                        Some('"') if in_quote => match src.next() {
                            Some('"') => scalar.push('"'),
                            Some(',') => finish!(scalar),
                            Some('\n') => finish!(vector),
                            None => finish!(table),
                            Some(_) => return Err(ErrorCause::NotCsv { value: value.to_owned() }),
                        }
                        Some(',') if !in_quote => finish!(scalar),
                        Some('\n') if !in_quote => finish!(vector),
                        Some(x) => scalar.push(x),
                        None => match in_quote {
                            true => return Err(ErrorCause::NotCsv { value: value.to_owned() }),
                            false => finish!(table),
                        }
                    }
                }
            }
        }
    }
    pub(super) fn to_csv<C: CustomTypes<S>, S: System<C>>(value: &Value<C, S>) -> Result<String, ErrorCause<C, S>> {
        let value = value.as_list()?;
        let value = value.borrow();

        fn process_scalar(res: &mut String, value: &str) {
            let needs_quotes = value.chars().any(|x| matches!(x, '"' | ',' | '\n'));

            if needs_quotes { res.push('"'); }
            for ch in value.chars() {
                match ch {
                    '"' => res.push_str("\"\""),
                    x => res.push(x),
                }
            }
            if needs_quotes { res.push('"'); }
        }
        fn process_vector<C: CustomTypes<S>, S: System<C>>(res: &mut String, value: &VecDeque<Value<C, S>>) -> Result<(), ErrorCause<C, S>> {
            for (i, x) in value.iter().enumerate() {
                if i != 0 { res.push(','); }
                process_scalar(res, x.as_string()?.as_ref())
            }
            Ok(())
        }
        fn process_table<C: CustomTypes<S>, S: System<C>>(res: &mut String, value: &VecDeque<Value<C, S>>) -> Result<(), ErrorCause<C, S>> {
            for (i, x) in value.iter().enumerate() {
                if i != 0 { res.push('\n'); }
                process_vector(res, &*x.as_list()?.borrow())?;
            }
            Ok(())
        }

        let mut res = String::new();
        let table_mode = value.iter().any(|x| matches!(x, Value::List(..)));
        let f = if table_mode { process_table } else { process_vector };
        f(&mut res, &*value)?;
        Ok(res)
    }

    fn binary_op_impl<'gc, C: CustomTypes<S>, S: System<C>>(mc: &Mutation<'gc>, system: &S, a: &Value<'gc, C, S>, b: &Value<'gc, C, S>, matrix_mode: bool, cache: &mut BTreeMap<(Identity<'gc, C, S>, Identity<'gc, C, S>, bool), Value<'gc, C, S>>, scalar_op: fn(&Mutation<'gc>, &S, &Value<'gc, C, S>, &Value<'gc, C, S>) -> Result<Value<'gc, C, S>, ErrorCause<C, S>>) -> Result<Value<'gc, C, S>, ErrorCause<C, S>> {
        let cache_key = (a.identity(), b.identity(), matrix_mode);
        Ok(match cache.get(&cache_key) {
            Some(x) => x.clone(),
            None => {
                let checker = if matrix_mode { as_matrix } else { as_list };
                match (checker(a), checker(b)) {
                    (Some(a), Some(b)) => {
                        let (a, b) = (a.borrow(), b.borrow());
                        let real_res: Value<C, S> = Gc::new(mc, RefLock::new(VecDeque::with_capacity(a.len().min(b.len())))).into();
                        cache.insert(cache_key, real_res.clone());
                        let res = as_list(&real_res).unwrap();
                        let mut res = res.borrow_mut(mc);
                        for (a, b) in iter::zip(&*a, &*b) {
                            res.push_back(binary_op_impl(mc, system, a, b, matrix_mode, cache, scalar_op)?);
                        }
                        real_res
                    }
                    (Some(a), None) => {
                        let a = a.borrow();
                        let real_res: Value<C, S> = Gc::new(mc, RefLock::new(VecDeque::with_capacity(a.len()))).into();
                        cache.insert(cache_key, real_res.clone());
                        let res = as_list(&real_res).unwrap();
                        let mut res = res.borrow_mut(mc);
                        for a in &*a {
                            res.push_back(binary_op_impl(mc, system, a, b, matrix_mode, cache, scalar_op)?);
                        }
                        real_res
                    }
                    (None, Some(b)) => {
                        let b = b.borrow();
                        let real_res: Value<C, S> = Gc::new(mc, RefLock::new(VecDeque::with_capacity(b.len()))).into();
                        cache.insert(cache_key, real_res.clone());
                        let res = as_list(&real_res).unwrap();
                        let mut res = res.borrow_mut(mc);
                        for b in &*b {
                            res.push_back(binary_op_impl(mc, system, a, b, matrix_mode, cache, scalar_op)?);
                        }
                        real_res
                    }
                    (None, None) => if matrix_mode { binary_op_impl(mc, system, a, b, false, cache, scalar_op)? } else { scalar_op(mc, system, a, b)? }
                }
            }
        })
    }
    pub(super) fn binary_op<'gc, 'a, C: CustomTypes<S>, S: System<C>>(mc: &Mutation<'gc>, system: &S, a: &'a Value<'gc, C, S>, b: &'a Value<'gc, C, S>, op: BinaryOp) -> Result<Value<'gc, C, S>, ErrorCause<C, S>> {
        let mut cache = Default::default();
        match op {
            BinaryOp::Add       => binary_op_impl(mc, system, a, b, true, &mut cache, |_, _, a, b| Ok(a.as_number()?.add(b.as_number()?)?.into())),
            BinaryOp::Sub       => binary_op_impl(mc, system, a, b, true, &mut cache, |_, _, a, b| Ok(a.as_number()?.sub(b.as_number()?)?.into())),
            BinaryOp::Mul       => binary_op_impl(mc, system, a, b, true, &mut cache, |_, _, a, b| Ok(a.as_number()?.mul(b.as_number()?)?.into())),
            BinaryOp::Div       => binary_op_impl(mc, system, a, b, true, &mut cache, |_, _, a, b| Ok(a.as_number()?.div(b.as_number()?)?.into())),
            BinaryOp::Pow       => binary_op_impl(mc, system, a, b, true, &mut cache, |_, _, a, b| Ok(a.as_number()?.powf(b.as_number()?)?.into())),
            BinaryOp::Log       => binary_op_impl(mc, system, a, b, true, &mut cache, |_, _, a, b| Ok(b.as_number()?.log(a.as_number()?)?.into())),
            BinaryOp::Atan2     => binary_op_impl(mc, system, a, b, true, &mut cache, |_, _, a, b| Ok(a.as_number()?.atan2(b.as_number()?)?.to_degrees()?.into())),

            BinaryOp::StrGet => binary_op_impl(mc, system, a, b, true, &mut cache, |_, _, a, b| {
                let string = b.as_string()?;
                let index = prep_index(a, string.chars().count())?;
                Ok(Rc::new(string.chars().nth(index).unwrap().to_string()).into())
            }),

            BinaryOp::Mod => binary_op_impl(mc, system, a, b, true, &mut cache, |_, _, a, b| {
                let (a, b) = (a.as_number()?.get(), b.as_number()?.get());
                Ok(Number::new(util::modulus(a, b))?.into())
            }),
            BinaryOp::SplitBy => binary_op_impl(mc, system, a, b, true, &mut cache, |mc, _, a, b| {
                let (text, pattern) = (a.as_string()?, b.as_string()?);
                Ok(Gc::new(mc, RefLock::new(text.split(pattern.as_ref()).map(|x| Rc::new(x.to_owned()).into()).collect::<VecDeque<_>>())).into())
            }),

            BinaryOp::Range => binary_op_impl(mc, system, a, b, true, &mut cache, |mc, _, a, b| {
                let (mut a, b) = (a.as_number()?.get(), b.as_number()?.get());
                let mut res = VecDeque::new();
                if a.is_finite() && b.is_finite() {
                    if a <= b {
                        while a <= b {
                            res.push_back(Number::new(a)?.into());
                            a += 1.0;
                        }
                    } else {
                        while a >= b {
                            res.push_back(Number::new(a)?.into());
                            a -= 1.0;
                        }
                    }
                }
                Ok(Gc::new(mc, RefLock::new(res)).into())
            }),
            BinaryOp::Random => binary_op_impl(mc, system, a, b, true, &mut cache, |_, system, a, b| {
                let (mut a, mut b) = (a.as_number()?.get(), b.as_number()?.get());
                if a > b { (a, b) = (b, a); }
                let res = if a == libm::round(a) && b == libm::round(b) {
                    let (a, b) = (a as i64, b as i64);
                    system.rand(a..=b) as f64
                } else {
                    system.rand(a..=b)
                };
                Ok(Number::new(res)?.into())
            }),
        }
    }

    fn unary_op_impl<'gc, C: CustomTypes<S>, S: System<C>>(mc: &Mutation<'gc>, system: &S, x: &Value<'gc, C, S>, cache: &mut BTreeMap<Identity<'gc, C, S>, Value<'gc, C, S>>, scalar_op: &dyn Fn(&Mutation<'gc>, &S, &Value<'gc, C, S>) -> Result<Value<'gc, C, S>, ErrorCause<C, S>>) -> Result<Value<'gc, C, S>, ErrorCause<C, S>> {
        let cache_key = x.identity();
        Ok(match cache.get(&cache_key) {
            Some(x) => x.clone(),
            None => match as_list(x) {
                Some(x) => {
                    let x = x.borrow();
                    let real_res: Value<C, S> = Gc::new(mc, RefLock::new(VecDeque::with_capacity(x.len()))).into();
                    cache.insert(cache_key, real_res.clone());
                    let res = as_list(&real_res).unwrap();
                    let mut res = res.borrow_mut(mc);
                    for x in &*x {
                        res.push_back(unary_op_impl(mc, system, x, cache, scalar_op)?);
                    }
                    cache.remove(&cache_key);
                    real_res
                }
                None => scalar_op(mc, system, x)?,
            }
        })
    }
    pub(super) fn unary_op<'gc, C: CustomTypes<S>, S: System<C>>(mc: &Mutation<'gc>, system: &S, x: &Value<'gc, C, S>, op: UnaryOp) -> Result<Value<'gc, C, S>, ErrorCause<C, S>> {
        let mut cache = Default::default();
        match op {
            UnaryOp::ToNumber => unary_op_impl(mc, system, x, &mut cache, &|_, _, x| Ok(x.as_number()?.into())),
            UnaryOp::Not      => unary_op_impl(mc, system, x, &mut cache, &|_, _, x| Ok((!x.as_bool()?).into())),
            UnaryOp::Abs      => unary_op_impl(mc, system, x, &mut cache, &|_, _, x| Ok(x.as_number()?.abs()?.into())),
            UnaryOp::Neg      => unary_op_impl(mc, system, x, &mut cache, &|_, _, x| Ok(x.as_number()?.neg()?.into())),
            UnaryOp::Sqrt     => unary_op_impl(mc, system, x, &mut cache, &|_, _, x| Ok(x.as_number()?.sqrt()?.into())),
            UnaryOp::Round    => unary_op_impl(mc, system, x, &mut cache, &|_, _, x| Ok(x.as_number()?.round()?.into())),
            UnaryOp::Floor    => unary_op_impl(mc, system, x, &mut cache, &|_, _, x| Ok(x.as_number()?.floor()?.into())),
            UnaryOp::Ceil     => unary_op_impl(mc, system, x, &mut cache, &|_, _, x| Ok(x.as_number()?.ceil()?.into())),
            UnaryOp::Sin      => unary_op_impl(mc, system, x, &mut cache, &|_, _, x| Ok(Number::new(libm::sin(x.as_number()?.get().to_radians()))?.into())),
            UnaryOp::Cos      => unary_op_impl(mc, system, x, &mut cache, &|_, _, x| Ok(Number::new(libm::cos(x.as_number()?.get().to_radians()))?.into())),
            UnaryOp::Tan      => unary_op_impl(mc, system, x, &mut cache, &|_, _, x| Ok(Number::new(libm::tan(x.as_number()?.get().to_radians()))?.into())),
            UnaryOp::Asin     => unary_op_impl(mc, system, x, &mut cache, &|_, _, x| Ok(Number::new(libm::asin(x.as_number()?.get()).to_degrees())?.into())),
            UnaryOp::Acos     => unary_op_impl(mc, system, x, &mut cache, &|_, _, x| Ok(Number::new(libm::acos(x.as_number()?.get()).to_degrees())?.into())),
            UnaryOp::Atan     => unary_op_impl(mc, system, x, &mut cache, &|_, _, x| Ok(Number::new(libm::atan(x.as_number()?.get()).to_degrees())?.into())),
            UnaryOp::StrLen   => unary_op_impl(mc, system, x, &mut cache, &|_, _, x| Ok(Number::new(x.as_string()?.chars().count() as f64)?.into())),

            UnaryOp::StrGetLast => unary_op_impl(mc, system, x, &mut cache, &|_, _, x| match x.as_string()?.chars().next_back() {
                Some(ch) => Ok(Rc::new(ch.to_string()).into()),
                None => Err(ErrorCause::IndexOutOfBounds { index: 1, len: 0 }),
            }),
            UnaryOp::StrGetRandom => unary_op_impl(mc, system, x, &mut cache, &|_, system, x| {
                let x = x.as_string()?;
                let i = prep_rand_index(system, x.chars().count())?;
                Ok(Rc::new(x.chars().nth(i).unwrap().to_string()).into())
            }),

            UnaryOp::SplitLetter => unary_op_impl(mc, system, x, &mut cache, &|mc, _, x| {
                Ok(Gc::new(mc, RefLock::new(x.as_string()?.chars().map(|x| Rc::new(x.to_string()).into()).collect::<VecDeque<_>>())).into())
            }),
            UnaryOp::SplitWord => unary_op_impl(mc, system, x, &mut cache, &|mc, _, x| {
                Ok(Gc::new(mc, RefLock::new(x.as_string()?.split_whitespace().map(|x| Rc::new(x.to_owned()).into()).collect::<VecDeque<_>>())).into())
            }),
            UnaryOp::SplitTab => unary_op_impl(mc, system, x, &mut cache, &|mc, _, x| {
                Ok(Gc::new(mc, RefLock::new(x.as_string()?.split('\t').map(|x| Rc::new(x.to_owned()).into()).collect::<VecDeque<_>>())).into())
            }),
            UnaryOp::SplitCR => unary_op_impl(mc, system, x, &mut cache, &|mc, _, x| {
                Ok(Gc::new(mc, RefLock::new(x.as_string()?.split('\r').map(|x| Rc::new(x.to_owned()).into()).collect::<VecDeque<_>>())).into())
            }),
            UnaryOp::SplitLF => unary_op_impl(mc, system, x, &mut cache, &|mc, _, x| {
                Ok(Gc::new(mc, RefLock::new(x.as_string()?.lines().map(|x| Rc::new(x.to_owned()).into()).collect::<VecDeque<_>>())).into())
            }),
            UnaryOp::SplitCsv => unary_op_impl(mc, system, x, &mut cache, &|mc, _, x| {
                let value = from_csv(mc, x.as_string()?.as_ref())?;
                Ok(Gc::new(mc, RefLock::new(value)).into())
            }),
            UnaryOp::SplitJson => unary_op_impl(mc, system, x, &mut cache, &|mc, _, x| {
                let value = x.as_string()?;
                match parse_json::<Json>(&value) {
                    Ok(json) => Ok(Value::from_simple(mc, SimpleValue::from_json(json)?)),
                    Err(_) => Err(ErrorCause::NotJson { value: value.into_owned() }),
                }
            }),

            UnaryOp::UnicodeToChar => unary_op_impl(mc, system, x, &mut cache, &|_, _, x| {
                let fnum = x.as_number()?.get();
                if fnum < 0.0 || fnum > u32::MAX as f64 { return Err(ErrorCause::InvalidUnicode { value: fnum }) }
                let num = fnum as u32;
                if num as f64 != fnum { return Err(ErrorCause::InvalidUnicode { value: fnum }) }
                match char::from_u32(num) {
                    Some(ch) => Ok(Rc::new(ch.to_string()).into()),
                    None => Err(ErrorCause::InvalidUnicode { value: fnum }),
                }
            }),
            UnaryOp::CharToUnicode => unary_op_impl(mc, system, x, &mut cache, &|mc, _, x| {
                let src = x.as_string()?;
                let values: VecDeque<_> = src.chars().map(|ch| Ok(Number::new(ch as u32 as f64)?.into())).collect::<Result<_, NumberError>>()?;
                Ok(match values.len() {
                    1 => values.into_iter().next().unwrap(),
                    _ => Gc::new(mc, RefLock::new(values)).into(),
                })
            }),
        }
    }
    pub(super) fn index_list<'gc, C: CustomTypes<S>, S: System<C>>(mc: &Mutation<'gc>, system: &S, list: &Value<'gc, C, S>, index: &Value<'gc, C, S>) -> Result<Value<'gc, C, S>, ErrorCause<C, S>> {
        let list = list.as_list()?;
        let list = list.borrow();
        unary_op_impl(mc, system, index, &mut Default::default(), &|_, _, x| Ok(list[prep_index(x, list.len())?].clone()))
    }

    fn cmp_impl<'gc, C: CustomTypes<S>, S: System<C>>(a: &Value<'gc, C, S>, b: &Value<'gc, C, S>, cache: &mut BTreeMap<(Identity<'gc, C, S>, Identity<'gc, C, S>), Option<Option<Ordering>>>) -> Result<Option<Ordering>, ErrorCause<C, S>> {
        let key = (a.identity(), b.identity());
        match cache.get(&key) {
            Some(Some(x)) => return Ok(*x),
            Some(None) => return Err(ErrorCause::CyclicValue),
            None => { cache.insert(key, None); }
        }

        let res = match (a, b) {
            (Value::Bool(a), Value::Bool(b)) => a.cmp(b).into(),
            (Value::Bool(_), _) | (_, Value::Bool(_)) => None,

            (Value::Number(a), Value::Number(b)) => a.cmp(b).into(),
            (Value::String(a), Value::String(b)) => match Value::<C, S>::parse_number(a).and_then(|a| Value::<C, S>::parse_number(b).map(|b| (a, b))) {
                Some((a, b)) => a.cmp(&b).into(),
                None => UniCase::new(a.as_str()).cmp(&UniCase::new(b.as_str())).into(),
            }
            (Value::Number(a), Value::String(b)) => match Value::<C, S>::parse_number(b) {
                Some(b) => a.cmp(&b).into(),
                None => UniCase::new(&a.to_string()).cmp(&UniCase::new(b.as_ref())).into(),
            }
            (Value::String(a), Value::Number(b)) => match Value::<C, S>::parse_number(a) {
                Some(a) => a.cmp(b).into(),
                None => UniCase::new(a.as_ref()).cmp(&UniCase::new(&b.to_string())).into(),
            }
            (Value::Number(_), _) | (_, Value::Number(_)) => None,
            (Value::String(_), _) | (_, Value::String(_)) => None,

            (Value::List(a), Value::List(b)) => {
                let (a, b) = (a.borrow(), b.borrow());
                let (mut a, mut b) = (a.iter(), b.iter());
                loop {
                    match (a.next(), b.next()) {
                        (Some(a), Some(b)) => match cmp_impl(a, b, cache)? {
                            Some(Ordering::Equal) => (),
                            x => break x,
                        }
                        (None, Some(_)) => break Some(Ordering::Less),
                        (Some(_), None) => break Some(Ordering::Greater),
                        (None, None) => break Some(Ordering::Equal),
                    }
                }
            }
            (Value::List(_), _) | (_, Value::List(_)) => None,

            (Value::Image(a), Value::Image(b)) => if Rc::ptr_eq(a, b) { Some(Ordering::Equal) } else { None },
            (Value::Image(_), _) | (_, Value::Image(_)) => None,

            (Value::Audio(a), Value::Audio(b)) => if Rc::ptr_eq(a, b) { Some(Ordering::Equal) } else { None },
            (Value::Audio(_), _) | (_, Value::Audio(_)) => None,

            (Value::Closure(a), Value::Closure(b)) => if a.as_ptr() == b.as_ptr() { Some(Ordering::Equal) } else { None },
            (Value::Closure(_), _) | (_, Value::Closure(_)) => None,

            (Value::Entity(a), Value::Entity(b)) => if a.as_ptr() == b.as_ptr() { Some(Ordering::Equal) } else { None },
            (Value::Entity(_), _) | (_, Value::Entity(_)) => None,

            (Value::Native(a), Value::Native(b)) => if Rc::ptr_eq(a, b) { Some(Ordering::Equal) } else { None },
        };

        debug_assert_eq!(cache.get(&key).cloned(), Some(None));
        *cache.get_mut(&key).unwrap() = Some(res);
        Ok(res)
    }
    pub(super) fn cmp<'gc, C: CustomTypes<S>, S: System<C>>(a: &Value<'gc, C, S>, b: &Value<'gc, C, S>) -> Result<Option<Ordering>, ErrorCause<C, S>> {
        cmp_impl(a, b, &mut Default::default())
    }

    pub(super) fn check_relation<'gc, C: CustomTypes<S>, S: System<C>>(a: &Value<'gc, C, S>, b: &Value<'gc, C, S>, relation: Relation) -> Result<bool, ErrorCause<C, S>> {
        let ord = cmp(a, b)?;
        Ok(match relation {
            Relation::Equal => ord == Some(Ordering::Equal),
            Relation::NotEqual => ord != Some(Ordering::Equal),
            _ => match ord {
                Some(ord) => match relation {
                    Relation::Equal | Relation::NotEqual => unreachable!(),
                    Relation::Less => ord == Ordering::Less,
                    Relation::LessEq => ord != Ordering::Greater,
                    Relation::Greater => ord == Ordering::Greater,
                    Relation::GreaterEq => ord != Ordering::Less,
                }
                None => return Err(ErrorCause::Incomparable { left: a.get_type(), right: b.get_type() }),
            }
        })
    }

    pub(super) fn identical<'gc, C: CustomTypes<S>, S: System<C>>(a: &Value<'gc, C, S>, b: &Value<'gc, C, S>) -> bool {
        match (a, b) {
            (Value::Bool(a), Value::Bool(b)) => a == b,
            (Value::Bool(_), _) | (_, Value::Bool(_)) => false,

            (Value::Number(a), Value::Number(b)) => a.get().to_bits() == b.get().to_bits(),
            (Value::Number(_), _) | (_, Value::Number(_)) => false,

            (Value::String(a), Value::String(b)) => a == b,
            (Value::String(_), _) | (_, Value::String(_)) => false,

            (Value::Image(a), Value::Image(b)) => Rc::ptr_eq(a, b),
            (Value::Image(_), _) | (_, Value::Image(_)) => false,

            (Value::Audio(a), Value::Audio(b)) => Rc::ptr_eq(a, b),
            (Value::Audio(_), _) | (_, Value::Audio(_)) => false,

            (Value::Closure(a), Value::Closure(b)) => a.as_ptr() == b.as_ptr(),
            (Value::Closure(_), _) | (_, Value::Closure(_)) => false,

            (Value::List(a), Value::List(b)) => a.as_ptr() == b.as_ptr(),
            (Value::List(_), _) | (_, Value::List(_)) => false,

            (Value::Entity(a), Value::Entity(b)) => a.as_ptr() == b.as_ptr(),
            (Value::Entity(_), _) | (_, Value::Entity(_)) => false,

            (Value::Native(a), Value::Native(b)) => Rc::ptr_eq(a, b),
        }
    }

    pub(super) fn find<'gc, C: CustomTypes<S>, S: System<C>>(list: Gc<'gc, RefLock<VecDeque<Value<'gc, C, S>>>>, value: &Value<'gc, C, S>) -> Result<Option<usize>, ErrorCause<C, S>> {
        let list = list.borrow();
        for (i, x) in list.iter().enumerate() {
            if cmp(x, value)? == Some(Ordering::Equal) {
                return Ok(Some(i));
            }
        }
        Ok(None)
    }
}
