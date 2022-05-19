//! Utilities for executing generated [`ByteCode`](crate::bytecode::ByteCode).

use std::prelude::v1::*;
use std::rc::Rc;

use crate::bytecode::*;
use crate::runtime::*;

/// An execution error from a [`Process`] (see [`StepResult`]).
/// 
/// Each error variant contains a field called `pos` which is the [`ByteCode`] index at the time of the error.
/// By using the [`Locations`] information from [`ByteCode::compile`], it is possible to determine which
/// script/function generated the error.
#[derive(Debug)]
pub enum ExecError {
    /// A variable lookup operation failed.
    /// `name` holds the name of the variable that was expected.
    UndefinedVariable { name: String, pos: usize },
}
/// Result of stepping through a [`Process`].
pub enum StepResult {
    /// The process was not running.
    Idle,
    /// The process executed an instruction successfully and does not need to yield.
    Normal,
    /// The process has signaled a yield point so that other code can run.
    /// Many yield results may occur back-to-back, such as while awaiting an asynchronous result.
    /// 
    /// Yielding is primarily needed for executing an entire semi-concurrent project so that scripts can appear to run simultaneously.
    /// If instead you are explicitly only using a single sandboxed process, this can be treated equivalently to [`StepResult::Normal`].
    Yield,
    /// The process has terminated with the given state.
    /// If an error was encountered during execution, returns `Err(e)` where `e` is en enum describing the error.
    /// Otherwise, `Ok(v)` is returned to denote success, where `v` is `Some(x)` for a return value of `x`,
    /// or `None` to denote that the script requested an immediate abort.
    Terminate(Result<Option<Value>, ExecError>),
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
    call_stack: Vec<usize>,
    value_stack: Vec<Value>,
    context_stack: Vec<SymbolTable>,
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
            context_stack: vec![],
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
        self.value_stack.clear();
        self.context_stack.clear();
        self.context_stack.push(context);
        self.context_stack.push(Default::default());
    }
    /// Executes a single instruction with the given execution context.
    /// The return value can be used to determine what additional effects the script has requested,
    /// as well as retrieving the return value or execution error in the event that the process terminates (see [`StepResult`]).
    pub fn step(&mut self, ref_pool: &mut RefPool, globals: &mut SymbolTable, fields: &mut SymbolTable) -> StepResult {
        if !self.running { return StepResult::Idle; }
        let locals = self.context_stack.last_mut().unwrap();
        let mut context = [globals, fields, locals];
        let mut context = LookupGroup(&mut context);

        match &self.code.0[self.pos] {
            Instruction::Assign { vars } => {
                let value = self.value_stack.pop().unwrap();
                for var in vars {
                    match context.lookup_mut(&var) {
                        Some(x) => *x = value,
                        None => context.set_or_define_last_context(&var, value),
                    }
                }
                self.pos += 1;
            }
            Instruction::Return => {
                match self.call_stack.pop() {
                    Some(v) => self.pos = v,
                    None => {
                        debug_assert_eq!(self.value_stack.len(), 1);
                        self.running = false;
                        return StepResult::Terminate(Ok(Some(self.value_stack.pop().unwrap())));
                    }
                }
            }

            Instruction::PushValue { value } => {
                self.value_stack.push(Value::from_ast(value, ref_pool));
                self.pos += 1;
            }
            Instruction::PopValue => {
                self.value_stack.pop().unwrap();
                self.pos += 1;
            }
        }

        StepResult::Normal
    }
}
