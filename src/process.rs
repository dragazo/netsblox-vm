use std::prelude::v1::*;
use std::rc::Rc;

use crate::bytecode::*;
use crate::runtime::*;

/// Result of stepping through a [`Process`].
pub enum StepResult {
    /// The process was not running.
    Idle,
    /// The process executed an instruction successfully and does not need to yield.
    Normal,
    /// The process has signaled a yield point so that other code can run.
    /// Many yield results may occur back-to-back, such as while awaiting an asynchronous result.
    Yield,
    /// The process has terminated with the given state.
    /// If an error was encountered during execution, return `Err(e)` where `e` is a string describing the error.
    /// Otherwise, `Ok(v)` is returned to denote success, where `v` is `Some(x)` for a return value of `x`,
    /// or `None` to denote that the script requested an immediate abort.
    Terminate(Result<Option<Value>, String>),
}
/// A [`ByteCode`] execution primitive.
pub struct Process {
    code: Rc<ByteCode>,
    pos: usize,
    running: bool,
    value_stack: Vec<Value>,
    context_stack: Vec<SymbolTable>,
}
impl Process {
    /// Creates a new process with the given code.
    /// The new process is initialized into an idle state.
    pub fn new(code: Rc<ByteCode>) -> Self {
        Self {
            code,
            pos: 0,
            running: false,
            value_stack: vec![],
            context_stack: vec![],
        }
    }
    /// Checks if the process is currently running.
    pub fn is_running(&self) -> bool {
        self.running
    }
    /// Prepares the process to execute code at the given [`ByteCode`] position
    /// and with the given context of local variables.
    /// Any previous process state is wiped when performing this action.
    pub fn initialize(&mut self, start_pos: usize, context: SymbolTable) {
        self.pos = start_pos;
        self.running = true;
        self.value_stack.clear();
        self.context_stack.clear();
        self.context_stack.push(context);
        self.context_stack.push(Default::default());
    }
    /// Executes a single instruction with the given execution context.
    pub fn step(&mut self, ref_pool: &mut RefPool, globals: &mut SymbolTable, fields: &mut SymbolTable) -> StepResult {
        if !self.running { return StepResult::Idle; }
        let locals = self.context_stack.last_mut().unwrap();
        let mut context = [globals, fields, locals];
        let mut context = LookupGroup(&mut context);

        match &self.code.0[self.pos] {
            Instruction::Assign { vars } => {
                let value = self.value_stack.pop().unwrap();
                for var in vars {
                    *context.lookup_mut(var).unwrap() = value;
                }
            }
            Instruction::Return => {
                debug_assert!(self.context_stack.len() >= 2);
                self.context_stack.pop();
                if self.context_stack.len() == 1 {
                    debug_assert_eq!(self.value_stack.len(), 1);
                    self.running = false;
                    return StepResult::Terminate(Ok(Some(self.value_stack.pop().unwrap())));
                }
            }

            Instruction::PushValue { value } => self.value_stack.push(Value::from_ast(value, ref_pool)),
            Instruction::PopValue => { self.value_stack.pop().unwrap(); }
        }

        StepResult::Normal
    }
}
