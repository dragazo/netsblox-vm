//! Utilities for executing generated [`ByteCode`](crate::bytecode::ByteCode).

use std::prelude::v1::*;
use std::rc::Rc;
use std::iter;

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
    /// An operation on [`Value::RefValue`] attempted to use an invalid key.
    /// Proper usage of this crate should never generate this error.
    /// The most likely cause is that you are using multiple instances of [`RefPool`] and used the wrong one for some operation.
    RefPoolKeyError { key: RefPoolKey },
    /// The result of a failed type conversion.
    ConversionError { got: Type, expected: Type },
    /// Exceeded the maximum call depth.
    /// This can be configured by [`Process::new`].
    CallDepthLimit { limit: usize },
}
impl From<RefPoolKey> for ExecError {
    fn from(key: RefPoolKey) -> Self {
        Self::RefPoolKeyError { key }
    }
}
impl From<ConversionError> for ExecError {
    fn from(err: ConversionError) -> Self {
        Self::ConversionError { got: err.got, expected: err.expected }
    }
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
    /// as well as retrieving the return value or execution error in the event that the process terminates (see [`StepResult`]).
    pub fn step(&mut self, ref_pool: &mut RefPool, globals: &mut SymbolTable, fields: &mut SymbolTable) -> StepResult {
        if !self.running { return StepResult::Idle; }
        let (_, locals) = self.call_stack.last_mut().unwrap();
        let mut context = [globals, fields, locals];
        let mut context = LookupGroup::new(&mut context);

        macro_rules! terminate_err {
            ($err:expr) => {{
                self.running = false;
                return StepResult::Terminate(Err($err));
            }}
        }
        macro_rules! lookup_var {
            ($var:expr) => {{
                let var = $var;
                match context.lookup(var) {
                    Some(x) => x,
                    None => terminate_err!(ExecError::UndefinedVariable { name: var.into(), pos: self.pos }),
                }
            }}
        }

        match &self.code.0[self.pos] {
            Instruction::Illegal => panic!(),

            Instruction::PushValue { value } => {
                self.value_stack.push(Value::from_ast(value, ref_pool));
                self.pos += 1;
            }
            Instruction::PushVariable { var } => {
                self.value_stack.push(lookup_var!(var));
                self.pos += 1;
            }
            Instruction::PopValue => {
                self.value_stack.pop().unwrap();
                self.pos += 1;
            }

            Instruction::BinaryOp { op } => {
                let b = self.value_stack.pop().unwrap();
                let a = self.value_stack.pop().unwrap();
                self.value_stack.push(match ops::binary_op(a, b, ref_pool, *op) {
                    Ok(x) => x,
                    Err(e) => terminate_err!(e),
                });
                self.pos += 1;
            }

            Instruction::Assign { vars } => {
                let value = self.value_stack.pop().unwrap();
                for var in vars {
                    context.set_or_define(var, value);
                }
                self.pos += 1;
            }
            Instruction::BinaryOpAssign { var, op } => {
                let b = self.value_stack.pop().unwrap();
                let a = lookup_var!(var);
                context.set_or_define(var, match ops::binary_op(a, b, ref_pool, *op) {
                    Ok(x) => x,
                    Err(e) => terminate_err!(e),
                });
                self.pos += 1;
            }

            Instruction::Jump { pos } => self.pos = *pos,
            Instruction::ConditionalJump { pos, when } => {
                let value = self.value_stack.pop().unwrap();
                self.pos = if value.flatten(&ref_pool).unwrap().is_truthy() == *when { *pos } else { self.pos + 1 };
            }

            Instruction::Call { pos, params } => {
                if self.call_stack.len() >= self.max_call_depth {
                    self.running = false;
                    return StepResult::Terminate(Err(ExecError::CallDepthLimit { limit: self.max_call_depth }));
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
                    self.running = false;
                    return StepResult::Terminate(Ok(Some(self.value_stack.pop().unwrap())));
                } else {
                    self.pos = pos;
                }
            }
        }

        StepResult::Normal
    }
}

mod ops {
    use super::*;

    fn as_list(v: Value, ref_pool: &RefPool) -> Option<&[Value]> {
        match v.flatten(ref_pool).unwrap() {
            FlatValue::List(v) => Some(&*v),
            _ => None,
        }
    }
    fn as_matrix(v: Value, ref_pool: &RefPool) -> Option<&[Value]> {
        match as_list(v, ref_pool) {
            Some(vals) => match vals {
                [] => None,
                [first, ..] => if as_list(*first, ref_pool).is_some() { Some(vals) } else { None },
            }
            None => None,
        }
    }

    fn binary_op_impl(a: Value, b: Value, ref_pool: &mut RefPool, scalar_op: fn(Value, Value, &mut RefPool) -> Result<Value, ExecError>, matrix_mode: bool) -> Result<Value, ExecError> {
        let checker = if matrix_mode { as_matrix } else { as_list };
        Ok(match (checker(a, ref_pool).map(ToOwned::to_owned), checker(b, ref_pool).map(ToOwned::to_owned)) {
            (Some(a), Some(b)) => Value::from_vec(iter::zip(a, b).map(|(a, b)| binary_op_impl(a, b, ref_pool, scalar_op, matrix_mode)).collect::<Result<_,_>>()?, ref_pool),
            (Some(a), None) => Value::from_vec(a.into_iter().map(|a| binary_op_impl(a, b, ref_pool, scalar_op, matrix_mode)).collect::<Result<_,_>>()?, ref_pool),
            (None, Some(b)) => Value::from_vec(b.into_iter().map(|b| binary_op_impl(a, b, ref_pool, scalar_op, matrix_mode)).collect::<Result<_,_>>()?, ref_pool),
            (None, None) => if matrix_mode { binary_op_impl(a, b, ref_pool, scalar_op, false)? } else { scalar_op(a, b, ref_pool)? }
        })
    }
    pub(super) fn binary_op(a: Value, b: Value, ref_pool: &mut RefPool, op: BinaryOp) -> Result<Value, ExecError> {
        match op {
            BinaryOp::Add     => ops::binary_op_impl(a, b, ref_pool, |a, b, ref_pool| Ok((a.flatten(ref_pool)?.to_number()? + b.flatten(ref_pool).unwrap().to_number()?).into()), true),
            BinaryOp::Sub     => ops::binary_op_impl(a, b, ref_pool, |a, b, ref_pool| Ok((a.flatten(ref_pool)?.to_number()? - b.flatten(ref_pool).unwrap().to_number()?).into()), true),
            BinaryOp::Mul     => ops::binary_op_impl(a, b, ref_pool, |a, b, ref_pool| Ok((a.flatten(ref_pool)?.to_number()? * b.flatten(ref_pool).unwrap().to_number()?).into()), true),
            BinaryOp::Div     => ops::binary_op_impl(a, b, ref_pool, |a, b, ref_pool| Ok((a.flatten(ref_pool)?.to_number()? / b.flatten(ref_pool).unwrap().to_number()?).into()), true),
            BinaryOp::Greater => ops::binary_op_impl(a, b, ref_pool, |a, b, ref_pool| Ok((a.flatten(ref_pool)?.to_number()? > b.flatten(ref_pool).unwrap().to_number()?).into()), true),
            BinaryOp::Less    => ops::binary_op_impl(a, b, ref_pool, |a, b, ref_pool| Ok((a.flatten(ref_pool)?.to_number()? < b.flatten(ref_pool).unwrap().to_number()?).into()), true),
        }
    }
}
