use std::prelude::v1::*;
use std::collections::{BTreeMap, VecDeque};

use netsblox_ast as ast;
use embedded_time::Clock as EmbeddedClock;
use slotmap::SlotMap;

slotmap::new_key_type! {
    struct RefPoolKey;
    struct EntityKey;
}

enum CopyValue {
    Bool(bool),
    Number(f64),
}
enum RefValue {
    String(String),
    List(Vec<Value>),
}
enum Value {
    CopyValue(CopyValue),
    RefValue(RefPoolKey),
}
impl Value {
    fn from_ast(value: &ast::Value, ref_pool: &mut RefPool) -> Self {
        match value {
            ast::Value::Bool(x) => Value::CopyValue(CopyValue::Bool(*x)),
            ast::Value::Number(x) => Value::CopyValue(CopyValue::Number(*x)),
            ast::Value::Constant(ast::Constant::E) => Value::CopyValue(CopyValue::Number(std::f64::consts::E)),
            ast::Value::Constant(ast::Constant::Pi) => Value::CopyValue(CopyValue::Number(std::f64::consts::PI)),
            ast::Value::String(x) => {
                for (k, v) in ref_pool.pool.iter() {
                    match v {
                        RefValue::String(s) if s == x => return Value::RefValue(k),
                        _ => (),
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

struct SymbolTable<'a>(BTreeMap<&'a str, Value>);
impl<'a> SymbolTable<'a> {
    fn new() -> Self {
        Self(Default::default())
    }
    fn define(&mut self, var: &'a str, value: Value) -> Result<(), Value> {
        match self.0.insert(var, value) {
            None => Ok(()),
            Some(x) => Err(x),
        }
    }
}

pub enum StepResult {
    Noop,
    Normal,
    Yield,
}








enum ScriptPosStepResult {
    Normal,
    Terminated,
}

struct StmtsPos<'a> {
    stmts: &'a [ast::Stmt],
    working: Option<StmtPos<'a>>,
}
struct StmtPos<'a> {
    stmt: &'a ast::Stmt,
    working: Vec<ExprPos<'a>>,
}
struct ExprPos<'a> {
    expr: &'a ast::Expr,
    working: Vec<ExprPos<'a>>,
}

impl<'a> ExprPos<'a> {
    fn new(expr: &'a ast::Expr) -> Self {
        Self { expr, working: vec![] }
    }
    fn step<Clock>(&mut self, global_context: &mut GlobalContext<Clock>, entity_context: &mut EntityContext, script_context: &mut ScriptContext) -> ScriptPosStepResult {
        match self.expr {
            ast::Expr::Add { left, right } => {

            }
            _ => unimplemented!(),
        }
        ScriptPosStepResult::Normal
    }
}

impl<'a> StmtsPos<'a> {
    fn new(stmts: &'a [ast::Stmt]) -> Self {
        Self { stmts, working: None }
    }
    fn step<Clock>(&mut self, global_context: &mut GlobalContext<Clock>, entity_context: &mut EntityContext, script_context: &mut ScriptContext) -> ScriptPosStepResult {
        if self.stmts.is_empty() { return ScriptPosStepResult::Terminated }

        if self.working.is_none() {
            self.working = Some(StmtPos::new
        }
    }
}

enum CodePosition<'a> {
    Stmts(StmtsPos<'a>),
    Stmt(StmtPos<'a>),
    Expr(ExprPos<'a>),
}
impl<'a> CodePosition<'a> {
    fn step<Clock>(&mut self, global_context: &mut GlobalContext<Clock>, entity_context: &mut EntityContext, script_context: &mut ScriptContext) -> ScriptPosStepResult {
        match self {
            CodePosition::Stmts(x) => x.step(),
            CodePosition::Stmt(x) => x.step(),
            CodePosition::Expr(x) => x.step(),
        }
    }
}



















struct ScriptContext<'a> {
    vars: SymbolTable<'a>,
}
enum ScriptState<'a> {
    Idle,
    Running { context: ScriptContext<'a>, code_pos: CodePosition<'a> }
}
struct Script<'a> {
    script: &'a ast::Script,
    state: ScriptState<'a>,
    exec_queue: VecDeque<ScriptContext<'a>>,
}
impl<'a> Script<'a> {
    fn step<Clock>(&mut self, global_context: &mut GlobalContext<Clock>, entity_context: &mut EntityContext) -> StepResult {
        if let ScriptState::Idle = &self.state {
            match self.exec_queue.pop_front() {
                None => return,
                Some(context) => self.state = ScriptState::Running { context, code_pos: CodePosition::Stmts(&*self.script.stmts) },
            }
        }
        if let ScriptState::Running { context, code_pos } = &mut self.state {
            code_pos.step(global_context, entity_context, context);
        }
    }
}

















// -----------------------------------------------------------------

struct EntityContext<'a> {
    name: String,
    fields: SymbolTable<'a>,
    is_clone: bool,
}
struct Entity<'a> {
    context: EntityContext<'a>,
    scripts: Vec<Script<'a>>,
    script_queue_pos: usize,
}
impl Entity<'_> {
    fn step<Clock>(&mut self, global_context: &mut GlobalContext<Clock>) -> StepResult {
        if self.scripts.is_empty() { return StepResult::Noop }
        let res = self.scripts[self.script_queue_pos].step(global_context, &mut self.context);
        match res {
            StepResult::Noop | StepResult::Normal => (), // keep executing same script
            StepResult::Yield => self.script_queue_pos = (self.script_queue_pos + 1) % self.scripts.len(), // yield to next script
        }
        res
    }
}

// -----------------------------------------------------------------

struct RefPool {
    pool: SlotMap<RefPoolKey, RefValue>,
}
impl RefPool {
    fn new() -> Self {
        Self { pool: Default::default() }
    }
}

// -----------------------------------------------------------------

struct GlobalContext<'a, Clock> {
    clock: Clock,
    proj_name: String,
    role_name: String,
    globals: SymbolTable<'a>,
    ref_pool: RefPool,
}
pub struct Engine<'a, Clock> {
    context: GlobalContext<'a, Clock>,
    entities: SlotMap<EntityKey, Entity<'a>>,
    entity_queue: VecDeque<EntityKey>,
}
impl<'a, Clock: EmbeddedClock<T = u64>> Engine<'a, Clock> {
    pub fn new(proj_name: String, role: &'a ast::Role, clock: Clock) -> Self {
        let mut ref_pool = RefPool::new();

        let mut globals = SymbolTable::new();
        for glob in role.globals.iter() {
            globals.define(&glob.trans_name, Value::from_ast(&glob.value, &mut ref_pool));
        }

        let mut entities: SlotMap<EntityKey, _> = Default::default();
        let mut entity_queue = VecDeque::new();
        for sprite in role.sprites.iter() {
            let mut fields = SymbolTable::new();
            for field in sprite.fields {
                fields.define(&field.trans_name, Value::from_ast(&field.value, &mut ref_pool));
            }

            let context = EntityContext {
                name: sprite.trans_name,
                fields,
                is_clone: false,
            };
            let scripts = sprite.scripts.iter()
                .filter(|x| x.hat.is_some()) // scripts without hat blocks can never actually be invoked, so we can ignore them
                .map(|x| Script { script: x, state: ScriptState::Idle, exec_queue: Default::default() })
                .collect();

            entity_queue.push_back(entities.insert(Entity { context, scripts, script_queue_pos: 0 }));
        }

        Self {
            context: GlobalContext {
                clock, globals, ref_pool,
                proj_name: proj_name,
                role_name: role.name,
            },
            entities, entity_queue,
        }
    }
    pub fn step(&mut self) -> StepResult {
        let (key, entity) = loop {
            match self.entity_queue.pop_front() {
                None => return StepResult::Noop,
                Some(key) => match self.entities.get(key) {
                    None => (), // prune invalid key due to pop
                    Some(entity) => break (key, entity),
                },
            }
        };

        let res = entity.step(&mut self.context);
        match res {
            StepResult::Noop | StepResult::Normal => self.entity_queue.push_front(key), // keep executing same entity
            StepResult::Yield => self.entity_queue.push_back(key), // yield to next entity
        }
        res
    }
}
