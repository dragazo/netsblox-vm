use std::prelude::v1::*;
use std::collections::{BTreeMap, VecDeque};
use std::rc::Rc;

use netsblox_ast as ast;
use embedded_time::Clock as EmbeddedClock;
use slotmap::SlotMap;

slotmap::new_key_type! {
    struct RefPoolKey;
    struct EntityKey;
}








struct RefPool {
    pool: SlotMap<RefPoolKey, RefValue>,
    intern: bool,
}
impl RefPool {
    fn new(intern: bool) -> Self {
        Self { pool: Default::default(), intern }
    }
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
                if ref_pool.intern {
                    for (k, v) in ref_pool.0.iter() {
                        match v {
                            RefValue::String(s) if s == x => return Value::RefValue(k),
                            _ => (),
                        }
                    }
                }
                Value::RefValue(ref_pool.0.insert(RefValue::String(x.clone())))
            }
            ast::Value::List(x) => {
                let values = x.iter().map(|x| Value::from_ast(x, ref_pool)).collect();
                Value::RefValue(ref_pool.0.insert(RefValue::List(values)))
            }
        }
    }
}

#[derive(Default)]
pub struct SymbolTable(BTreeMap<String, Value>);
impl SymbolTable {
    pub fn define(&mut self, var: String, value: Value) -> Result<(), Value> {
        match self.0.insert(var, value) {
            None => Ok(()),
            Some(x) => Err(x),
        }
    }
}

pub struct LookupGroup<'a>(pub &'a mut [SymbolTable]);
impl LookupGroup<'_> {
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
}

enum Instruction {
    Assign { vars: Vec<ast::VariableRef> },
    PushValue { value: ast::Value },
}

pub struct ByteCode {
    instructions: Vec<Instruction>,
}
impl ByteCode {
    fn append_expr(&mut self, expr: &ast::Expr) {
        match expr {
            ast::Expr::Value(v) => self.instructions.push(Instruction::PushValue { value: v.clone() }),
            _ => unimplemented!(),
        }
    }
    fn append_stmt(&mut self, stmt: &ast::Stmt) {
        match stmt {
            ast::Stmt::Assign { vars, value, .. } => {
                self.append_expr(value);
                self.instructions.push(Instruction::Assign { vars: vars.clone() })
            }
            _ => unimplemented!(),
        }
    }
    fn append_stmts(&mut self, stmts: &[ast::Stmt]) {
        for stmt in stmts {
            self.append_stmt(stmt);
        }
    }
    pub fn compile(role: &ast::Role) -> Self {
        let mut res = ByteCode {
            instructions: vec![],
        };

        for sprite in role.sprites.iter() {
            for script in sprite.scripts.iter() {
                res.append_stmts(&script.stmts);
            }
        }

        res
    }
}

pub enum ProcessState {
    Running,

}

pub struct Process {
    code: Rc<ByteCode>,
    pos: usize,
    value_stack: Vec<Value>,
    context_stack: Vec<SymbolTable>,
}
impl Process {
    pub fn new(code: Rc<ByteCode>, pos: usize) -> Self {
        Self {
            code, pos,
            value_stack: vec![],
            context_stack: vec![Default::default()],
        }
    }
    pub fn step(&mut self) {
        let ins = &self.code.instructions[self.pos];
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



















struct ScriptContext {
    vars: SymbolTable,
}
enum ScriptState<'a> {
    Idle,
    Running { context: ScriptContext, code_pos: CodePosition<'a> }
}
struct Script {
    script: &'a ast::Script,
    state: ScriptState,
    exec_queue: VecDeque<ScriptContext>,
}
impl Script {
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

#[derive(PartialEq, Eq)]
enum EntityKind {
    Stage,
    Original,
    Clone,
    Dead,
}
struct EntityContext {
    name: String,
    fields: SymbolTable,
    kind: EntityKind,
}
struct Entity {
    context: EntityContext,
    scripts: Vec<Script>,
    script_queue_pos: usize,
}
impl Entity {
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

struct GlobalContext<Clock> {
    clock: Clock,
    ref_pool: RefPool,
    globals: SymbolTable,
}
pub struct Engine<Clock> {
    context: GlobalContext<Clock>,
    entities: SlotMap<EntityKey, Entity>,
    entity_queue: VecDeque<EntityKey>,
}
impl<Clock: EmbeddedClock<T = u64>> Engine<Clock> {
    pub fn new(role: &ast::Role, intern: bool, clock: Clock) -> Self {
        let code = Rc::new(ByteCode::compile(role));
        let mut ref_pool = RefPool::new(intern);

        let mut globals = SymbolTable::new();
        for glob in role.globals.iter() {
            globals.define(&glob.trans_name, Value::from_ast(&glob.value, &mut ref_pool));
        }

        let mut entities: SlotMap<EntityKey, _> = Default::default();
        let mut entity_queue = VecDeque::new();
        for (i, sprite) in role.sprites.iter() {
            let mut fields = SymbolTable::new();
            for field in sprite.fields {
                fields.define(&field.trans_name, Value::from_ast(&field.value, &mut ref_pool));
            }

            let context = EntityContext {
                name: sprite.trans_name,
                fields,
                kind: if i == 0 { EntityKind::Stage } else { EntityKind::Original },
            };
            let scripts = sprite.scripts.iter()
                .filter(|x| x.hat.is_some()) // scripts without hat blocks can never actually be invoked, so we can ignore them
                .map(|x| Script { script: x, state: ScriptState::Idle, exec_queue: Default::default() })
                .collect();

            entity_queue.push_back(entities.insert(Entity { context, scripts, script_queue_pos: 0 }));
        }

        Self {
            context: GlobalContext { clock, globals, ref_pool },
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
