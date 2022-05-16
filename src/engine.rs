use std::prelude::v1::*;
use std::collections::{BTreeMap, VecDeque};

use netsblox_ast as ast;
use embedded_time::Clock as EmbeddedClock;
use slotmap::{SlotMap, DefaultKey};

struct SymbolTable(BTreeMap<String, ast::Value>);

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
struct Script<'a> {
    script: &'a ast::Script,
    state: ScriptState<'a>,
    exec_queue: VecDeque<ScriptContext>,
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

struct EntityContext {
    name: String,
    fields: SymbolTable,
    is_clone: bool,
}
struct Entity<'a> {
    context: EntityContext,
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

struct GlobalContext<Clock> {
    clock: Clock,
    proj_name: String,
    role_name: String,
    globals: SymbolTable,
}
pub struct Engine<'a, Clock> {
    context: GlobalContext<Clock>,
    entities: SlotMap<DefaultKey, Entity<'a>>,
    entity_queue: VecDeque<DefaultKey>,
}
impl<'a, Clock: EmbeddedClock<T = u64>> Engine<'a, Clock> {
    pub fn new(proj_name: String, role: &'a ast::Role, clock: Clock) -> Self {
        let context = GlobalContext {
            clock,
            proj_name: proj_name,
            role_name: role.name,
            globals: SymbolTable(role.globals.into_iter().map(|x| (x.trans_name, x.value)).collect()),
        };

        let mut entities = SlotMap::new();
        let mut entity_queue = VecDeque::new();
        for sprite in role.sprites.iter() {
            let context = EntityContext {
                name: sprite.trans_name,
                fields: SymbolTable(sprite.fields.into_iter().map(|x| (x.trans_name, x.value)).collect()),
                is_clone: false,
            };
            let scripts = sprite.scripts.iter()
                .filter(|x| x.hat.is_some()) // scripts without hat blocks can never actually be invoked, so we can ignore them
                .map(|x| Script { script: x, state: ScriptState::Idle, exec_queue: Default::default() })
                .collect();

            entity_queue.push_back(entities.insert(Entity { context, scripts, script_queue_pos: 0 }));
        }

        Self { context, entities, entity_queue }
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
