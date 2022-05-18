use std::prelude::v1::*;
use std::collections::{BTreeMap, VecDeque};
use std::rc::Rc;
use std::iter;

use netsblox_ast as ast;
use embedded_time::Clock as EmbeddedClock;
use slotmap::SlotMap;

use crate::bytecode::*;

slotmap::new_key_type! {
    struct RefPoolKey;
    struct EntityKey;
}

// -----------------------------------------------------------------

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

#[derive(Default)]
struct SymbolTable(BTreeMap<String, Value>);
impl SymbolTable {
    fn define(&mut self, var: String, value: Value) -> Result<(), Value> {
        match self.0.insert(var, value) {
            None => Ok(()),
            Some(x) => Err(x),
        }
    }
}

struct LookupGroup<'a>(&'a mut [SymbolTable]);
impl LookupGroup<'_> {
    fn lookup(&self, var: &str) -> Option<&Value> {
        for src in self.0.iter() {
            if let Some(val) = src.0.get(var) {
                return Some(val);
            }
        }
        None
    }
    fn lookup_mut(&mut self, var: &str) -> Option<&mut Value> {
        for src in self.0.iter_mut() {
            if let Some(val) = src.0.get_mut(var) {
                return Some(val);
            }
        }
        None
    }
}

// -----------------------------------------------------------------

enum StepResult {
    Noop,
    Normal,
    Yield,
    Terminate,
}
enum ProcessState {
    Uninitialized,
    Running,
    Terminated(Result<Value, String>),
}
struct Process {
    code: Rc<ByteCode>,
    pos: usize,
    state: ProcessState,
    value_stack: Vec<Value>,
    context_stack: Vec<SymbolTable>,
}
impl Process {
    fn new(code: Rc<ByteCode>) -> Self {
        Self {
            code,
            pos: 0,
            state: ProcessState::Uninitialized,
            value_stack: vec![],
            context_stack: vec![],
        }
    }
    fn initialize(&mut self, start_pos: usize, context: SymbolTable) {
        self.pos = start_pos;
        self.state = ProcessState::Running;
        self.value_stack.clear();
        self.context_stack.clear();
        self.context_stack.push(context);
        self.context_stack.push(Default::default());
    }
    fn step(&mut self) {
        unimplemented!()
    }
}

// -----------------------------------------------------------------

struct Script {
    hat: Option<ast::Hat>,
    process: Process,
    start_pos: usize,
    exec_queue: VecDeque<SymbolTable>,
}
impl Script {
    fn step<Clock>(&mut self, global_context: &mut GlobalContext<Clock>, entity_context: &mut EntityContext) -> StepResult {
        
    }
}

// -----------------------------------------------------------------

#[derive(PartialEq, Eq)]
enum EntityKind {
    Stage,
    Original,
    Clone,
}
struct EntityContext {
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
            StepResult::Yield | StepResult::Terminate => self.script_queue_pos = (self.script_queue_pos + 1) % self.scripts.len(), // yield to next script
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
        let mut ref_pool = RefPool::new(intern);
        let mut globals = SymbolTable::default();
        for glob in role.globals.iter() {
            globals.define(glob.trans_name.clone(), Value::from_ast(&glob.value, &mut ref_pool));
        }

        let (code, locations) = ByteCode::compile(role);
        let code = Rc::new(code);

        let mut entities: SlotMap<EntityKey, _> = Default::default();
        let mut entity_queue = VecDeque::with_capacity(role.sprites.len());
        for (i, (entity, locs)) in iter::zip(&role.sprites, &locations.entities).enumerate() {
            let mut fields = SymbolTable::default();
            for field in entity.fields.iter() {
                fields.define(field.trans_name.clone(), Value::from_ast(&field.value, &mut ref_pool));
            }

            let mut scripts = Vec::with_capacity(entity.scripts.len());
            for (script, loc) in iter::zip(&entity.scripts, &locs.scripts) {
                scripts.push(Script {
                    hat: script.hat.clone(),
                    process: Process::new(code.clone()),
                    start_pos: *loc,
                    exec_queue: Default::default(),
                })
            }

            entity_queue.push_back(entities.insert(Entity {
                context: EntityContext {
                    fields,
                    kind: if i == 0 { EntityKind::Stage } else { EntityKind::Original },
                },
                scripts,
                script_queue_pos: 0
            }));
        }

        Self {
            context: GlobalContext { clock, globals, ref_pool },
            entities, entity_queue,
        }
    }
    pub fn step(&mut self) {
        let (key, entity) = loop {
            match self.entity_queue.pop_front() {
                None => return,
                Some(key) => match self.entities.get(key) {
                    None => (), // prune invalid key due to pop
                    Some(entity) => break (key, entity),
                },
            }
        };

        match entity.step(&mut self.context) {
            StepResult::Noop | StepResult::Normal => self.entity_queue.push_front(key), // keep executing same entity
            StepResult::Yield => self.entity_queue.push_back(key), // yield to next entity
            StepResult::Terminate => { self.entities.remove(key); } // delete entity to kill it and don't add back to entity queue
        }
    }
}
