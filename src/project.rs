use std::collections::VecDeque;
use std::rc::{Rc, Weak};
use std::iter;

use netsblox_ast as ast;
use slotmap::SlotMap;

use crate::bytecode::*;
use crate::runtime::*;
use crate::process::*;

slotmap::new_key_type! {
    struct EntityKey;
    struct ProcessKey;
}

pub enum UserInput {
    ClickStart,
}

struct Script<S: System> {
    hat: Option<ast::Hat>,
    process: Process<S>,
    start_pos: usize,
    context_queue: VecDeque<SymbolTable>,
}
impl<S: System> Script<S> {
    fn consume_context(&mut self) {
        if !self.process.is_running() {
            if let Some(context) = self.context_queue.pop_front() {
                self.process.initialize(self.start_pos, context);
            }
        }
    }
    fn schedule(&mut self, max_queue: usize, context: SymbolTable) {
        self.context_queue.push_back(context);
        self.consume_context();
        if self.context_queue.len() > max_queue {
            self.context_queue.pop_back();
        }
    }
    fn step(&mut self, ref_pool: &mut RefPool, system: &mut S, project: &mut ProjectInfo) -> StepType {
        self.consume_context();
        self.process.step(ref_pool, system, project, &*self.entity.upgrade().unwrap())
    }
}

pub struct Project<S: System> {
    context: ProjectInfo,
    ref_pool: RefPool,
    entities: SlotMap<EntityKey, Rc<Entity>>,
    entity_queue: VecDeque<EntityKey>,
    processes: SlotMap<ProcessKey, Process<S>>,
    process_queue: VecDeque<ProcessKey>,
    max_call_depth: usize,
}
impl<S: System> Project<S> {
    pub fn new(role: &ast::Role, max_call_depth: usize) -> Self {
        let mut ref_pool = RefPool::default();
        let globals = SymbolTable::from_globals(role, &mut ref_pool);

        let (code, locations) = ByteCode::compile(role);
        let code = Rc::new(code);

        let mut entities: SlotMap<EntityKey, _> = Default::default();
        let mut entity_queue = VecDeque::with_capacity(role.entities.len());
        for (i, (entity, locs)) in iter::zip(&role.entities, &locations.entities).enumerate() {
            let fields = SymbolTable::from_fields(entity, &mut ref_pool);

            let mut scripts = Vec::with_capacity(entity.scripts.len());
            for (script, loc) in iter::zip(&entity.scripts, &locs.scripts) {
                scripts.push(Script {
                    hat: script.hat.clone(),
                    process: Process::new(code.clone(), max_call_depth),
                    start_pos: *loc,
                    context_queue: Default::default(),
                })
            }

            entity_queue.push_back(entities.insert(Rc::new(Entity {

            })));
        }

        Self {
            context: ProjectInfo { name: role.name.into(), globals },
            ref_pool, entities, entity_queue, max_call_depth,
        }
    }
    pub fn input(&mut self, input: UserInput) {
        match input {
            UserInput::ClickStart => {
                for (_, entity) in self.entities.iter_mut() {
                    for script in entity.scripts.iter_mut() {
                        if let Some(ast::Hat::OnFlag { .. }) = &script.hat {
                            script.schedule(0, Default::default());
                        }
                    }
                }
            }
        }
    }
    pub fn step(&mut self) -> StepType {
        let (key, entity) = loop {
            match self.entity_queue.pop_front() {
                None => return,
                Some(key) => match self.entities.get_mut(key) {
                    None => (), // prune invalid key due to pop
                    Some(entity) => break (key, entity),
                },
            }
        };

        match entity.step(&mut self.context) {
            StepType::Normal => self.entity_queue.push_front(key), // keep executing same entity
            StepType::Yield => self.entity_queue.push_back(key), // yield to next entity
        }
    }
}
