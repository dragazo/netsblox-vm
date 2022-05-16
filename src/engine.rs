use std::prelude::v1::*;
use std::collections::{BTreeMap, VecDeque};

use netsblox_ast as ast;
use embedded_time::Clock as EmbeddedClock;
use slotmap::{SlotMap, DefaultKey};

pub enum StepResult {
    Normal,
    Terminated,
}

struct SymbolTable(BTreeMap<String, ast::Value>);

struct Task {
    script: ast::Script,
    context_queue: VecDeque<SymbolTable>,
}

struct EntityContext {
    name: String,
    fields: SymbolTable,
}
struct Entity {
    context: EntityContext,
    tasks: Vec<Task>,
    task_pos: usize,
}

impl<Clock: EmbeddedClock<T = u64>> Entity {
    fn step(&mut self, global_context: &mut GlobalContext<Clock>) {

    }
}

struct GlobalContext<Clock> {
    clock: Clock,
    proj_name: String,
    role_name: String,
    globals: SymbolTable,
}
pub struct Engine<Clock> {
    context: GlobalContext<Clock>,
    entities: SlotMap<DefaultKey, Entity>,
    entity_queue: VecDeque<DefaultKey>,
}

impl<Clock: EmbeddedClock<T = u64>> Engine<Clock> {
    pub fn new(proj_name: String, role: ast::Role, clock: Clock) -> Self {
        let context = GlobalContext {
            clock,
            proj_name: proj_name,
            role_name: role.name,
            globals: SymbolTable(role.globals.into_iter().map(|x| (x.trans_name, x.value)).collect()),
        };

        let mut entities = SlotMap::new();
        let mut entity_queue = VecDeque::new();
        for sprite in role.sprites {
            let context = EntityContext {
                name: sprite.trans_name,
                fields: SymbolTable(sprite.fields.into_iter().map(|x| (x.trans_name, x.value)).collect()),
            };
            let scripts = sprite.scripts.into_iter().filter(|x| x.hat.is_some()).collect();

            entity_queue.push_back(entities.insert(Entity { context, scripts }));
        }

        Self { context, entities, entity_queue }
    }
    pub fn step(&mut self) -> StepResult {
        let (key, entity) = loop {
            match self.entity_queue.pop_front() {
                None => return StepResult::Terminated,
                Some(key) => match self.entities.get(key) {
                    None => (), // prune invalid key due to pop
                    Some(entity) => break (key, entity),
                },
            }
        };

        entity.step(&mut self.context);

        self.entity_queue.push_back(key); // add same entity back to execution queue
        StepResult::Normal
    }
}