use std::prelude::v1::*;
use std::collections::VecDeque;
use std::rc::Rc;
use std::iter;

use netsblox_ast as ast;
use slotmap::SlotMap;

use crate::bytecode::*;
use crate::runtime::*;
use crate::process::*;

slotmap::new_key_type! {
    struct ProcessKey;
}

/// Simulates input from the user.
pub enum Input {
    /// Simulate pressing the start (green flag) button.
    /// This has the effect of interrupting any running "on start" scripts and restarting them (with an empty context).
    /// Any other running processes are not affected.
    Start,
    /// Simulate pressing the stop button.
    /// This has the effect of stopping all currently-running processes.
    /// Note that some hat blocks could cause new processes to spin up after this operation.
    Stop,
}

/// Result of stepping through the execution of a [`Project`].
pub enum ProjectStep {
    /// The project had running processes to execute and did so.
    Normal,
    /// There were no running processes to execute.
    Idle,
}

struct Script {
    hat: ast::Hat,
    start_pos: usize,
    entity: EntityKey,
    process: Option<ProcessKey>,
    context_queue: VecDeque<SymbolTable>,
}
impl Script {
    fn get_process_mut<'a, S: System>(&self, state: &'a mut State<S>) -> Option<&'a mut Process<S>> {
        state.processes.get_mut(self.process?)
    }
    fn consume_context<S: System>(&mut self, state: &mut State<S>) {
        let process = self.get_process_mut(state);
        if process.as_ref().map(|x| x.is_running()).unwrap_or(false) { return }

        let context = match self.context_queue.pop_front() {
            Some(x) => x,
            None => return,
        };

        match process {
            Some(process) => process.initialize(context),
            None => {
                let mut process = Process::new(state.code.clone(), self.start_pos, self.entity, state.settings);
                process.initialize(context);
                let key = state.processes.insert(process);
                state.process_queue.push_back(key);
                self.process = Some(key);
            }
        }
    }
    fn stop_all<S: System>(&mut self, state: &mut State<S>) {
        if let Some(process) = self.process {
            state.processes.remove(process);
            self.process = None;
        }
        self.context_queue.clear();
    }
    fn schedule<S: System>(&mut self, state: &mut State<S>, context: SymbolTable, max_queue: usize) {
        self.context_queue.push_back(context);
        self.consume_context(state);
        if self.context_queue.len() > max_queue {
            self.context_queue.pop_back();
        }
    }
}

struct State<S: System> {
    runtime: Runtime,
    code: Rc<ByteCode>,
    settings: Settings,
    processes: SlotMap<ProcessKey, Process<S>>,
    process_queue: VecDeque<ProcessKey>,
}
pub struct Project<S: System> {
    state: State<S>,
    scripts: Vec<Script>,
}
impl<S: System> Project<S> {
    pub fn from_ast(role: &ast::Role, settings: Settings) -> Self {
        let (runtime, entity_keys) = Runtime::from_ast(role);
        let (code, locations) = ByteCode::compile(role);

        let mut scripts = vec![];
        for (entity_key, (entity, locs)) in iter::zip(entity_keys, &locations.entities) {
            for (script, loc) in iter::zip(&entity.scripts, &locs.scripts) {
                if let Some(hat) = &script.hat {
                    scripts.push(Script {
                        hat: hat.clone(),
                        entity: entity_key,
                        process: None,
                        start_pos: loc.1,
                        context_queue: Default::default(),
                    });
                }
            }
        }

        Self { scripts, state: State { runtime, code: Rc::new(code), settings, processes: Default::default(), process_queue: Default::default() } }
    }
    pub fn runtime(&self) -> &Runtime {
        &self.state.runtime
    }
    pub fn runtime_mut(&mut self) -> &mut Runtime {
        &mut self.state.runtime
    }
    pub fn input(&mut self, input: Input) {
        match input {
            Input::Start => {
                for script in self.scripts.iter_mut() {
                    if let ast::Hat::OnFlag { .. } = &script.hat {
                        script.stop_all(&mut self.state);
                        script.schedule(&mut self.state, Default::default(), 0);
                    }
                }
            }
            Input::Stop => {
                self.state.processes.clear();
                self.state.process_queue.clear();
            }
        }
    }
    pub fn step(&mut self, system: &mut S) -> ProjectStep {
        let (process_key, process) = loop {
            match self.state.process_queue.pop_front() {
                None => return ProjectStep::Idle,
                Some(process_key) => match self.state.processes.get_mut(process_key) {
                    None => (), // prune dead process key
                    Some(process) => break (process_key, process),
                }
            }
        };

        match process.step(&mut self.state.runtime, system) {
            Ok(x) => match x {
                ProcessStep::Normal => self.state.process_queue.push_front(process_key),   // continue executing same process
                ProcessStep::Yield => self.state.process_queue.push_back(process_key),     // next process
                ProcessStep::Terminate(_) => { self.state.processes.remove(process_key); } // prune terminated process and key
                ProcessStep::Idle => unreachable!(),
            }
            Err(_) => unimplemented!(),
        }

        ProjectStep::Normal
    }
}
