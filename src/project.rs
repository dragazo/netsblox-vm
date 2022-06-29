use std::prelude::v1::*;
use std::collections::VecDeque;
use std::rc::Rc;
use std::iter;

use netsblox_ast as ast;

use crate::gc::*;
use crate::system::*;
use crate::bytecode::*;
use crate::process::*;

#[derive(Collect)]
#[collect(no_drop)]
struct State<'gc, S: System> {
    global_context: GcCell<'gc, GlobalContext<'gc>>,
    code: Rc<ByteCode>,
    settings: Settings,
    processes: VecDeque<Process<'gc, S>>,
}
#[derive(Collect)]
#[collect(no_drop)]
pub struct Project<'gc, S: System> {
    state: State<'gc, S>,
    scripts: Vec<Script<'gc, S>>,
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

#[derive(Collect)]
#[collect(require_static)]
enum Hat {
    OnFlag,
    LocalMessage { msg_type: String },
}

#[derive(Collect)]
#[collect(no_drop)]
struct Script<'gc, S: System> {
    hat: Hat,
    start_pos: usize,
    entity: GcCell<'gc, Entity<'gc>>,
    process: Option<ProcessKey>,
    context_queue: VecDeque<SymbolTable<'gc>>,
}
impl<'gc, S: System> Script<'gc, S> {
    fn get_process_mut<'a>(&self, state: &'a mut State<'gc, S>) -> Option<&'a mut Process<'gc, S>> {
        state.processes.get_mut(self.process?)
    }
    fn consume_context(&mut self, state: &mut State<'gc, S>) {
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
    fn stop_all(&mut self, state: &mut State<'gc, S>) {
        if let Some(process) = self.process {
            state.processes.remove(process);
            self.process = None;
        }
        self.context_queue.clear();
    }
    fn schedule(&mut self, state: &mut State<'gc, S>, context: SymbolTable<'gc>, max_queue: usize) {
        self.context_queue.push_back(context);
        self.consume_context(state);
        if self.context_queue.len() > max_queue {
            self.context_queue.pop_back();
        }
    }
}

impl<'gc, S: System> Project<'gc, S> {
    pub fn from_ast(mc: MutationContext<'gc, '_>, role: &ast::Role, settings: Settings) -> Self {
        let runtime = Runtime::from_ast(mc, role);
        let (code, locations) = ByteCode::compile(role);

        let mut scripts = vec![];
        for (entity, (ast_entity, locs)) in iter::zip(&runtime.entities, &locations.entities) {
            for (script, loc) in iter::zip(&ast_entity.scripts, &locs.scripts) {
                if let Some(hat) = &script.hat {
                    scripts.push(Script {
                        hat: match hat {
                            ast::Hat::OnFlag { .. } => Hat::OnFlag,
                            ast::Hat::LocalMessage { msg_type, .. } => Hat::LocalMessage { msg_type: msg_type.clone() },
                            x => unimplemented!("{:?}", x),
                        },
                        entity: *entity,
                        process: None,
                        start_pos: loc.1,
                        context_queue: Default::default(),
                    });
                }
            }
        }

        Self { scripts, state: State { runtime, code: Rc::new(code), settings, processes: Default::default() } }
    }
    pub fn input(&mut self, mc: MutationContext<'gc, '_>, input: Input) {
        match input {
            Input::Start => {
                for script in self.scripts.iter() {
                    let script = script.write(mc);
                    if let Hat::OnFlag = &script.hat {
                        script.stop_all(&mut self.state);
                        script.schedule(&mut self.state, Default::default(), 0);
                    }
                }
            }
            Input::Stop => self.state.processes.clear(),
        }
    }
    pub fn step(&mut self, mc: MutationContext<'gc, '_>, system: &mut S) -> ProjectStep {
        let process = match self.state.processes.front_mut() {
            None => return ProjectStep::Idle,
            Some(x) => x,
        };

        match process.step(mc, &mut self.state.runtime, system) {
            Ok(x) => match x {
                ProcessStep::Normal => (),
                ProcessStep::Yield => self.state.processes.rotate_left(1),
                ProcessStep::Terminate => { self.state.processes.pop_front(); }
                ProcessStep::Idle => unreachable!(),
            }
            Err(_) => unimplemented!(),
        }

        ProjectStep::Normal
    }
}
