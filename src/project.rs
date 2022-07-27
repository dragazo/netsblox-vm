use std::prelude::v1::*;
use std::collections::VecDeque;
use std::rc::Rc;
use std::iter;

use crate::*;
use crate::gc::*;
use crate::slotmap::*;
use crate::runtime::*;
use crate::bytecode::*;
use crate::process::*;

new_key! {
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

#[derive(Collect)]
#[collect(no_drop)]
struct State<'gc, S: System> {
    global_context: GcCell<'gc, GlobalContext<'gc>>,
    code: Rc<ByteCode>,
    settings: Settings,
    processes: SlotMap<ProcessKey, Process<'gc, S>>,
    process_queue: VecDeque<ProcessKey>,
}
#[derive(Collect)]
#[collect(no_drop)]
pub struct Project<'gc, S: System> {
    state: State<'gc, S>,
    scripts: Vec<Script<'gc>>,
}

#[derive(Collect)]
#[collect(require_static)]
enum Hat {
    OnFlag,
    LocalMessage { msg_type: String },
}

#[derive(Collect)]
#[collect(no_drop)]
struct Script<'gc> {
    hat: Hat,
    start_pos: usize,
    entity: GcCell<'gc, Entity<'gc>>,
    process: Option<ProcessKey>,
    context_queue: VecDeque<(SymbolTable<'gc>, Option<Barrier>)>,
}
impl<'gc> Script<'gc> {
    fn get_process_mut<'a, S: System>(&self, state: &'a mut State<'gc, S>) -> Option<&'a mut Process<'gc, S>> {
        state.processes.get_mut(self.process?)
    }
    fn consume_context<S: System>(&mut self, state: &mut State<'gc, S>) {
        let process = self.get_process_mut(state);
        if process.as_ref().map(|x| x.is_running()).unwrap_or(false) { return }

        let (context, barrier) = match self.context_queue.pop_front() {
            Some(x) => x,
            None => return,
        };

        match process {
            Some(process) => process.initialize(context, barrier),
            None => {
                let mut process = Process::new(state.code.clone(), self.start_pos, state.global_context, self.entity, state.settings.clone());
                process.initialize(context, barrier);
                let key = state.processes.insert(process);
                state.process_queue.push_back(key);
                self.process = Some(key);
            }
        }
    }
    fn stop_all<S: System>(&mut self, state: &mut State<'gc, S>) {
        if let Some(process) = self.process {
            state.processes.remove(process);
            self.process = None;
        }
        self.context_queue.clear();
    }
    fn schedule<S: System>(&mut self, state: &mut State<'gc, S>, context: SymbolTable<'gc>, barrier: Option<Barrier>, max_queue: usize) {
        self.context_queue.push_back((context, barrier));
        self.consume_context(state);
        if self.context_queue.len() > max_queue {
            self.context_queue.pop_back();
        }
    }
}

impl<'gc, S: System> Project<'gc, S> {
    pub fn from_ast(mc: MutationContext<'gc, '_>, role: &ast::Role, settings: Settings) -> Self {
        let global_context = GlobalContext::from_ast(mc, role);
        let (code, locations) = ByteCode::compile(role);

        let mut scripts = vec![];
        for (entity, (ast_entity, locs)) in iter::zip(&global_context.entities, &locations.entities) {
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

        Self {
            scripts,
            state: State {
                global_context: GcCell::allocate(mc, global_context),
                code: Rc::new(code),
                settings,
                processes: Default::default(),
                process_queue: Default::default(),
            }
        }
    }
    pub fn input(&mut self, input: Input) {
        match input {
            Input::Start => {
                for script in self.scripts.iter_mut() {
                    if let Hat::OnFlag = &script.hat {
                        script.stop_all(&mut self.state);
                        script.schedule(&mut self.state, Default::default(), None, 0);
                    }
                }
            }
            Input::Stop => {
                self.state.processes.clear();
                self.state.process_queue.clear();
            }
        }
    }
    pub fn step(&mut self, mc: MutationContext<'gc, '_>, system: &S) -> ProjectStep {
        let (proc_key, proc) = loop {
            match self.state.process_queue.pop_front() {
                None => return ProjectStep::Idle,
                Some(proc_key) => if let Some(proc) = self.state.processes.get_mut(proc_key) { break (proc_key, proc) }
            }
        };

        match proc.step(mc, system) {
            Ok(x) => match x {
                ProcessStep::Normal => self.state.process_queue.push_front(proc_key),
                ProcessStep::Yield => self.state.process_queue.push_back(proc_key),
                ProcessStep::Terminate { .. } => (),
                ProcessStep::Idle => unreachable!(),
                ProcessStep::Broadcast { msg_type, barrier } => {
                    for script in self.scripts.iter_mut() {
                        if let Hat::LocalMessage { msg_type: recv_type } = &script.hat {
                            if *recv_type == *msg_type {
                                script.stop_all(&mut self.state);
                                script.schedule(&mut self.state, Default::default(), barrier.clone(), 0);
                            }
                        }
                    }
                    self.state.process_queue.push_front(proc_key); // keep executing same process, if it was a wait, it'll yield next step
                }
            }
            Err(_) => unimplemented!(),
        }

        ProjectStep::Normal
    }
    pub fn global_context(&self) -> GcCell<'gc, GlobalContext<'gc>> {
        self.state.global_context
    }
}
