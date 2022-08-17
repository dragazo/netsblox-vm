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

fn parse_key(key: &str) -> Option<KeyCode> {
    Some(match key {
        "any key" => return None,
        "up arrow" => KeyCode::Up,
        "down arrow" => KeyCode::Down,
        "left arrow" => KeyCode::Left,
        "right arrow" => KeyCode::Right,
        "space" => KeyCode::Char(' '),
        _ => {
            assert_eq!(key.chars().count(), 1);
            KeyCode::Char(key.chars().next().unwrap().to_ascii_lowercase())
        }
    })
}

/// Simulates input from the user.
#[derive(Debug)]
pub enum Input {
    /// Simulate pressing the start (green flag) button.
    /// This has the effect of interrupting any running "on start" scripts and restarting them (with an empty context).
    /// Any other running processes are not affected.
    Start,
    /// Simulate pressing the stop button.
    /// This has the effect of stopping all currently-running processes.
    /// Note that some hat blocks could cause new processes to spin up after this operation.
    Stop,
    /// Simulates a key down event from the keyboard.
    /// This should be repeated if the button is held down.
    KeyDown(KeyCode),
    /// Simulates a key up event from the keyboard.
    /// Due to the nature of the TTY interface, key up events are not always available, so this event does not need to be sent.
    /// If not sent, a timeout is used to determine when a key is released (sending this event can short-circuit the timeout).
    KeyUp(KeyCode),
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
    /// Fire an event when a key is pressed. [`None`] is used to denote any key press.
    OnKey { key: Option<KeyCode> },
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
    fn consume_context<S: System>(&mut self, state: &mut State<'gc, S>, system: &S) {
        let process = self.process.and_then(|key| Some((key, state.processes.get_mut(key)?)));
        if process.as_ref().map(|x| x.1.is_running()).unwrap_or(false) { return }

        let (context, barrier) = match self.context_queue.pop_front() {
            Some(x) => x,
            None => return,
        };

        match process {
            Some((key, process)) => {
                debug_assert!(!state.process_queue.contains(&key));
                debug_assert_eq!(self.process, Some(key));

                process.initialize(context, barrier, system);
                state.process_queue.push_back(key);
            }
            None => {
                let mut process = Process::new(state.code.clone(), self.start_pos, state.global_context, self.entity, state.settings);
                process.initialize(context, barrier, system);
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
    fn schedule<S: System>(&mut self, state: &mut State<'gc, S>, system: &S, context: SymbolTable<'gc>, barrier: Option<Barrier>, max_queue: usize) {
        self.context_queue.push_back((context, barrier));
        self.consume_context(state, system);
        if self.context_queue.len() > max_queue {
            self.context_queue.pop_back();
        }
    }
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
                            ast::Hat::OnKey { key, .. } => Hat::OnKey { key: parse_key(key) },
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
    pub fn input(&mut self, input: Input, system: &S) {
        match input {
            Input::Start => {
                for script in self.scripts.iter_mut() {
                    if let Hat::OnFlag = &script.hat {
                        script.stop_all(&mut self.state);
                        script.schedule(&mut self.state, system, Default::default(), None, 0);
                    }
                }
            }
            Input::Stop => {
                self.state.processes.clear();
                self.state.process_queue.clear();
            }
            Input::KeyDown(input_key) => {
                for script in self.scripts.iter_mut() {
                    if let Hat::OnKey { key } = &script.hat {
                        if key.map(|x| x == input_key).unwrap_or(true) {
                            script.schedule(&mut self.state, system, Default::default(), None, 0);
                        }
                    }
                }
            }
            Input::KeyUp(_) => unimplemented!(),
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
                                script.schedule(&mut self.state, system, Default::default(), barrier.clone(), 0);
                            }
                        }
                    }
                    self.state.process_queue.push_front(proc_key); // keep executing same process, if it was a wait, it'll yield next step
                }
            }
            Err(e) => unimplemented!("{e:?}"),
        }

        ProjectStep::Normal
    }
    pub fn global_context(&self) -> GcCell<'gc, GlobalContext<'gc>> {
        self.state.global_context
    }
}
