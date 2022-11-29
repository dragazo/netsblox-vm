use std::prelude::v1::*;
use std::collections::{VecDeque, BTreeMap};
use std::rc::Rc;

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
    /// Simulates a key down hat from the keyboard.
    /// This should be repeated if the button is held down.
    KeyDown(KeyCode),
    /// Simulates a key up hat from the keyboard.
    /// Due to the nature of the TTY interface, key up events are not always available, so this hat does not need to be sent.
    /// If not sent, a timeout is used to determine when a key is released (sending this hat can short-circuit the timeout).
    KeyUp(KeyCode),
}

/// Result of stepping through the execution of a [`Project`].
pub enum ProjectStep<'gc, S: System> {
    /// There were no running processes to execute.
    Idle,
    /// The project had a running process, which yielded.
    Yield,
    /// The project had a running process, which did any non-yielding operation.
    Normal,
    /// The project had a running process, which which encountered a runtime error.
    Error { error: ExecError<S>, proc: Process<'gc, S> },
}

pub enum Hat {
    OnFlag,
    LocalMessage { msg_type: String },
    NetworkMessage { msg_type: String, fields: Vec<String> },
    /// Fire an hat when a key is pressed. [`None`] is used to denote any key press.
    OnKey { key: Option<KeyCode> },
}
impl Hat {
    pub fn from_ast(hat: &ast::HatKind) -> Result<Self, FromAstError> {
        Ok(match hat {
            ast::HatKind::OnFlag => Hat::OnFlag,
            ast::HatKind::LocalMessage { msg_type } => Hat::LocalMessage { msg_type: msg_type.clone() },
            ast::HatKind::NetworkMessage { msg_type, fields } => Hat::NetworkMessage { msg_type: msg_type.clone(), fields: fields.iter().map(|x| x.trans_name.clone()).collect() },
            ast::HatKind::OnKey { key } => Hat::OnKey {
                key: match key.as_str() {
                    "any key" => None,
                    "up arrow" => Some(KeyCode::Up),
                    "down arrow" => Some(KeyCode::Down),
                    "left arrow" => Some(KeyCode::Left),
                    "right arrow" => Some(KeyCode::Right),
                    "space" => Some(KeyCode::Char(' ')),
                    _ => {
                        let mut chars = key.chars();
                        let res = chars.next().map(|x| KeyCode::Char(x.to_ascii_lowercase())).ok_or_else(|| FromAstError::BadKeycode { key: key.clone() })?;
                        if chars.next().is_some() { return Err(FromAstError::BadKeycode { key: key.clone() }); }
                        Some(res)
                    }
                }
            },
            _ => return Err(FromAstError::UnsupportedEvent { kind: hat.clone() }),
        })
    }
}

#[derive(Collect)]
#[collect(no_drop, bound = "")]
struct ContextEntry<'gc, S: System> {
                               locals: SymbolTable<'gc, S>,
    #[collect(require_static)] barrier: Option<Barrier>,
    #[collect(require_static)] reply_key: Option<S::InternReplyKey>,
}

#[derive(Collect)]
#[collect(no_drop, bound = "")]
struct Script<'gc, S: System> {
    #[collect(require_static)] hat: Hat,
    #[collect(require_static)] code: Rc<ByteCode>,
    #[collect(require_static)] start_pos: usize,
                               entity: GcCell<'gc, Entity<'gc, S>>,
    #[collect(require_static)] process: Option<ProcessKey>,
                               context_queue: VecDeque<ContextEntry<'gc, S>>,
}
impl<'gc, S: System> Script<'gc, S> {
    fn consume_context(&mut self, state: &mut State<'gc, S>) {
        let process = self.process.and_then(|key| Some((key, state.processes.get_mut(key)?)));
        if process.as_ref().map(|x| x.1.is_running()).unwrap_or(false) { return }

        let ContextEntry { locals, barrier, reply_key } = match self.context_queue.pop_front() {
            Some(x) => x,
            None => return,
        };

        match process {
            Some((key, process)) => {
                debug_assert!(!state.process_queue.contains(&key));
                debug_assert_eq!(self.process, Some(key));

                process.initialize(locals, barrier, reply_key);
                state.process_queue.push_back(key);
            }
            None => {
                let mut process = Process::new(self.code.clone(), self.start_pos, state.global_context, self.entity, state.settings, state.system.clone());
                process.initialize(locals, barrier, reply_key);
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
    fn schedule(&mut self, state: &mut State<'gc, S>, locals: SymbolTable<'gc, S>, barrier: Option<Barrier>, reply_key: Option<S::InternReplyKey>, max_queue: usize) {
        self.context_queue.push_back(ContextEntry { locals, barrier, reply_key });
        self.consume_context(state);
        if self.context_queue.len() > max_queue {
            self.context_queue.pop_back();
        }
    }
}

#[derive(Collect)]
#[collect(no_drop, bound = "")]
struct State<'gc, S: System> {
    #[collect(require_static)] settings: Settings,
                               global_context: GcCell<'gc, GlobalContext<'gc, S>>,
                               processes: SlotMap<ProcessKey, Process<'gc, S>>,
    #[collect(require_static)] process_queue: VecDeque<ProcessKey>,
    #[collect(require_static)] system: Rc<S>,
}
#[derive(Collect)]
#[collect(no_drop, bound = "")]
pub struct Project<'gc, S: System> {
    state: State<'gc, S>,
    scripts: Vec<Script<'gc, S>>,
}
impl<'gc, S: System> Project<'gc, S> {
    pub fn new(global_context: GcCell<'gc, GlobalContext<'gc, S>>, settings: Settings, system: Rc<S>) -> Self {
        Self {
            state: State {
                global_context, settings, system,
                processes: Default::default(),
                process_queue: Default::default(),
            },
            scripts: Default::default(),
        }
    }
    pub fn add_script(&mut self, code: Rc<ByteCode>, start_pos: usize, entity: GcCell<'gc, Entity<'gc, S>>, hat: Option<Hat>) {
        match hat {
            Some(hat) => self.scripts.push(Script {
                code, start_pos, hat, entity,
                process: None,
                context_queue: Default::default(),
            }),
            None => {
                let process = Process::new(code, start_pos, self.state.global_context, entity, self.state.settings, self.state.system.clone());
                let key = self.state.processes.insert(process);
                self.state.process_queue.push_back(key);
            }
        }
    }
    pub fn input(&mut self, input: Input) {
        match input {
            Input::Start => {
                for script in self.scripts.iter_mut() {
                    if let Hat::OnFlag = &script.hat {
                        script.stop_all(&mut self.state);
                        script.schedule(&mut self.state, Default::default(), None, None, 0);
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
                            script.schedule(&mut self.state, Default::default(), None, None, 0);
                        }
                    }
                }
            }
            Input::KeyUp(_) => unimplemented!(),
        }
    }
    pub fn step(&mut self, mc: MutationContext<'gc, '_>) -> ProjectStep<'gc, S> {
        if let Some((msg_type, values, reply_key)) = self.state.system.receive_message() {
            let values: BTreeMap<_,_> = values.into_iter().collect();
            for script in self.scripts.iter_mut() {
                if let Hat::NetworkMessage { msg_type: script_msg_type, fields } = &script.hat {
                    if msg_type == *script_msg_type {
                        let mut context = SymbolTable::default();
                        for field in fields.iter() {
                            context.redefine_or_define(field,
                                values.get(field).map(|x| Value::from_json(mc, x.clone()).ok())
                                .flatten().unwrap_or_else(|| Number::new(0.0).unwrap().into()).into());
                        }
                        script.schedule(&mut self.state, context, None, reply_key.clone(), usize::MAX);
                    }
                }
            }
        }

        let (proc_key, proc) = loop {
            match self.state.process_queue.pop_front() {
                None => return ProjectStep::Idle,
                Some(proc_key) => if let Some(proc) = self.state.processes.get_mut(proc_key) { break (proc_key, proc) }
            }
        };

        match proc.step(mc) {
            Ok(x) => match x {
                ProcessStep::Normal => {
                    self.state.process_queue.push_front(proc_key);
                    ProjectStep::Normal
                }
                ProcessStep::Yield => {
                    self.state.process_queue.push_back(proc_key);
                    ProjectStep::Yield
                }
                ProcessStep::Terminate { .. } => ProjectStep::Normal,
                ProcessStep::Idle => unreachable!(),
                ProcessStep::Broadcast { msg_type, barrier } => {
                    for script in self.scripts.iter_mut() {
                        if let Hat::LocalMessage { msg_type: recv_type } = &script.hat {
                            if *recv_type == *msg_type {
                                script.stop_all(&mut self.state);
                                script.schedule(&mut self.state, Default::default(), barrier.clone(), None, 0);
                            }
                        }
                    }
                    self.state.process_queue.push_front(proc_key); // keep executing same process, if it was a wait, it'll yield next step
                    ProjectStep::Normal
                }
            }
            Err(error) => ProjectStep::Error {
                error,
                proc: self.state.processes.remove(proc_key).unwrap(),
            },
        }
    }
}
