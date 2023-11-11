use alloc::vec::Vec;
use alloc::boxed::Box;
use alloc::string::String;
use alloc::collections::{VecDeque, BTreeMap};
use alloc::rc::Rc;

use crate::*;
use crate::gc::*;
use crate::slotmap::*;
use crate::runtime::*;
use crate::bytecode::*;
use crate::process::*;

new_key! {
    struct ProcessKey;
}

/// A state machine that performs an action during idle periods.
/// 
/// This could be used to invoke [`std::thread::sleep`] during idle periods to save CPU time.
pub struct IdleAction {
    count: usize,
    thresh: usize,
    action: Box<dyn FnMut()>,
}
impl IdleAction {
    /// Creates a new [`IdleAction`] that triggers automatically after `max_yields` idle steps.
    pub fn new(thresh: usize, action: Box<dyn FnMut()>) -> Self {
        Self { count: 0, thresh, action }
    }
    /// Consumes a step result and advances the state machine.
    /// If the step resulting in an idle action, this may trigger the idle action to fire and reset the state machine.
    pub fn consume<C: CustomTypes<S>, S: System<C>>(&mut self, res: &ProjectStep<'_, C, S>) {
        match res {
            ProjectStep::Idle | ProjectStep::Yield | ProjectStep::Pause => {
                self.count += 1;
                if self.count >= self.thresh {
                    self.trigger();
                }
            }
            ProjectStep::Normal | ProjectStep::ProcessTerminated { .. } | ProjectStep::Error { .. } | ProjectStep::Watcher { .. } => self.count = 0,
        }
    }
    /// Explicitly triggers the idle action and reset the state machine.
    pub fn trigger(&mut self) {
        self.count = 0;
        self.action.as_mut()();
    }
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
    KeyDown { key: KeyCode },
    /// Simulates a key up hat from the keyboard.
    /// Due to the nature of the TTY interface, key up events are not always available, so this hat does not need to be sent.
    /// If not sent, a timeout is used to determine when a key is released (sending this hat can short-circuit the timeout).
    KeyUp { key: KeyCode },
    /// Trigger the execution of a custom event (hat) block script with the given set of message-style input variables.
    /// The `interrupt` flag can be set to cause any running scripts to stop and wipe their current queues, placing this new execution front and center.
    /// The `max_queue` field controls the maximum size of the context/schedule execution queue; beyond this size, this (and only this) execution will be dropped.
    CustomEvent { name: String, args: BTreeMap<String, SimpleValue>, interrupt: bool, max_queue: usize },
}

/// Result of stepping through the execution of a [`Project`].
pub enum ProjectStep<'gc, C: CustomTypes<S>, S: System<C>> {
    /// There were no running processes to execute.
    Idle,
    /// The project had a running process, which yielded.
    Yield,
    /// The project had a running process, which did any non-yielding operation.
    Normal,
    /// The project had a running process which terminated successfully.
    /// This can be though of as a special case of [`ProjectStep::Normal`],
    /// but also returns the result and process so it can be queried for state information if needed.
    ProcessTerminated { result: Option<Value<'gc, C, S>>, proc: Process<'gc, C, S> },
    /// The project had a running process, which encountered a runtime error.
    /// The dead process is returned, which can be queried for diagnostic information.
    Error { error: ExecError<C, S>, proc: Process<'gc, C, S> },
    /// The project had a running process that requested to create or destroy a watcher.
    /// See [`ProcessStep::Watcher`] for more details.
    Watcher { create: bool, watcher: Watcher<'gc, C, S> },
    /// The project had a running process that requested to pause execution of the (entire) project.
    /// See [`ProcessStep::Pause`] for more details.
    Pause,
}

#[derive(Collect)]
#[collect(no_drop, bound = "")]
struct Script<'gc, C: CustomTypes<S>, S: System<C>> {
    #[collect(require_static)] event: Rc<(Event, usize)>, // event and bytecode start pos
                               entity: Gc<'gc, RefLock<Entity<'gc, C, S>>>,
    #[collect(require_static)] process: Option<ProcessKey>,
                               context_queue: VecDeque<ProcContext<'gc, C, S>>,
}
impl<'gc, C: CustomTypes<S>, S: System<C>> Script<'gc, C, S> {
    fn consume_context(&mut self, state: &mut State<'gc, C, S>) {
        let process = self.process.and_then(|key| Some((key, state.processes.get_mut(key)?)));
        if process.as_ref().map(|x| x.1.is_running()).unwrap_or(false) { return }

        let context = match self.context_queue.pop_front() {
            Some(x) => x,
            None => return,
        };

        match process {
            Some((key, process)) => {
                debug_assert!(!state.process_queue.contains(&key));
                debug_assert_eq!(self.process, Some(key));

                process.initialize(context);
                state.process_queue.push_back(key);
            }
            None => {
                let mut process = Process::new(state.global_context, self.entity, self.event.1);
                process.initialize(context);
                let key = state.processes.insert(process);
                state.process_queue.push_back(key);
                self.process = Some(key);
            }
        }
    }
    fn stop_all(&mut self, state: &mut State<'gc, C, S>) {
        if let Some(process) = self.process.take() {
            state.processes.remove(process);
        }
        self.context_queue.clear();
    }
    fn schedule(&mut self, state: &mut State<'gc, C, S>, context: ProcContext<'gc, C, S>, max_queue: usize) {
        self.context_queue.push_back(context);
        self.consume_context(state);
        if self.context_queue.len() > max_queue {
            self.context_queue.pop_back();
        }
    }
}

struct AllContextsConsumer {
    did_it: bool,
}
impl AllContextsConsumer {
    fn new() -> Self {
        Self { did_it: false }
    }
    fn do_once<C: CustomTypes<S>, S: System<C>>(&mut self, proj: &mut Project<C, S>) {
        if !core::mem::replace(&mut self.did_it, true) {
            for script in proj.scripts.iter_mut() {
                script.consume_context(&mut proj.state);
            }
        }
    }
}

#[derive(Collect)]
#[collect(no_drop, bound = "")]
struct State<'gc, C: CustomTypes<S>, S: System<C>> {
                               global_context: Gc<'gc, RefLock<GlobalContext<'gc, C, S>>>,
                               processes: SlotMap<ProcessKey, Process<'gc, C, S>>,
    #[collect(require_static)] process_queue: VecDeque<ProcessKey>,
}
#[derive(Collect)]
#[collect(no_drop, bound = "")]
pub struct Project<'gc, C: CustomTypes<S>, S: System<C>> {
    state: State<'gc, C, S>,
    scripts: Vec<Script<'gc, C, S>>,
}
impl<'gc, C: CustomTypes<S>, S: System<C>> Project<'gc, C, S> {
    pub fn from_init(mc: &Mutation<'gc>, init_info: &InitInfo, bytecode: Rc<ByteCode>, settings: Settings, system: Rc<S>) -> Self {
        let global_context = GlobalContext::from_init(mc, init_info, bytecode, settings, system);
        let mut project = Self::new(Gc::new(mc, RefLock::new(global_context)));

        for entity_info in init_info.entities.iter() {
            let entity = *project.state.global_context.borrow().entities.get(&entity_info.name).unwrap();
            for (event, pos) in entity_info.scripts.iter() {
                project.add_script(*pos, entity, Some(event.clone()));
            }
        }

        project
    }
    pub fn new(global_context: Gc<'gc, RefLock<GlobalContext<'gc, C, S>>>) -> Self {
        Self {
            state: State {
                global_context,
                processes: Default::default(),
                process_queue: Default::default(),
            },
            scripts: Default::default(),
        }
    }
    pub fn add_script(&mut self, start_pos: usize, entity: Gc<'gc, RefLock<Entity<'gc, C, S>>>, event: Option<Event>) {
        let mut all_contexts_consumer = AllContextsConsumer::new();
        match event {
            Some(event) => self.scripts.push(Script {
                event: Rc::new((event, start_pos)),
                entity,
                process: None,
                context_queue: Default::default(),
            }),
            None => {
                let process = Process::new(self.state.global_context, entity, start_pos);
                let key = self.state.processes.insert(process);

                all_contexts_consumer.do_once(self); // need to consume all contexts before scheduling things in the future
                self.state.process_queue.push_back(key);
            }
        }
    }
    pub fn input(&mut self, mc: &Mutation<'gc>, input: Input) {
        let mut all_contexts_consumer = AllContextsConsumer::new();
        match input {
            Input::Start => {
                for i in 0..self.scripts.len() {
                    if let Event::OnFlag = &self.scripts[i].event.0 {
                        all_contexts_consumer.do_once(self); // need to consume all contexts before scheduling things in the future
                        self.scripts[i].stop_all(&mut self.state);
                        self.scripts[i].schedule(&mut self.state, Default::default(), 0);
                    }
                }
            }
            Input::CustomEvent { name, args, interrupt, max_queue } => {
                for i in 0..self.scripts.len() {
                    if let Event::Custom { name: script_event_name, fields } = &self.scripts[i].event.0 {
                        if name != *script_event_name { continue }

                        let mut locals = SymbolTable::default();
                        for field in fields.iter() {
                            let value = args.get(field).map(|x| Value::from_simple(mc, x.clone())).unwrap_or_else(|| Number::new(0.0).unwrap().into());
                            locals.define_or_redefine(field, value.into());
                        }

                        all_contexts_consumer.do_once(self); // need to consume all contexts before scheduling things in the future
                        if interrupt { self.scripts[i].stop_all(&mut self.state); }
                        self.scripts[i].schedule(&mut self.state, ProcContext { locals, ..Default::default() }, max_queue);
                    }
                }
            }
            Input::Stop => {
                for script in self.scripts.iter_mut() {
                    script.stop_all(&mut self.state);
                }
                self.state.processes.clear();
                self.state.process_queue.clear();
            }
            Input::KeyDown { key: input_key } => {
                for i in 0..self.scripts.len() {
                    if let Event::OnKey { key_filter } = &self.scripts[i].event.0 {
                        if key_filter.map(|x| x == input_key).unwrap_or(true) {
                            all_contexts_consumer.do_once(self); // need to consume all contexts before scheduling things in the future
                            self.scripts[i].schedule(&mut self.state, Default::default(), 0);
                        }
                    }
                }
            }
            Input::KeyUp { .. } => unimplemented!(),
        }
    }
    pub fn step(&mut self, mc: &Mutation<'gc>) -> ProjectStep<'gc, C, S> {
        let mut all_contexts_consumer = AllContextsConsumer::new();

        let msg = self.state.global_context.borrow().system.receive_message();
        if let Some(IncomingMessage { msg_type, values, reply_key }) = msg {
            let values: BTreeMap<_,_> = values.into_iter().collect();
            for i in 0..self.scripts.len() {
                if let Event::NetworkMessage { msg_type: script_msg_type, fields } = &self.scripts[i].event.0 {
                    if msg_type != *script_msg_type { continue }

                    let mut locals = SymbolTable::default();
                    for field in fields.iter() {
                        let value = values.get(field).map(|x| Value::from_simple(mc, x.clone())).unwrap_or_else(|| Number::new(0.0).unwrap().into());
                        locals.define_or_redefine(field, value.into());
                    }

                    all_contexts_consumer.do_once(self); // need to consume all contexts before scheduling things in the future
                    self.scripts[i].schedule(&mut self.state, ProcContext { locals, barrier: None, reply_key: reply_key.clone(), local_message: None }, usize::MAX);
                }
            }
        }

        let (proc_key, proc) = loop {
            match self.state.process_queue.pop_front() {
                None => {
                    debug_assert!(self.scripts.iter().all(|x| x.context_queue.is_empty()));
                    return ProjectStep::Idle;
                }
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
                    all_contexts_consumer.do_once(self); // need to consume all contexts before scheduling things in the future
                    self.state.process_queue.push_back(proc_key);
                    ProjectStep::Yield
                }
                ProcessStep::Watcher { create, watcher } => {
                    self.state.process_queue.push_front(proc_key);
                    ProjectStep::Watcher { create, watcher }
                }
                ProcessStep::Pause => {
                    self.state.process_queue.push_front(proc_key);
                    ProjectStep::Pause
                }
                ProcessStep::Fork { pos, locals, entity } => {
                    let mut proc = Process::new(ProcContext { global_context: self.state.global_context, entity, start_pos: pos, locals, barrier: None, reply_key: None, local_message: None });
                    let fork_proc_key = self.state.processes.insert(proc);

                    all_contexts_consumer.do_once(self); // need to consume all contexts before scheduling things in the future
                    self.state.process_queue.push_back(fork_proc_key); // forked process starts at end of exec queue
                    self.state.process_queue.push_front(proc_key); // keep executing the same process as before
                    ProjectStep::Normal
                }
                ProcessStep::CreatedClone { new_entity } => {
                    let original = new_entity.borrow().original.unwrap();
                    let mut new_scripts = vec![];
                    for script in self.scripts.iter() {
                        if Gc::ptr_eq(script.entity, original) {
                            new_scripts.push(Script {
                                event: script.event.clone(),
                                entity: new_entity,
                                process: None,
                                context_queue: Default::default(),
                            });
                        }
                    }
                    for script in new_scripts.iter_mut() {
                        if let Event::OnClone = &script.event.0 {
                            all_contexts_consumer.do_once(self); // need to consume all contexts before scheduling things in the future
                            script.schedule(&mut self.state, ProcContext::default(), 0);
                        }
                    }
                    self.scripts.extend(new_scripts);
                    self.state.process_queue.push_front(proc_key); // keep executing the same process as before
                    ProjectStep::Normal
                }
                ProcessStep::Broadcast { msg_type, barrier, targets } => {
                    for i in 0..self.scripts.len() {
                        if let Event::LocalMessage { msg_type: recv_type } = &self.scripts[i].event.0 {
                            if recv_type.as_ref().map(|x| *x == *msg_type).unwrap_or(true) {
                                if let Some(targets) = &targets {
                                    if !targets.iter().any(|&target| Gc::ptr_eq(self.scripts[i].entity, target)) {
                                        continue
                                    }
                                }

                                all_contexts_consumer.do_once(self); // need to consume all contexts before scheduling things in the future
                                self.scripts[i].stop_all(&mut self.state);
                                self.scripts[i].schedule(&mut self.state, ProcContext { locals: Default::default(), barrier: barrier.clone(), reply_key: None, local_message: Some(msg_type.clone()) }, 0);
                            }
                        }
                    }
                    self.state.process_queue.push_front(proc_key); // keep executing same process, if it was a wait, it'll yield next step
                    ProjectStep::Normal
                }
                ProcessStep::Terminate { result } => {
                    let proc = self.state.processes.remove(proc_key).unwrap();
                    all_contexts_consumer.do_once(self); // need to consume all contexts after dropping a process
                    ProjectStep::ProcessTerminated { result, proc }
                }
                ProcessStep::Idle => unreachable!(),
            }
            Err(error) => {
                let proc = self.state.processes.remove(proc_key).unwrap();
                all_contexts_consumer.do_once(self); // need to consume all contexts after dropping a process
                ProjectStep::Error { error, proc }
            }
        }
    }
    pub fn get_global_context(&self) -> Gc<'gc, RefLock<GlobalContext<'gc, C, S>>> {
        self.state.global_context
    }
}
