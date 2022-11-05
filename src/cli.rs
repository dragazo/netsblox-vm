use std::prelude::v1::*;
use std::fs::File;
use std::rc::Rc;
use std::time::Duration;
use std::collections::VecDeque;
use std::cell::{Cell, RefCell};
use std::io::{self, Read, Write as IoWrite, stdout};
use std::fmt::Write as FmtWrite;
use std::sync::{Arc, Mutex};
use std::sync::mpsc::{channel, Sender, TryRecvError};
use std::{thread, mem, fmt, iter};

use clap::Parser;
use serde::Serialize;
use actix_web::{get, post, web, App, HttpServer, Responder, HttpResponse};
use actix_cors::Cors;

use crossterm::{cursor, execute, queue};
use crossterm::tty::IsTty;
use crossterm::event::{self, Event, KeyCode as RawKeyCode, KeyModifiers as RawKeyModifiers};
use crossterm::terminal::{self, ClearType};
use crossterm::style::{ResetColor, SetForegroundColor, Color, Print};

use crate::*;
use crate::gc::{GcCell, Collect, make_arena};
use crate::json::*;
use crate::bytecode::*;
use crate::runtime::*;
use crate::process::*;
use crate::project::*;

const STEPS_PER_IO_ITER: usize = 64;
const MAX_REQUEST_SIZE_BYTES: usize = 1024 * 1024 * 1024;
const YIELDS_BEFORE_IDLE_SLEEP: usize = 256;
const IDLE_SLEEP_TIME: Duration = Duration::from_micros(500);

struct IdleSleeper {
    yield_count: usize,
}
impl IdleSleeper {
    pub fn new() -> Self {
        IdleSleeper { yield_count: 0 }
    }
    pub fn consume<S: System>(&mut self, res: &ProjectStep<'_, S>) {
        match res {
            ProjectStep::Idle | ProjectStep::Yield => {
                self.yield_count += 1;
                if self.yield_count >= YIELDS_BEFORE_IDLE_SLEEP {
                    self.yield_count = 0;
                    thread::sleep(IDLE_SLEEP_TIME);
                }
            }
            ProjectStep::Normal | ProjectStep::Error { .. } => self.yield_count = 0,
        }
    }
}

macro_rules! crash {
    ($ret:literal : $($tt:tt)*) => {{
        eprint!($($tt)*);
        eprint!("\r\n");
        std::process::exit($ret);
    }}
}

struct AtExit<F: FnOnce()>(Option<F>);
impl<F: FnOnce()> AtExit<F> {
    fn new(f: F) -> Self { Self(Some(f)) }
}
impl<F: FnOnce()> Drop for AtExit<F> {
    fn drop(&mut self) {
        self.0.take().unwrap()()
    }
}

#[derive(Collect)]
#[collect(no_drop)]
struct Env<'gc> {
    proj: GcCell<'gc, Project<'gc, StdSystem>>,
    locs: InsLocations<String>,
}
make_arena!(EnvArena, Env);

/// Standard NetsBlox VM project actions that can be performed
#[derive(Parser, Debug)]
pub enum Mode {
    /// Compiles and runs a single project file
    Run {
        /// Path to the (xml) project file
        src: String,
        /// The specific role to run, or none if not ambiguous
        #[clap(long)]
        role: Option<String>,

        /// Address of the NetsBlox server (default: https://editor.netsblox.org)
        #[clap(long, default_value_t = String::from("https://editor.netsblox.org"))]
        server: String,
    },
    /// Compiles a single project file and dumps its disassembly to stdout
    Dump {
        /// Path to the (xml) project file
        src: String,
        /// The specific role to compile, or none if not ambiguous
        #[clap(long)]
        role: Option<String>,
    },
    /// Starts an execution server which you can connect to from the browser
    Start {
        /// Address of the NetsBlox server (default: https://editor.netsblox.org)
        #[clap(long, default_value_t = String::from("https://editor.netsblox.org"))]
        server: String,

        /// The address of this machine, which others use to send HTTP requests (default 127.0.0.1)
        #[clap(long, default_value_t = String::from("127.0.0.1"))]
        addr: String,
        /// The port to bind for the web server (default 6286)
        #[clap(long, default_value_t = 6286)]
        port: u16,
    },
}

pub enum SyscallMenu<'a> {
    Entry { label: &'a str },
    Submenu { label: &'a str, content: &'a [SyscallMenu<'a>] },
}
impl SyscallMenu<'_> {
    fn format(items: &[Self]) -> String {
        fn format_impl(value: &SyscallMenu, res: &mut String) {
            match value {
                SyscallMenu::Entry { label } => write!(res, "'{label}':'{label}',").unwrap(),
                SyscallMenu::Submenu { label, content } => {
                    write!(res, "'{label}':{{").unwrap();
                    for value in *content {
                        format_impl(value, res);
                    }
                    res.push('}');
                }
            }
        }
        let mut res = String::with_capacity(64);
        res.push('{');
        for item in items {
            format_impl(item, &mut res);
        }
        res.push('}');
        res
    }
}

#[derive(Debug)]
enum OpenProjectError<'a> {
    ParseError { error: ast::Error },
    RoleNotFound { role: &'a str },
    NoRoles,
    MultipleRoles { count: usize },
}
impl fmt::Display for OpenProjectError<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            OpenProjectError::ParseError { error } => write!(f, "failed to parse project: {error:?}"),
            OpenProjectError::RoleNotFound { role } => write!(f, "no role named '{role}'"),
            OpenProjectError::NoRoles => write!(f, "project had no roles"),
            OpenProjectError::MultipleRoles { count } => write!(f, "project had multiple ({count}) roles, but a specific role was not specified"),
        }
    }
}

fn read_file(src: &str) -> io::Result<String> {
    let mut file = File::open(src)?;
    let mut s = String::new();
    file.read_to_string(&mut s)?;
    Ok(s)
}
fn open_project<'a>(content: &str, role: Option<&'a str>) -> Result<(String, ast::Role), OpenProjectError<'a>> {
    let parsed = match ast::ParserBuilder::default().build().unwrap().parse(content) {
        Ok(x) => x,
        Err(error) => return Err(OpenProjectError::ParseError { error }),
    };
    let role = match role {
        Some(role) => match parsed.roles.into_iter().find(|x| x.name == role) {
            Some(x) => x,
            None => return Err(OpenProjectError::RoleNotFound { role }),
        }
        None => match parsed.roles.len() {
            0 => return Err(OpenProjectError::NoRoles),
            1 => parsed.roles.into_iter().next().unwrap(),
            count => return Err(OpenProjectError::MultipleRoles { count }),
        }
    };
    Ok((parsed.name, role))
}
fn get_env(role: &ast::Role) -> EnvArena {
    EnvArena::new(Default::default(), |mc| {
        let settings = Settings::builder().build().unwrap();
        let (proj, locs) = Project::from_ast(mc, role, settings);
        Env { proj: GcCell::allocate(mc, proj), locs: locs.instructions.transform(ToOwned::to_owned) }
    })
}

fn run_proj_tty(project_name: &str, server: String, mut env: EnvArena, overrides: StdSystemConfig) {
    terminal::enable_raw_mode().unwrap();
    execute!(stdout(), cursor::Hide).unwrap();
    let _tty_mode_guard = AtExit::new(|| {
        terminal::disable_raw_mode().unwrap();
        execute!(stdout(), cursor::Show).unwrap()
    });

    let old_panic_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |ctx| {
        let _ = terminal::disable_raw_mode();
        old_panic_hook(ctx);
    }));

    let update_flag = Rc::new(Cell::new(false));
    let input_queries = Rc::new(RefCell::new(VecDeque::new()));
    let mut term_size = terminal::size().unwrap();
    let mut input_value = String::new();

    let config = overrides.or(StdSystemConfig::builder()
        .print({
            let update_flag = update_flag.clone();
            Rc::new(move |value, entity| {
                if let Some(value) = value {
                    print!("{entity:?} > {value:?}\r\n");
                    update_flag.set(true);
                }
                Ok(())
            })
        })
        .input({
            let update_flag = update_flag.clone();
            let input_queries = input_queries.clone();
            Rc::new(move |_, key, prompt, entity| {
                input_queries.borrow_mut().push_back((format!("{entity:?} {prompt:?} > "), key));
                update_flag.set(true);
                Ok(())
            })
        })
        .build().unwrap());
    let system = StdSystem::new(server, Some(project_name), config);
    let mut idle_sleeper = IdleSleeper::new();
    print!("public id: {}\r\n", system.get_public_id());

    env.mutate(|mc, env| env.proj.write(mc).input(Input::Start, &system));

    let mut input_sequence = Vec::with_capacity(16);
    let in_input_mode = || !input_queries.borrow().is_empty();
    'program: loop {
        debug_assert_eq!(input_sequence.len(), 0);
        while event::poll(Duration::from_secs(0)).unwrap() {
            match event::read().unwrap() {
                Event::Key(key) => match key.code {
                    RawKeyCode::Char('c') if key.modifiers == RawKeyModifiers::CONTROL => break 'program,
                    RawKeyCode::Esc => input_sequence.push(Input::Stop),
                    RawKeyCode::Char(ch) => match in_input_mode() {
                        true => { input_value.push(ch); update_flag.set(true); }
                        false => input_sequence.push(Input::KeyDown(KeyCode::Char(ch.to_ascii_lowercase()))),
                    }
                    RawKeyCode::Backspace => if in_input_mode() && input_value.pop().is_some() { update_flag.set(true) }
                    RawKeyCode::Enter => if let Some((_, res_key)) = input_queries.borrow_mut().pop_front() {
                        system.finish_input(res_key, mem::take(&mut input_value));
                        update_flag.set(true);
                    }
                    RawKeyCode::Up => if !in_input_mode() { input_sequence.push(Input::KeyDown(KeyCode::Up)) }
                    RawKeyCode::Down => if !in_input_mode() { input_sequence.push(Input::KeyDown(KeyCode::Down)) }
                    RawKeyCode::Left => if !in_input_mode() { input_sequence.push(Input::KeyDown(KeyCode::Left)) }
                    RawKeyCode::Right => if !in_input_mode() { input_sequence.push(Input::KeyDown(KeyCode::Right)) }
                    _ => (),
                }
                Event::Resize(c, r) => {
                    term_size = (c, r);
                    update_flag.set(true);
                }
                _ => (),
            }
        }

        env.mutate(|mc, env| {
            let mut proj = env.proj.write(mc);
            for input in input_sequence.drain(..) { proj.input(input, &system); }
            for _ in 0..STEPS_PER_IO_ITER {
                let res = proj.step(mc, &system);
                idle_sleeper.consume(&res);
            }
        });

        if update_flag.get() {
            update_flag.set(false);

            queue!(stdout(),
                cursor::SavePosition,
                cursor::MoveTo(0, term_size.1 - 1),
                terminal::Clear(ClearType::CurrentLine)).unwrap();
            let queries = input_queries.borrow();
            if let Some((query, _)) = queries.front() {
                queue!(stdout(),
                    SetForegroundColor(Color::Blue),
                    Print(query),
                    ResetColor,
                    Print(&input_value)).unwrap();
            }
            queue!(stdout(), cursor::RestorePosition).unwrap();
            stdout().flush().unwrap();
        }
    }

    execute!(stdout(), terminal::Clear(ClearType::CurrentLine)).unwrap();
}
fn run_proj_non_tty(project_name: &str, server: String, mut env: EnvArena, overrides: StdSystemConfig) {
    let config = overrides.or(StdSystemConfig::builder()
        .print(Rc::new(move |value, entity| Ok(if let Some(value) = value { println!("{entity:?} > {value:?}") })))
        .build().unwrap());
    let system = StdSystem::new(server, Some(project_name), config);
    let mut idle_sleeper = IdleSleeper::new();
    println!("public id: {}", system.get_public_id());

    env.mutate(|mc, env| env.proj.write(mc).input(Input::Start, &system));

    loop {
        env.mutate(|mc, env| {
            let mut proj = env.proj.write(mc);
            for _ in 0..STEPS_PER_IO_ITER {
                let res = proj.step(mc, &system);
                idle_sleeper.consume(&res);
            }
        });
    }
}
fn run_server(nb_server: String, addr: String, port: u16, overrides: StdSystemConfig, syscalls: &[SyscallMenu<'_>]) {
    println!(r#"connect from {nb_server}/?extensions=["http://{addr}:{port}/extension.js"]"#);

    let extension_template = liquid::ParserBuilder::with_stdlib().build().unwrap().parse(include_str!("assets/extension.js")).unwrap();
    let extension = extension_template.render(&liquid::object!({
        "addr": addr,
        "port": port,
        "syscalls": SyscallMenu::format(syscalls),
    })).unwrap();

    let (proj_sender, proj_receiver) = channel();

    #[derive(Serialize)]
    struct Error {
        cause: String,
        entity: String,
        trace: Vec<String>,
    }
    struct State {
        extension: String,
        proj_sender: Mutex<Sender<String>>,
        output: Mutex<String>,
        errors: Mutex<Vec<Error>>,
    }
    let state = web::Data::new(State {
        extension,
        proj_sender: Mutex::new(proj_sender),
        output: Mutex::new(String::with_capacity(1024)),
        errors: Mutex::new(Vec::with_capacity(8)),
    });

    macro_rules! tee_println {
        ($state:expr => $($t:tt)*) => {{
            let content = format!($($t)*);
            if let Some(state) = $state {
                let mut output = state.output.lock().unwrap();
                output.push_str(&content);
                output.push('\n');
            }
            println!("{content}");
        }}
    }

    let weak_state = Arc::downgrade(&state);
    let config = overrides.or(StdSystemConfig::builder()
        .print(Rc::new(move |value, entity| Ok(if let Some(value) = value { tee_println!(weak_state.upgrade() => "{entity:?} > {value:?}") })))
        .build().unwrap());
    let system = StdSystem::new(nb_server, Some("native-server"), config);
    let mut idle_sleeper = IdleSleeper::new();
    println!("public id: {}", system.get_public_id());

    #[tokio::main(flavor = "multi_thread", worker_threads = 1)]
    async fn run_http(state: web::Data<State>, port: u16) {
        #[get("/extension.js")]
        async fn get_extension(state: web::Data<State>) -> impl Responder {
            HttpResponse::Ok().content_type("text/javascript").body(state.extension.clone())
        }

        #[get("/pull")]
        async fn pull_status(state: web::Data<State>) -> impl Responder {
            let mut output = state.output.lock().unwrap();
            let mut errors = state.errors.lock().unwrap();

            let res = HttpResponse::Ok().content_type("application/json").body(json!({
                "output": output.as_str(),
                "errors": errors.as_slice(),
            }).to_string());

            errors.clear();
            output.clear();
            res
        }

        #[post("/run")]
        async fn run_project(state: web::Data<State>, body: web::Bytes) -> impl Responder {
            match String::from_utf8(body.to_vec()) {
                Ok(content) => {
                    state.proj_sender.lock().unwrap().send(content).unwrap();
                    HttpResponse::Ok().content_type("text/plain").body("loaded project")
                }
                Err(_) => HttpResponse::BadRequest().content_type("text/plain").body("project was not valid utf8")
            }
        }

        HttpServer::new(move || {
            App::new()
                .wrap(Cors::permissive())
                .app_data(web::PayloadConfig::new(MAX_REQUEST_SIZE_BYTES))
                .app_data(state.clone())
                .service(get_extension)
                .service(pull_status)
                .service(run_project)
        })
        .workers(1)
        .bind(("localhost", port)).unwrap().run().await.unwrap();
    }
    let weak_state = Arc::downgrade(&state);
    thread::spawn(move || run_http(state, port));

    let (_, empty_role) = open_project(include_str!("assets/empty-proj.xml"), None).unwrap_or_else(|_| crash!(666: "default project failed to load"));
    let mut env = get_env(&empty_role);

    loop {
        match proj_receiver.try_recv() {
            Ok(content) => match open_project(&content, None) {
                Ok((proj_name, role)) => {
                    tee_println!(weak_state.upgrade() => "\n>>> loaded project '{proj_name}'\n");
                    env = get_env(&role);
                    env.mutate(|mc, env| env.proj.write(mc).input(Input::Start, &system));
                }
                Err(e) => tee_println!(weak_state.upgrade() => "\n>>> project load error: {e:?}\n>>> resuming previous project...\n"),
            }
            Err(TryRecvError::Disconnected) => break,
            Err(TryRecvError::Empty) => (),
        }

        env.mutate(|mc, env| {
            let mut proj = env.proj.write(mc);
            for _ in 0..STEPS_PER_IO_ITER {
                let res = proj.step(mc, &system);
                if let ProjectStep::Error { error, proc } = &res {
                    if let Some(state) = weak_state.upgrade() {
                        let entity = proc.get_entity().read().name.clone();
                        let call_stack = proc.get_call_stack();

                        let cause = format!("{:?}", error.cause);
                        tee_println!(Some(&state) => "\n>>> runtime error in entity {entity:?}: {cause:?}\n>>> see red error comments...\n");

                        let mut trace = Vec::with_capacity(call_stack.len() + 1);
                        for pos in call_stack[1..].iter().map(|x| x.called_from).chain(iter::once(error.pos)) {
                            if let Some(loc) = env.locs.lookup(pos) {
                                trace.push(loc.clone());
                            }
                        }

                        state.errors.lock().unwrap().push(Error { entity, cause, trace });
                    }
                }
                idle_sleeper.consume(&res);
            }
        });
    }
}

/// Runs a CLI client using the given [`Mode`] configuration.
pub fn run(mode: Mode, config: StdSystemConfig, syscalls: &[SyscallMenu]) {
    match mode {
        Mode::Run { src, role, server } => {
            let content = read_file(&src).unwrap_or_else(|_| crash!(1: "failed to read file '{src}'"));
            let (project_name, role) = open_project(&content, role.as_deref()).unwrap_or_else(|e| crash!(2: "{e}"));

            let env = get_env(&role);

            if stdout().is_tty() {
                run_proj_tty(&project_name, server, env, config);
            } else {
                run_proj_non_tty(&project_name, server, env, config);
            }
        }
        Mode::Dump { src, role } => {
            let content = read_file(&src).unwrap_or_else(|_| crash!(1: "failed to read file '{src}'"));
            let (_, role) = open_project(&content, role.as_deref()).unwrap_or_else(|e| crash!(2: "{e}"));

            let (bytecode, _) = ByteCode::compile(&role);
            println!("instructions:");
            bytecode.dump_code(&mut std::io::stdout().lock()).unwrap();
            println!("\ndata:");
            bytecode.dump_data(&mut std::io::stdout().lock()).unwrap();
            println!("\ntotal size: {}", bytecode.total_size());
        }
        Mode::Start { server, addr, port } => {
            run_server(server, addr, port, config, syscalls);
        }
    }
}
