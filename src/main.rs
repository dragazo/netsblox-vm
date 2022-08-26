use std::fs::File;
use std::rc::Rc;
use std::time::Duration;
use std::collections::VecDeque;
use std::cell::{Cell, RefCell};
use std::io::{self, Read, Write, stdout};
use std::sync::{Arc, Mutex, Condvar};
use std::sync::atomic::{AtomicBool, Ordering as MemOrder};
use std::{thread, mem, fmt};

use clap::Parser;
use actix_web::{get, post, web, App, HttpServer, Responder, HttpResponse};

use crossterm::{cursor, execute, queue};
use crossterm::tty::IsTty;
use crossterm::event::{self, Event, KeyCode as RawKeyCode, KeyModifiers as RawKeyModifiers};
use crossterm::terminal::{self, ClearType};
use crossterm::style::{ResetColor, SetForegroundColor, Color, Print};

use netsblox_vm::*;
use netsblox_vm::gc::{GcCell, Collect, make_arena};
use netsblox_vm::bytecode::*;
use netsblox_vm::runtime::*;
use netsblox_vm::process::*;
use netsblox_vm::project::*;

const STEPS_PER_IO_ITER: usize = 32;

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
}
make_arena!(EnvArena, Env);

#[derive(Parser, Debug)]
enum Mode {
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
        let proj = Project::from_ast(mc, role, settings);
        Env { proj: GcCell::allocate(mc, proj) }
    })
}

trait StopFlag {
    fn should_stop(&self) -> bool;
}
struct NeverStop;
impl StopFlag for NeverStop {
    fn should_stop(&self) -> bool { false }
}
impl StopFlag for Arc<AtomicBool> {
    fn should_stop(&self) -> bool { self.load(MemOrder::SeqCst) }
}

fn run_proj_tty<T: StopFlag>(project_name: &str, server: String, mut env: EnvArena, stop_flag: T) {
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

    let config = StdSystemConfig::builder()
        .print({
            let update_flag = update_flag.clone();
            Rc::new(move |value, entity| {
                if let Some(value) = value {
                    print!("{entity:?} > {value:?}\r\n");
                    update_flag.set(true);
                }
            })
        })
        .input({
            let update_flag = update_flag.clone();
            let input_queries = input_queries.clone();
            Rc::new(move |prompt, entity, key| {
                input_queries.borrow_mut().push_back((format!("{entity:?} {prompt:?} > "), key));
                update_flag.set(true);
            })
        })
        .build().unwrap();
    let system = StdSystem::new(server, Some(project_name), config);
    print!("public id: {}\r\n", system.get_public_id());

    env.mutate(|mc, env| env.proj.write(mc).input(Input::Start, &system));

    let mut input_sequence = Vec::with_capacity(16);
    let in_input_mode = || !input_queries.borrow().is_empty();
    'program: loop {
        if stop_flag.should_stop() { break }

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
                proj.step(mc, &system);
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
fn run_proj_non_tty<T: StopFlag>(project_name: &str, server: String, mut env: EnvArena, stop_flag: T) {
    let config = StdSystemConfig::builder()
        .print(Rc::new(move |value, entity| { if let Some(value) = value { println!("{entity:?} > {value:?}") } }))
        .build().unwrap();
    let system = StdSystem::new(server, Some(project_name), config);
    println!("public id: {}", system.get_public_id());

    env.mutate(|mc, env| env.proj.write(mc).input(Input::Start, &system));

    loop {
        if stop_flag.should_stop() { break }

        env.mutate(|mc, env| {
            let mut proj = env.proj.write(mc);
            for _ in 0..STEPS_PER_IO_ITER {
                proj.step(mc, &system);
            }
        });
    }
}
#[tokio::main(flavor = "multi_thread", worker_threads = 1)]
async fn run_server(nb_server: String, addr: String, port: u16) {
    println!(r#"connect from {nb_server}/?extensions=["http://{addr}:{port}/extension.js"]"#);

    let extension_template = liquid::ParserBuilder::with_stdlib().build().unwrap().parse(include_str!("assets/extension.js")).unwrap();
    let extension = extension_template.render(&liquid::object!({
        "addr": addr,
        "port": port,
    })).unwrap();

    struct State {
        nb_server: String,
        extension: String,
        project: Mutex<Option<(String, ast::Role)>>,
        project_cond: Condvar,
        stop_flag: Arc<AtomicBool>,
    }
    let state = web::Data::new(State {
        nb_server, extension,
        project: Mutex::new(None),
        project_cond: Condvar::new(),
        stop_flag: Arc::new(AtomicBool::new(false)),
    });

    fn project_runner(state: web::Data<State>) {
        loop {
            let (project_name, role) = {
                let mut project_lock = state.project.lock().unwrap();
                loop {
                    match project_lock.take() {
                        Some(x) => break x,
                        None => project_lock = state.project_cond.wait(project_lock).unwrap(),
                    }
                }
            };
            state.stop_flag.store(false, MemOrder::SeqCst);

            let env = get_env(&role);
            run_proj_non_tty(&project_name, state.nb_server.clone(), env, state.stop_flag.clone());
        }
    }
    let state_clone = state.clone();
    thread::spawn(move || project_runner(state_clone));

    #[get("/extension.js")]
    async fn get_extension(state: web::Data<State>) -> impl Responder {
        HttpResponse::Ok()
            .content_type("text/javascript")
            .body(state.extension.clone())
    }

    #[post("/run")]
    async fn run_project(state: web::Data<State>, body: web::Bytes) -> impl Responder {
        match String::from_utf8(body.to_vec()) {
            Ok(content) => {
                match open_project(&content, None) {
                    Ok(x) => {
                        let mut project_lock = state.project.lock().unwrap();
                        *project_lock = Some(x);
                        state.project_cond.notify_all();
                        state.stop_flag.store(true, MemOrder::SeqCst);
                        HttpResponse::Ok().body("loaded project")
                    }
                    Err(e) => HttpResponse::BadRequest().body(format!("failed to load project: {e}")),
                }
            }
            Err(_) => HttpResponse::BadRequest().body("project was not valid utf8")
        }
    }

    HttpServer::new(move || {
        App::new()
            .app_data(state.clone())
            .service(get_extension)
            .service(run_project)
    })
    .workers(1)
    .bind(("localhost", port)).unwrap().run().await.unwrap();
}

fn main() {
    match Mode::parse() {
        Mode::Run { src, role, server } => {
            let content = read_file(&src).unwrap_or_else(|_| crash!(1: "failed to read file '{src}'"));
            let (project_name, role) = open_project(&content, role.as_deref()).unwrap_or_else(|e| crash!(2: "{e}"));

            let env = get_env(&role);

            if stdout().is_tty() {
                run_proj_tty(&project_name, server, env, NeverStop);
            } else {
                run_proj_non_tty(&project_name, server, env, NeverStop);
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
            run_server(server, addr, port);
        }
    }
}
