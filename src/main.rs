use std::fs::File;
use std::rc::Rc;
use std::time::Duration;
use std::collections::VecDeque;
use std::cell::{Cell, RefCell};
use std::io::{Read, Write, stdout, stderr};
use std::mem;

use clap::Parser;

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

macro_rules! crash {
    ($ret:literal : $($tt:tt)*) => {{
        write!(stderr(), $($tt)*).unwrap();
        write!(stderr(), "\r\n").unwrap();
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
    Run {
        src: String,
        #[clap(long)] role: Option<String>,

        #[clap(long, default_value_t = String::from("https://editor.netsblox.org"))]
        server: String,
    },
    Dump {
        src: String,
        #[clap(long)] role: Option<String>,
    }
}

fn open_project(src: &str, role: Option<&str>) -> (String, ast::Role) {
    let content = match File::open(src) {
        Ok(mut x) => {
            let mut s = String::new();
            x.read_to_string(&mut s).unwrap();
            s
        }
        Err(e) => crash!(1: "failed to open '{}' for reading:\n{e:?}", src),
    };
    let parsed = match ast::ParserBuilder::default().build().unwrap().parse(&content) {
        Ok(x) => x,
        Err(e) => crash!(2: "failed to parse '{}' as a NetsBlox project file:\n{e:?}", src),
    };
    let role = match role {
        Some(role) => match parsed.roles.into_iter().find(|x| x.name == role) {
            Some(x) => x,
            None => crash!(3: "project had no role named '{role}'"),
        }
        None => match parsed.roles.len() {
            0 => crash!(4: "project has no roles"),
            1 => parsed.roles.into_iter().next().unwrap(),
            _ => crash!(5: "project has multiple roles and a specific role was not specified"),
        }
    };
    (parsed.name, role)
}

fn run_proj_tty(project_name: &str, server: String, mut env: EnvArena) {
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
                    write!(stdout(), "{entity:?} > {value:?}\r\n").unwrap();
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
            proj.step(mc, &system)
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
fn run_proj_non_tty(project_name: &str, server: String, mut env: EnvArena) {
    let config = StdSystemConfig::builder()
        .print(Rc::new(move |value, entity| { if let Some(value) = value { println!("{entity:?} > {value:?}") } }))
        .build().unwrap();
    let system = StdSystem::new(server, Some(project_name), config);

    env.mutate(|mc, env| env.proj.write(mc).input(Input::Start, &system));

    loop {
        env.mutate(|mc, env| {
            let mut proj = env.proj.write(mc);
            proj.step(mc, &system)
        });
    }
}

fn main() {
    match Mode::parse() {
        Mode::Run { src, role, server } => {
            let (project_name, role) = open_project(&src, role.as_deref());
            let env = EnvArena::new(Default::default(), |mc| {
                let settings = Settings::builder().build().unwrap();
                let proj = Project::from_ast(mc, &role, settings);
                Env { proj: GcCell::allocate(mc, proj) }
            });

            if stdout().is_tty() {
                run_proj_tty(&project_name, server, env);
            } else {
                run_proj_non_tty(&project_name, server, env);
            }
        }
        Mode::Dump { src, role } => {
            let (_, role) = open_project(&src, role.as_deref());
            let (bytecode, _) = ByteCode::compile(&role);
            println!("instructions:");
            bytecode.dump_code(&mut std::io::stdout().lock()).unwrap();
            println!("\ndata:");
            bytecode.dump_data(&mut std::io::stdout().lock()).unwrap();
            println!("\ntotal size: {}", bytecode.total_size());
        }
    }
}
