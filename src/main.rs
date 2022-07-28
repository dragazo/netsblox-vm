use std::fs::File;
use std::rc::Rc;
use std::io::Read;

use clap::Parser;

use netsblox_vm::*;
use netsblox_vm::gc::{GcCell, Collect, make_arena};
use netsblox_vm::bytecode::*;
use netsblox_vm::runtime::*;
use netsblox_vm::process::*;
use netsblox_vm::project::*;

macro_rules! crash {
    ($ret:literal : $($tt:tt)*) => {{
        eprintln!($($tt)*);
        std::process::exit($ret);
    }}
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

fn main() {
    match Mode::parse() {
        Mode::Run { src, role, server } => {
            let (project_name, role) = open_project(&src, role.as_deref());

            let mut env = EnvArena::new(Default::default(), |mc| {
                let settings = SettingsBuilder::default()
                    .printer(Rc::new(|value, entity| if let Some(value) = value { println!("{:?} > {:?}", entity, value) }))
                    .build().unwrap();

                let mut proj = Project::from_ast(mc, &role, settings);
                proj.input(Input::Start);
                Env { proj: GcCell::allocate(mc, proj) }
            });
            let system = StdSystem::new(server, Some(&project_name));

            env.mutate(|mc, env| {
                let mut proj = env.proj.write(mc);
                loop {
                    match proj.step(mc, &system) {
                        ProjectStep::Idle => return,
                        ProjectStep::Normal => (),
                    }
                }
            });
        }
        Mode::Dump { src, role } => {
            let (_, role) = open_project(&src, role.as_deref());
            let (code, _) = ByteCode::compile(&role);
            code.dump(&mut std::io::stdout().lock()).unwrap();
        }
    }
}
