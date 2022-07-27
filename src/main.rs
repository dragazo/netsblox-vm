use std::fs::File;
use std::rc::Rc;
use std::io::Read;

use clap::Parser;

use netsblox_vm::*;
use netsblox_vm::gc::{GcCell, Collect, make_arena};
use netsblox_vm::runtime::*;
use netsblox_vm::process::*;
use netsblox_vm::project::*;

#[derive(Collect)]
#[collect(no_drop)]
struct Env<'gc> {
    proj: GcCell<'gc, Project<'gc, StdSystem>>,
}
make_arena!(EnvArena, Env);

#[derive(Parser, Debug)]
struct Args {
    src: String,

    #[clap(long)]
    role: Option<String>,

    #[clap(long, default_value_t = String::from("https://editor.netsblox.org"))]
    server: String,
}

fn main() {
    macro_rules! crash {
        ($ret:literal : $($tt:tt)*) => {{
            eprintln!($($tt)*);
            std::process::exit($ret);
        }}
    }

    let hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |panic_info| {
        hook(panic_info);
        crash!(666: "unrecoverable error");
    }));

    let args = Args::parse();
    let content = match File::open(&args.src) {
        Ok(mut x) => {
            let mut s = String::new();
            x.read_to_string(&mut s).unwrap();
            s
        }
        Err(e) => crash!(1: "failed to open '{}' for reading:\n{e:?}", args.src),
    };
    let parsed = match ast::ParserBuilder::default().build().unwrap().parse(&content) {
        Ok(x) => x,
        Err(e) => crash!(2: "failed to parse '{}' as a NetsBlox project file:\n{e:?}", args.src),
    };
    let role = match args.role.as_deref() {
        Some(role) => match parsed.roles.iter().find(|x| x.name == role) {
            Some(x) => x,
            None => crash!(3: "project had no role named '{role}'"),
        }
        None => match parsed.roles.as_slice() {
            [] => crash!(4: "project has no roles"),
            [x] => x,
            _ => crash!(5: "project has multiple roles and a specific role was not specified"),
        }
    };
    let mut env = EnvArena::new(Default::default(), |mc| {
        let settings = SettingsBuilder::default()
            .printer(Rc::new(|value, entity| if let Some(value) = value { println!("{:?} > {:?}", entity, value) }))
            .build().unwrap();

        let mut proj = Project::from_ast(mc, role, settings);
        proj.input(Input::Start);
        Env { proj: GcCell::allocate(mc, proj) }
    });
    let system = StdSystem::new(args.server, Some(&parsed.name));

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
