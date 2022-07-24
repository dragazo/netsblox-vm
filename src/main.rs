use std::fs::File;
use std::io::Read;

use clap::Parser;

use netsblox_vm::bytecode::*;
use netsblox_vm::ast;

#[derive(Parser, Debug)]
struct Args {
    src: String,

    #[clap(long)]
    role: Option<String>,
}

fn main() {
    macro_rules! crash {
        ($ret:literal : $($tt:tt)*) => {{
            eprintln!($($tt)*);
            std::process::exit($ret);
        }}
    }

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
    let (code, locations) = ByteCode::compile(role);

    println!("{:#?}", locations);
}
