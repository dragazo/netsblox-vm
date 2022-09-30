use netsblox_vm::cli::{run, Mode};
use netsblox_vm::runtime::StdSystemConfig;
use clap::Parser;

fn main() {
    run(Mode::parse(), StdSystemConfig::builder().build().unwrap(), &[]);
}
