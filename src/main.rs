use netsblox_vm::cli::*;
use clap::Parser;

fn main() {
    run(Mode::parse());
}
