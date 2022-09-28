use netsblox_vm::cli;
use clap::Parser;

fn main() {
    cli::run(cli::Mode::parse());
}
