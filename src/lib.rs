#![forbid(unsafe_code)]
#![no_std]

extern crate no_std_compat as std;

mod bytecode;
mod engine;

pub use engine::*;
