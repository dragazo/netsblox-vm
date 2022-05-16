#![forbid(unsafe_code)]
#![no_std]

extern crate no_std_compat as std;

mod engine;

#[cfg(test)]
mod test;

pub use engine::*;
