#![forbid(unsafe_code)]
#![no_std]

#![doc = include_str!("../README.md")]

extern crate no_std_compat as std;

#[macro_use] extern crate num_derive;
pub(crate) use educe::Educe;

/// Re-exports of relevant items from `gc_arena`.
pub mod gc {
    pub use gc_arena::{Collect, Gc, GcCell, StaticCollect, MutationContext, Arena, Rootable};
}

/// Re-exports of relevant items from `serde_json`.
pub mod json {
    pub use serde_json::{Value as Json, json};
}

/// The re-exported version of the `netsblox-ast` crate.
pub use netsblox_ast as ast;

pub mod bytecode;
pub mod slotmap;
pub mod runtime;
pub mod process;
pub mod project;

#[cfg(any(test, feature = "std"))] pub mod std_system;
#[cfg(feature = "cli")] pub mod cli;

#[cfg(test)] mod test;
