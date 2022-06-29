#![forbid(unsafe_code)]
#![no_std]

//! [NetsBlox](https://netsblox.org/) is a block-based programming environment developed at [Vanderbilt](https://www.vanderbilt.edu/)
//! which is based on [Snap!](https://snap.berkeley.edu/) from Berkeley.
//! NetsBlox adds several networking-related features, in particular the use of Remote Procedure Calls (RPCs)
//! that can access web-based resources and cloud utilities, as well as message passing between
//! NetsBlox projects running anywhere in the world.
//!
//! `netsblox_vm` is a pure Rust implementation of the NetsBlox block-based code execution engine
//! which is written in safe, `no_std` Rust for use on arbitrary devices, including in embedded applications.
//! This makes it possible to execute general block-based code on nearly any platform or environment with cross-compilation.
//!
//! # `no_std`
//! 
//! To use `netsblox_vm` in `no_std` Rust projects, simply pass the `default-features = false` flag to the project dependency.
//! Note that `alloc` is required in this case.
//! 
//! ```toml
//! [dependencies]
//! netsblox_vm = { version = "...", default-features = false }
//! ```
//! 
//! ## Features
//! 
//! | Name | Description | Default |
//! | ---- | ----------- | ------- |
//! | `std` | Link to the standard library. Among other benefits, this gives access to the `StdSystem` implementation of [`System`](crate::runtime::System), which works out of the box. | Enabled |

extern crate no_std_compat as std;

/// Re-exports of relevant items from `gc_arena`.
pub mod gc {
    pub use gc_arena::{Collect, Gc, GcCell, MutationContext, make_arena};
}

/// Re-exports of relevant items from `serde_json`.
pub mod json {
    pub use serde_json::{Value as Json, json};
}

pub mod bytecode;
// pub mod slotmap;
pub mod runtime;
pub mod process;
// pub mod project;

#[cfg(test)] mod test;
