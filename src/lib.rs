#![forbid(unsafe_code)]
#![no_std]

//! [NetsBlox](https://netsblox.org/) is a block-based programming environment developed at [Vanderbilt](https://www.vanderbilt.edu/)
//! which is based on [Snap!](https://snap.berkeley.edu/) from Berkeley.
//! NetsBlox adds several networking-related features, in particular the use of Remote Procedure Calls (RPCs)
//! that can access web-based resources and cloud utilities, as well as message passing between
//! NetsBlox projects running anywhere in the world.
//!
//! `netsblox_vm` is a pure Rust implementation of the NetsBlox block-based code execution engine
//! which is written in safe, no_std Rust for use on arbitrary devices, including in embedded applications.
//! 
//! ## Features
//! | Name | Description | Default |
//! | ---- | ----------- | ------- |
//! | `std` | Link to the standard library. This gives access to the `StdSystem` implementation of [`System`](crate::runtime::System). | Disabled |
//! | `intern_strings` | Globally enable string interning for each new [`Value::String`](crate::runtime::Value::String) allocation within a project context. In general, this degrades performance, but could be useful in some embedded systems where memory is limited and there are many duplicate string values (e.g., from parsing a csv/json value) | Disabled |

extern crate no_std_compat as std;

macro_rules! trivial_from_impl {
    ($t:ident : $($f:ident),*$(,)?) => {$(
        impl From<$f> for $t { fn from(e: $f) -> $t { $t::$f(e) } }
    )*}
}

pub mod bytecode;
pub mod runtime;
pub mod process;

#[cfg(test)] mod test;
