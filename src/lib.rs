#![forbid(unsafe_code)]
#![no_std]

//! [NetsBlox](https://netsblox.org/) is a block-based programming language developed by Vanderbilt
//! which is based on [Snap!](https://snap.berkeley.edu/) from Berkeley.
//! NetsBlox adds several networking-related features, primarily the use of Remote Procedure Calls (RPCs)
//! that can access web-based resources and cloud utilities, as well as message passing between
//! NetsBlox projects running anywhere in the world.
//!
//! `netsblox_vm` is a pure rust implementation of the NetsBlox block-based code execution engine
//! which is written in safe, no_std Rust for use on arbitrary devices, including embedded applications.

extern crate no_std_compat as std;

pub mod bytecode;
pub mod runtime;
pub mod process;

#[cfg(test)] mod test;
