#![forbid(unsafe_code)]
#![no_std]

#![recursion_limit = "256"]

#![doc = include_str!("../README.md")]

#[cfg(feature = "std")]
#[macro_use]
extern crate std;

#[macro_use] extern crate alloc;
#[macro_use] extern crate num_derive;

use educe::Educe;

/// Re-exports of relevant items from `gc_arena`.
pub mod gc {
    pub use gc_arena::{self, Collect, Gc, GcWeak, StaticCollect, Mutation, Arena, Rootable, lock::RefLock};
}

/// Re-exports of relevant items from `serde_json`.
pub mod json {
    pub use serde_json::{self, Value as Json, Number as JsonNumber, Map as JsonMap, json, from_str as parse_json, from_slice as parse_json_slice};
}

/// Re-exports of relevant items from `time`.
pub mod real_time {
    pub use time::{self, OffsetDateTime, UtcOffset};
}

/// The re-exported version of the `compact-str` crate.
pub mod compact_str {
    pub use ::compact_str::{self, CompactString, ToCompactString, CompactStringExt, format_compact};
}

/// The re-exported version of the `netsblox-ast` crate.
pub use netsblox_ast as ast;

macro_rules! format_text {
    ($($t:tt)*) => {{
        $crate::runtime::Text::from(format!($($t)*).as_str())
    }};
}

pub mod bytecode;
pub mod slotmap;
pub mod vecmap;
pub mod runtime;
pub mod process;
pub mod project;
pub mod template;
mod util;

mod meta {
    include!(concat!(env!("OUT_DIR"), "/meta.rs"));
}

#[cfg(feature = "std")] pub mod std_util;
#[cfg(feature = "std-system")] pub mod std_system;
#[cfg(feature = "cli")] pub mod cli;

#[cfg(test)] mod test;
