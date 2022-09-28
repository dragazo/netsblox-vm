# NetsBlox-VM

[NetsBlox](https://netsblox.org/) is a browser-based visual programming environment (based on [Snap!](https://snap.berkeley.edu/)) that extends the typical block-based programming features with internet and distributed computing tools such as RPCs (remote procedure calls) that access network resources (e.g., databases), and message passing between projects over the internet.

NetsBlox-VM is a native Rust implementation of the NetsBlox code execution engine and runtime. This makes it possible to execute NetsBlox program code at blistering speeds on any device targeted by the Rust compiler. But more importantly, NetsBlox-VM has several extension APIs which make it possible to extend its features with new hardware peripheral access capabilities (e.g., controlling sensors and actuators through GPIO), all with safe, native Rust.

## Features

NetsBlox-VM contains the following feature flags.

| name | default | description |
| ---- | ------- | ----------- |
| `std`  | on | Enables the `std` crate dependency and access to the default `netsblox_vm::runtime::StdSystem` implementation of `netsblox_vm::runtime::System` |
| `cli` | off | Enables the `std` feature flag and additionally gives access to `netsblox_vm::cli`, which gives API access to the standard CLI (needed for syscall extensions) |

## `no-std`

NetsBlox-VM supports building in `no-std` environments by disabling the default `std` feature flag via

```toml
[dependencies]
netsblox_vm = { version = "...", default-features = false }
```

Note that this precludes access to `netsblox_vm::runtime::StdSystem`, meaning a new implementation of `netsblox_vm::runtime::System` would be required for your target platform.

## CLI Installation

This crate includes a binary called `nb` which serves as a shallow wrapper for the `netsblox_vm::cli` API with a default suite of syscall extensions.
_Note: if you need to create your own syscall extensions, you must do so in a separate binary using this crate as a dependency._

To install the standard CLI, you can use one of the following commands

```bash
# to build from source
cargo build --release --features=cli

# to install from source
cargo install --path . --features=cli

# to install from crates.io latest release
cargo install netsblox-vm --features=cli
```
