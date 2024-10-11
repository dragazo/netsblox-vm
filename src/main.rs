use core::cell::RefCell;
use core::fmt;

use std::rc::Rc;
use std::fs::{File, OpenOptions};
use std::io::{BufRead, Write, BufReader, BufWriter};

use netsblox_vm::cli::{run, Mode};
use netsblox_vm::template::SyscallMenu;
use netsblox_vm::runtime::{GetType, Value, Type, EntityKind, Request, RequestStatus, Config, CustomTypes, Key, SimpleValue, ProcessKind, Unwindable};
use netsblox_vm::std_system::StdSystem;
use netsblox_vm::gc::Mutation;
use netsblox_vm::compact_str::format_compact;
use clap::Parser;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NativeType {
    InputFile,
    OutputFile,
}

enum NativeValue {
    InputFile { handle: RefCell<Option<BufReader<File>>> },
    OutputFile { handle: RefCell<Option<BufWriter<File>>> },
}
impl fmt::Debug for NativeValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NativeValue::InputFile { .. } => write!(f, "[InputFile]"),
            NativeValue::OutputFile { .. } => write!(f, "[OutputFile]"),
        }
    }
}
impl GetType for NativeValue {
    type Output = NativeType;
    fn get_type(&self) -> Self::Output {
        match self {
            NativeValue::InputFile { .. } => NativeType::InputFile,
            NativeValue::OutputFile { .. } => NativeType::OutputFile,
        }
    }
}

struct EntityState;
impl From<EntityKind<'_, '_, C, StdSystem<C>>> for EntityState {
    fn from(_: EntityKind<'_, '_, C, StdSystem<C>>) -> Self {
        EntityState
    }
}

struct ProcessState;
impl From<ProcessKind<'_, '_, C, StdSystem<C>>> for ProcessState {
    fn from(_: ProcessKind<'_, '_, C, StdSystem<C>>) -> Self {
        ProcessState
    }
}
impl Unwindable for ProcessState {
    type UnwindPoint = ();
    fn get_unwind_point(&self) -> Self::UnwindPoint { }
    fn unwind_to(&mut self, _: &Self::UnwindPoint) { }
}

enum Intermediate {
    Simple(SimpleValue),
    Native(NativeValue),
}
impl From<SimpleValue> for Intermediate {
    fn from(value: SimpleValue) -> Self {
        Intermediate::Simple(value)
    }
}

struct C;
impl CustomTypes<StdSystem<C>> for C {
    type NativeValue = NativeValue;
    type Intermediate = Intermediate;

    type EntityState = EntityState;
    type ProcessState = ProcessState;

    fn from_intermediate<'gc>(mc: &Mutation<'gc>, value: Self::Intermediate) -> Value<'gc, C, StdSystem<C>> {
        match value {
            Intermediate::Simple(x) => Value::from_simple(mc, x),
            Intermediate::Native(x) => Value::Native(Rc::new(x)),
        }
    }
}

#[derive(Parser)]
struct Args {
    /// Enable file-system syscalls for any running projects
    #[clap(long, default_value_t = false)]
    fs: bool,

    #[command(subcommand)]
    mode: Mode,
}

fn main() {
    let args = Args::parse();

    let mut config = Config::<C, StdSystem<C>>::default();
    let mut syscalls = vec![];

    if args.fs {
        let new_config = Config::<C, StdSystem<C>> {
            request: Some(Rc::new(move |_, key, request, _| match &request {
                Request::Syscall { name, args } => match name.as_str() {
                    "open" => {
                        let (path, mode) = match args.as_slice() {
                            [path, mode] => match (path.as_text(), mode.as_text()) {
                                (Ok(path), Ok(mode)) => (path, mode),
                                _ => {
                                    key.complete(Err(format_compact!("syscall open - expected 2 string args, received {:?} and {:?}", path.get_type(), mode.get_type())));
                                    return RequestStatus::Handled;
                                }
                            }
                            _ => {
                                key.complete(Err(format_compact!("syscall open - expected 2 args, received {}", args.len())));
                                return RequestStatus::Handled;
                            }
                        };

                        let mut opts = OpenOptions::new();
                        match mode.as_ref() {
                            "r" => { opts.read(true); }
                            "w" => { opts.write(true).create(true).truncate(true); }
                            "a" => { opts.write(true).create(true).append(true); }
                            x => {
                                key.complete(Err(format_compact!("syscall open - unknown mode '{x}' expected 'r', 'w', or 'a'")));
                                return RequestStatus::Handled;
                            }
                        }

                        let file = match opts.open(path.as_ref()) {
                            Ok(x) => x,
                            Err(e) => {
                                key.complete(Err(format_compact!("syscall open - file open error: {e:?}")));
                                return RequestStatus::Handled;
                            }
                        };

                        let res = match mode.as_ref() {
                            "r" => NativeValue::InputFile { handle: RefCell::new(Some(BufReader::new(file))) },
                            "w" | "a" => NativeValue::OutputFile { handle: RefCell::new(Some(BufWriter::new(file))) },
                            _ => unreachable!(),
                        };

                        key.complete(Ok(Intermediate::Native(res)));
                        RequestStatus::Handled
                    }
                    "close" => match args.as_slice() {
                        [file] => match file {
                            Value::Native(x) => {
                                match &**x {
                                    NativeValue::InputFile { handle } => *handle.borrow_mut() = None,
                                    NativeValue::OutputFile { handle } => *handle.borrow_mut() = None,
                                }
                                key.complete(Ok(SimpleValue::Text("OK".into()).into()));
                                RequestStatus::Handled
                            }
                            _ => {
                                key.complete(Err(format_compact!("syscall readLine - expected type {:?} or {:?}, received type {:?}", NativeType::InputFile, NativeType::OutputFile, file.get_type())));
                                RequestStatus::Handled
                            }
                        }
                        _ => {
                            key.complete(Err(format_compact!("syscall close - expected 1 arg, received {}", args.len())));
                            RequestStatus::Handled
                        }
                    }
                    "readLine" => match args.as_slice() {
                        [file] => match file {
                            Value::Native(x) => match &**x {
                                NativeValue::InputFile { handle } => match handle.borrow_mut().as_mut() {
                                    Some(handle) => {
                                        let mut res = String::new();
                                        if let Err(e) = handle.read_line(&mut res) {
                                            key.complete(Err(format_compact!("syscall readLine - read error: {e:?}")));
                                            return RequestStatus::Handled;
                                        }

                                        key.complete(Ok(SimpleValue::Text(res.into()).into()));
                                        RequestStatus::Handled
                                    }
                                    None => {
                                        key.complete(Err("syscall readLine - this file has been closed".into()));
                                        RequestStatus::Handled
                                    }
                                }
                                _ => {
                                    key.complete(Err(format_compact!("syscall readLine - expected type {:?}, received type {:?}", NativeType::InputFile, file.get_type())));
                                    RequestStatus::Handled
                                }
                            }
                            _ => {
                                key.complete(Err(format_compact!("syscall readLine - expected type {:?}, received type {:?}", NativeType::InputFile, file.get_type())));
                                RequestStatus::Handled
                            }
                        }
                        _ => {
                            key.complete(Err(format_compact!("syscall readLine - expected 1 arg, received {}", args.len())));
                            RequestStatus::Handled
                        }
                    }
                    "writeLine" => match args.as_slice() {
                        [file, content] => match file {
                            Value::Native(x) => match &**x {
                                NativeValue::OutputFile { handle } => match handle.borrow_mut().as_mut() {
                                    Some(handle) => match writeln!(*handle, "{content}") {
                                        Ok(_) => {
                                            key.complete(Ok(SimpleValue::Text("OK".into()).into()));
                                            RequestStatus::Handled
                                        }
                                        Err(e) => {
                                            key.complete(Err(format_compact!("syscall writeLine - write error: {e:?}")));
                                            RequestStatus::Handled
                                        }
                                    }
                                    None => {
                                        key.complete(Err("syscall writeLine - this file has been closed".into()));
                                        RequestStatus::Handled
                                    }
                                }
                                _ => {
                                    key.complete(Err(format_compact!("syscall writeLine - expected types {:?} and {:?}. received types {:?} and {:?}", NativeType::OutputFile, Type::<C, StdSystem<C>>::Text, file.get_type(), Type::<C, StdSystem<C>>::Text)));
                                    RequestStatus::Handled
                                }
                            }
                            _ => {
                                key.complete(Err(format_compact!("syscall writeLine - expected types {:?} and {:?}. received types {:?} and {:?}", NativeType::OutputFile, Type::<C, StdSystem<C>>::Text, file.get_type(), content.get_type())));
                                RequestStatus::Handled
                            }
                        }
                        _ => {
                            key.complete(Err(format_compact!("syscall writeLine - expected 2 args, received {}", args.len())));
                            RequestStatus::Handled
                        }
                    }
                    _ => RequestStatus::UseDefault { key, request },
                }
                _ => RequestStatus::UseDefault { key, request },
            })),
            command: None,
        };
        config = new_config.fallback(&config);
        syscalls.extend([
            SyscallMenu::simple_entry("open".into()),
            SyscallMenu::simple_entry("close".into()),
            SyscallMenu::simple_entry("readLine".into()),
            SyscallMenu::simple_entry("writeLine".into()),
        ]);
    }
    run::<C>(args.mode, config, &syscalls);
}
