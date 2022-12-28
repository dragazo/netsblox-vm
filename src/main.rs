use std::fs::{File, OpenOptions};
use std::io::{BufRead, Write, BufReader, BufWriter};
use std::rc::Rc;
use std::fmt;

use netsblox_vm::cli::{run, Mode, SyscallMenu};
use netsblox_vm::runtime::{GetType, Value, Type, ErrorCause, EntityKind, System, Request};
use netsblox_vm::std_system::{Config, CustomTypes, StdSystem, RequestStatus};
use netsblox_vm::gc::{GcCell, MutationContext, StaticCollect};
use netsblox_vm::json::{Json, json};
use clap::Parser;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NativeType {
    InputFile,
    OutputFile,
}

enum NativeValue {
    InputFile { handle: Option<BufReader<File>> },
    OutputFile { handle: Option<BufWriter<File>> },
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
impl<S: System> From<EntityKind<'_, '_, S>> for EntityState {
    fn from(_: EntityKind<'_, '_, S>) -> Self {
        EntityState
    }
}

enum Intermediate {
    Json(Json),
    Native(NativeValue),
}
impl From<Json> for Intermediate {
    fn from(value: Json) -> Self {
        Intermediate::Json(value)
    }
}

struct C;
impl CustomTypes for C {
    type NativeValue = NativeValue;
    type Intermediate = Intermediate;

    type EntityState = EntityState;

    fn from_intermediate<'gc>(mc: MutationContext<'gc, '_>, value: Self::Intermediate) -> Result<Value<'gc, StdSystem<Self>>, ErrorCause<StdSystem<Self>>> {
        Ok(match value {
            Intermediate::Json(x) => Value::from_json(mc, x)?,
            Intermediate::Native(x) => Value::Native(GcCell::allocate(mc, StaticCollect(x))),
        })
    }
}

fn main() {
    let config = Config {
        request: Some(Rc::new(move |_, mc, key, request, _| match &request {
            Request::Syscall { name, args } => match name.as_str() {
                "open" => {
                    let (path, mode) = match args.as_slice() {
                        [path, mode] => match (path.to_string(mc), mode.to_string(mc)) {
                            (Ok(path), Ok(mode)) => (path, mode),
                            _ => {
                                key.complete(Err(format!("syscall open - expected 2 string args, received {:?} and {:?}", path.get_type(), mode.get_type())));
                                return RequestStatus::Handled;
                            }
                        }
                        _ => {
                            key.complete(Err(format!("syscall open - expected 2 args, received {}", args.len())));
                            return RequestStatus::Handled;
                        }
                    };

                    let mut opts = OpenOptions::new();
                    match mode.as_str() {
                        "r" => { opts.read(true); }
                        "w" => { opts.write(true).create(true).truncate(true); }
                        "a" => { opts.write(true).create(true).append(true); }
                        x => {
                            key.complete(Err(format!("syscall open - unknown mode '{x}' expected 'r', 'w', or 'a'")));
                            return RequestStatus::Handled;
                        }
                    }

                    let file = match opts.open(path.as_str()) {
                        Ok(x) => x,
                        Err(e) => {
                            key.complete(Err(format!("syscall open - file open error: {e:?}")));
                            return RequestStatus::Handled;
                        }
                    };

                    let res = match mode.as_str() {
                        "r" => NativeValue::InputFile { handle: Some(BufReader::new(file)) },
                        "w" | "a" => NativeValue::OutputFile { handle: Some(BufWriter::new(file)) },
                        _ => unreachable!(),
                    };

                    key.complete(Ok(Intermediate::Native(res)));
                    RequestStatus::Handled
                }
                "close" => match args.as_slice() {
                    [file] => match file {
                        Value::Native(x) => {
                            match &mut x.write(mc).0 {
                                NativeValue::InputFile { handle } => *handle = None,
                                NativeValue::OutputFile { handle } => *handle = None,
                            }
                            key.complete(Ok(json!("OK").into()));
                            return RequestStatus::Handled;
                        }
                        _ => {
                            key.complete(Err(format!("syscall readLine - expected type {:?} or {:?}, received type {:?}", NativeType::InputFile, NativeType::OutputFile, file.get_type())));
                            return RequestStatus::Handled;
                        }
                    }
                    _ => {
                        key.complete(Err(format!("syscall close - expected 1 arg, received {}", args.len())));
                        return RequestStatus::Handled;
                    }
                }
                "readLine" => match args.as_slice() {
                    [file] => match file {
                        Value::Native(x) => match &mut x.write(mc).0 {
                            NativeValue::InputFile { handle } => match handle.as_mut() {
                                Some(handle) => {
                                    let mut res = String::new();
                                    if let Err(e) = handle.read_line(&mut res) {
                                        key.complete(Err(format!("syscall readLine - read error: {e:?}")));
                                        return RequestStatus::Handled;
                                    }

                                    key.complete(Ok(json!(res).into()));
                                    return RequestStatus::Handled;
                                }
                                None => {
                                    key.complete(Err(format!("syscall readLine - this file has been closed")));
                                    return RequestStatus::Handled;
                                }
                            }
                            _ => {
                                key.complete(Err(format!("syscall readLine - expected type {:?}, received type {:?}", NativeType::InputFile, file.get_type())));
                                return RequestStatus::Handled;
                            }
                        }
                        _ => {
                            key.complete(Err(format!("syscall readLine - expected type {:?}, received type {:?}", NativeType::InputFile, file.get_type())));
                            return RequestStatus::Handled;
                        }
                    }
                    _ => {
                        key.complete(Err(format!("syscall readLine - expected 1 arg, received {}", args.len())));
                        return RequestStatus::Handled;
                    }
                }
                "writeLine" => match args.as_slice() {
                    [file, content] => match (file, content.to_string(mc)) {
                        (Value::Native(x), Ok(content)) => match &mut x.write(mc).0 {
                            NativeValue::OutputFile { handle } => match handle.as_mut() {
                                Some(handle) => match writeln!(*handle, "{content}") {
                                    Ok(_) => {
                                        key.complete(Ok(Intermediate::Json(json!("OK"))));
                                        return RequestStatus::Handled;
                                    }
                                    Err(e) => {
                                        key.complete(Err(format!("syscall writeLine - write error: {e:?}")));
                                        return RequestStatus::Handled;
                                    }
                                }
                                None => {
                                    key.complete(Err(format!("syscall writeLine - this file has been closed")));
                                    return RequestStatus::Handled;
                                }
                            }
                            _ => {
                                key.complete(Err(format!("syscall writeLine - expected types {:?} and {:?}. received types {:?} and {:?}", NativeType::OutputFile, Type::<StdSystem<C>>::String, file.get_type(), Type::<StdSystem<C>>::String)));
                                return RequestStatus::Handled;
                            }
                        }
                        _ => {
                            key.complete(Err(format!("syscall writeLine - expected types {:?} and {:?}. received types {:?} and {:?}", NativeType::OutputFile, Type::<StdSystem<C>>::String, file.get_type(), content.get_type())));
                            return RequestStatus::Handled;
                        }
                    }
                    _ => {
                        key.complete(Err(format!("syscall writeLine - expected 2 args, received {}", args.len())));
                        return RequestStatus::Handled;
                    }
                }
                _ => RequestStatus::UseDefault { key, request },
            }
            _ => RequestStatus::UseDefault { key, request },
        })),
        command: None,
    };
    run::<C>(Mode::parse(), config, &[
        SyscallMenu::Entry { label: "open" },
        SyscallMenu::Entry { label: "close" },
        SyscallMenu::Entry { label: "readLine" },
        SyscallMenu::Entry { label: "writeLine" },
    ]);
}
