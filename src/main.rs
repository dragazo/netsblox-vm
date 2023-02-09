use std::fs::{File, OpenOptions};
use std::io::{BufRead, Write, BufReader, BufWriter};
use std::cell::RefCell;
use std::rc::Rc;
use std::fmt;

use netsblox_vm::cli::{run, Mode};
use netsblox_vm::template::SyscallMenu;
use netsblox_vm::runtime::{GetType, Value, Type, ErrorCause, EntityKind, System, Request, RequestStatus, Config};
use netsblox_vm::std_system::{CustomTypes, StdSystem, IntermediateType};
use netsblox_vm::gc::MutationContext;
use netsblox_vm::json::{Json, json};
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
impl<S: System> From<EntityKind<'_, '_, S>> for EntityState {
    fn from(_: EntityKind<'_, '_, S>) -> Self {
        EntityState
    }
}

enum Intermediate {
    Json(Json),
    Image(Vec<u8>),
    Native(NativeValue),
}
impl IntermediateType for Intermediate {
    fn from_json(json: Json) -> Self {
        Self::Json(json)
    }
    fn from_image(img: Vec<u8>) -> Self {
        Self::Image(img)
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
            Intermediate::Image(x) => Value::Image(Rc::new(x)),
            Intermediate::Native(x) => Value::Native(Rc::new(x)),
        })
    }
}

fn main() {
    let config = Config::<StdSystem<_>> {
        request: Some(Rc::new(move |_, _, key, request, _| match &request {
            Request::Syscall { name, args } => match name.as_str() {
                "open" => {
                    let (path, mode) = match args.as_slice() {
                        [path, mode] => match (path.to_string(), mode.to_string()) {
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
                    match mode.as_ref() {
                        "r" => { opts.read(true); }
                        "w" => { opts.write(true).create(true).truncate(true); }
                        "a" => { opts.write(true).create(true).append(true); }
                        x => {
                            key.complete(Err(format!("syscall open - unknown mode '{x}' expected 'r', 'w', or 'a'")));
                            return RequestStatus::Handled;
                        }
                    }

                    let file = match opts.open(path.as_ref()) {
                        Ok(x) => x,
                        Err(e) => {
                            key.complete(Err(format!("syscall open - file open error: {e:?}")));
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
                            key.complete(Ok(Intermediate::from_json(json!("OK").into())));
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
                        Value::Native(x) => match &**x {
                            NativeValue::InputFile { handle } => match handle.borrow_mut().as_mut() {
                                Some(handle) => {
                                    let mut res = String::new();
                                    if let Err(e) = handle.read_line(&mut res) {
                                        key.complete(Err(format!("syscall readLine - read error: {e:?}")));
                                        return RequestStatus::Handled;
                                    }

                                    key.complete(Ok(Intermediate::from_json(json!(res).into())));
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
                    [file, content] => match (file, content.to_string()) {
                        (Value::Native(x), Ok(content)) => match &**x {
                            NativeValue::OutputFile { handle } => match handle.borrow_mut().as_mut() {
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
