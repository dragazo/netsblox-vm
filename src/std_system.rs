//! An customizable implementation of [`System`].
//! 
//! This submodule is only available with the [`std`](crate) feature flag.
//! 
//! The primary type of interest is [`StdSystem`], which implements [`System`].
//! [`StdSystem`] can be configured with [`CustomTypes`] and [`Config`],
//! which together allow for the definition of any external features (e.g., defining syscalls),
//! as well as overriding default behavior (e.g., rpc intercepting).

use std::prelude::v1::*;
use std::collections::BTreeMap;
use std::rc::Rc;
use std::fmt;

extern crate std as real_std;
use real_std::time::{Instant, SystemTime, UNIX_EPOCH};
use real_std::sync::{Arc, Mutex};
use real_std::sync::mpsc::{Sender, Receiver, channel};
use real_std::thread;

use rand::distributions::uniform::{SampleUniform, SampleRange};
use rand_chacha::ChaChaRng;
use rand::{Rng, SeedableRng};
use tokio_tungstenite::tungstenite::Message;
use futures::{StreamExt, SinkExt};
use uuid::Uuid;

use crate::runtime::*;
use crate::json::*;
use crate::gc::*;
use crate::*;

const MESSAGE_REPLY_TIMEOUT_MS: u32 = 1500;

/// A [`StdSystem`] key type used to await a reply message from an external source.
#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq)]
pub struct ExternReplyKey {
    request_id: String,
}
/// A [`StdSystem`] key type required for this client to send a reply message.
#[derive(Debug, Clone)]
pub struct InternReplyKey {
    src_id: String,
    request_id: String,
}

struct Context {
    base_url: String,
    client_id: String,

    project_name: String,
    project_id: String,
    role_name: String,
    role_id: String,
}
struct RpcRequest {
    service: String,
    rpc: String,
    args: Vec<(String, Json)>,
    key: RpcKey,
}
enum OutgoingMessage {
    Normal {
        msg_type: String,
        values: Vec<(String, Json)>,
        targets: Vec<String>,
    },
    Blocking {
        msg_type: String,
        values: Vec<(String, Json)>,
        targets: Vec<String>,
        reply_key: ExternReplyKey,
    },
    Reply {
        value: Json,
        reply_key: InternReplyKey,
    },
}
struct IncomingMessage {
    msg_type: String,
    values: Vec<(String, Json)>,
    reply_key: Option<InternReplyKey>,
}
struct ReplyEntry {
    timestamp: Instant,
    value: Option<Json>,
}

/// The status of a potentially-intercepted RPC.
/// 
/// See [`Config::intercept_rpc`] for details.
pub enum RpcIntercept<'gc, C: CustomTypes> {
    /// The RPC was intercepted and the value will be produced by the interceptor.
    Intercepted,
    /// The RPC was not intercepted, and the default implementation should be used.
    UseDefault { key: RpcKey, service: String, rpc: String, args: Vec<(String, Value<'gc, StdSystem<C>>)> },
}

enum AsyncResult<T> {
    Pending,
    Completed(T),
    Used,
}
#[derive(Educe)]
#[educe(Clone)]
struct AsyncResultHandle<T>(Arc<Mutex<AsyncResult<T>>>);
impl<T> AsyncResultHandle<T> {
    fn pending() -> Self {
        Self(Arc::new(Mutex::new(AsyncResult::Pending)))
    }
    fn complete(&self, result: T) {
        let mut handle = self.0.lock().unwrap();
        match &mut *handle {
            AsyncResult::Pending => *handle = AsyncResult::Completed(result),
            _ => panic!("AsyncResultHandle can only be completed once"),
        }
    }
    fn poll(&self) -> AsyncPoll<T> {
        let mut handle = self.0.lock().unwrap();
        match &mut *handle {
            AsyncResult::Pending => AsyncPoll::Pending,
            AsyncResult::Completed(_) => match std::mem::replace(&mut *handle, AsyncResult::Used) {
                AsyncResult::Completed(x) => AsyncPoll::Completed(x),
                _ => unreachable!(),
            }
            AsyncResult::Used => panic!("AsyncResultHandle can only be successfully polled once"),
        }
    }
}

/// A [`StdSystem`] key type for an async syscall request.
/// 
/// Internally, this manages a shared handle to value of type [`CustomTypes::Intermediate`],
/// which allows you to define a custom type for the result of a syscall.
/// Other helper methods must be defined in [`CustomTypes`] to convert between this type and
/// an instance of [`Value`] that the vm can handle.
pub struct SyscallKey<C: CustomTypes>(AsyncResultHandle<Result<C::Intermediate, String>>);
impl<C: CustomTypes> SyscallKey<C> {
    /// Completes the syscall with the given result.
    /// A value of [`Ok`] denotes a successful syscall, whose value will be returned to the system
    /// after conversion under [`CustomTypes::from_intermediate`].
    /// A value of [`Err`] denotes a failed syscall, which will be returned as an error to the requestor,
    /// subject to the caller's [`ErrorScheme`](crate::process::ErrorScheme) setting for syscalls.
    pub fn complete(self, result: Result<C::Intermediate, String>) { self.0.complete(result) }
    pub(crate) fn poll(&self) -> AsyncPoll<Result<C::Intermediate, String>> { self.0.poll() }
}

/// A [`StdSystem`] key type for an async RPC request.
/// 
/// Internally, this manages a shared handle to a value of type [`Json`].
/// Although RPCs can be intercepted to run on local hardware (e.g., via [`Config::intercept_rpc`]),
/// the return value behavior of said RPCs should be indistinguishable, hence why this uses a standard [`Json`]
/// result rather than a customizable type like [`SyscallKey`].
pub struct RpcKey(AsyncResultHandle<Result<Json, String>>);
impl RpcKey {
    /// Completes the RPC call with the given result.
    /// A value of [`Ok`] denotes a successful RPC request, whose value is returned to the system.
    /// A value of [`Err`] denotes a failed syscall, which will be returned as an error to the requestor,
    /// subject to the caller's [`ErrorScheme`](crate::process::ErrorScheme) setting for RPCs.
    pub fn complete(self, result: Result<Json, String>) { self.0.complete(result) }
    pub(crate) fn poll(&self) -> AsyncPoll<Result<Json, String>> { self.0.poll() }
}

/// A [`StdSystem`] key type for an async input request.
/// 
/// Internally, this manages a shared handle to a value of type [`String`],
/// which is intended to be eventually provided with input from the user.
pub struct InputKey(AsyncResultHandle<String>);
impl InputKey {
    /// Completes the input request with the given input from the user, which is then returned to the caller.
    pub fn complete(self, result: String) { self.0.complete(result) }
    pub(crate) fn poll(&self) -> AsyncPoll<String> { self.0.poll() }
}

type MessageReplies = BTreeMap<ExternReplyKey, ReplyEntry>;

/// A collection of static settings for using custom native types.
pub trait CustomTypes: 'static + Sized {
    /// A native type that can be exposed directly to the VM as a value of type [`Value::Native`].
    /// For type checking, this is required to implement [`GetType`], which can use a custom type enum.
    type NativeValue: 'static + GetType + fmt::Debug;
    /// An intermediate type used to produce a [`Value`] for the [`StdSystem`] under async context.
    /// The reason this is needed is that [`Value`] can only be used during the lifetime of an associated [`MutationContext`] handle,
    /// which cannot be extended into the larger lifetime required for async operations.
    /// 
    /// Conversions are automatically performed between this type and [`Value`] via [`CustomTypes::from_intermediate`] and [`CustomTypes::to_intermediate`].
    type Intermediate: 'static;

    /// Converts a [`Value`] into a [`CustomTypes::Intermediate`] for use outside of gc context.
    fn from_intermediate<'gc>(mc: MutationContext<'gc, '_>, value: Self::Intermediate) -> Result<Value<'gc, StdSystem<Self>>, ErrorCause<StdSystem<Self>>>;
    /// Converts a [`CustomTypes::Intermediate`] into a [`Value`] for use inside the vm's gc context.
    fn to_intermediate<'gc>(value: Value<'gc, StdSystem<Self>>) -> Result<Self::Intermediate, ErrorCause<StdSystem<Self>>>;
}

/// A collection of implementation options for [`StdSystem`].
#[derive(Educe)]
#[educe(Default, Clone)]
pub struct Config<C: CustomTypes> {
    /// A function used to process all "say" and "think" blocks.
    /// Inputs include the actual message value, or [`None`] to clear the output (Snap!-style), and a reference to the entity making the request.
    /// If not specified, the system will simply ignore all output requests.
    pub print: Option<Rc<dyn for<'gc> Fn(&StdSystem<C>, MutationContext<'gc, '_>, Option<Value<'gc, StdSystem<C>>>, &Entity<'gc, StdSystem<C>>) -> Result<(), ErrorCause<StdSystem<C>>>>>,

    /// A function used to request input from the user.
    /// This should be non-blocking, and the result should eventually be forwarded to [`InputKey::complete`].
    /// If not specified (default), the system gives an error when processes attempt to request user input.
    pub input: Option<Rc<dyn for<'gc> Fn(&StdSystem<C>, MutationContext<'gc, '_>, InputKey, Option<Value<'gc, StdSystem<C>>>, &Entity<'gc, StdSystem<C>>) -> Result<(), ErrorCause<StdSystem<C>>>>>,

    /// A function used to perform system calls on the local hardware.
    /// This should not block (for an extended period of time), and the result should eventually be forwarded to [`SyscallKey::complete`].
    /// If not specified (default), the system gives an error when processes attempt to perform a syscall.
    ///
    /// This function is permitted to return an error during its synchronous initialization;
    /// however, this is intended for hard errors such as trying to invoke non-existent system calls.
    /// Normal syscall failures should instead yield an [`Err`] value to [`SyscallKey::complete`],
    /// which lets the runtime treat it similar to an RPC error that user code can handle properly.
    pub syscall: Option<Rc<dyn for<'gc> Fn(&StdSystem<C>, MutationContext<'gc, '_>, SyscallKey<C>, String, Vec<Value<'gc, StdSystem<C>>>) -> Result<(), ErrorCause<StdSystem<C>>>>>,

    /// A function used to intercept NetsBlox RPCs and redirect them for other purposes.
    /// For instance, the RoboScape service could be intercepted and the commands used to drive physical hardware directly.
    /// A result of type [`RpcIntercept::Intercepted`] denotes that the RPC was properly intercepted (and you are responsible for providing the result to [`RpcKey::complete`]).
    /// A result of type [`RpcIntercept::UseDefault`] denotes that the RPC was not intercepted.
    /// Note that even in the default case, the values returned can be modified, e.g., to facilitate passing platform specific types
    /// that would otherwise not be able to serialize under normal [`Value`] semantics.
    pub intercept_rpc: Option<Rc<dyn for<'gc> Fn(&StdSystem<C>, MutationContext<'gc, '_>, RpcKey, String, String, Vec<(String, Value<'gc, StdSystem<C>>)>) -> Result<RpcIntercept<'gc, C>, ErrorCause<StdSystem<C>>>>>,
}
impl<C: CustomTypes> Config<C> {
    /// Combines this config object with another.
    /// Equivalent to calling [`Option::or`] on every field.
    pub fn or(self, other: Self) -> Self {
        Self {
            print: self.print.or(other.print),
            input: self.input.or(other.input),
            syscall: self.syscall.or(other.syscall),
            intercept_rpc: self.intercept_rpc.or(other.intercept_rpc),
        }
    }
}

async fn call_rpc_async(context: &Context, client: &reqwest::Client, service: &str, rpc: &str, args: &[(&str, &Json)]) -> Result<Json, String> {
    let time = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_millis();
    let url = format!("{base_url}/services/{service}/{rpc}?uuid={client_id}&projectId={project_id}&roleId={role_id}&t={time}",
        base_url = context.base_url, client_id = context.client_id, project_id = context.project_id, role_id = context.role_id);
    let args: BTreeMap<&str, &Json> = args.iter().copied().collect();

    match client.post(url).json(&args).send().await {
        Ok(res) => {
            let status = res.status();
            match res.text().await {
                Ok(text) => match status.is_success() {
                    true => Ok(serde_json::from_str(&text).unwrap_or(Json::String(text))),
                    false => Err(text),
                }
                Err(_) => Err("Failed to read response body".to_owned()),
            }
        }
        Err(_) => Err(format!("Failed to reach {}", context.base_url)),
    }
}

/// A type implementing the [`System`] trait which supports all features.
pub struct StdSystem<C: CustomTypes> {
    config: Config<C>,
    context: Arc<Context>,
    client: Arc<reqwest::Client>,
    start_time: Instant,
    rng: Mutex<ChaChaRng>,

    rpc_request_pipe: Sender<RpcRequest>,

    message_replies: Arc<Mutex<MessageReplies>>,
    message_sender: Sender<OutgoingMessage>,
    message_receiver: Receiver<IncomingMessage>,
}
impl<C: CustomTypes> StdSystem<C> {
    /// Initializes a new instance of [`StdSystem`] targeting the given NetsBlox server base url (e.g., `https://editor.netsblox.org`).
    #[tokio::main(flavor = "current_thread")]
    pub async fn new(base_url: String, project_name: Option<&str>, config: Config<C>) -> Self {
        let mut context = Context {
            base_url,
            client_id: format!("vm-{}", names::Generator::default().next().unwrap()),
            project_name: project_name.unwrap_or("untitled").to_owned(),

            project_id: String::new(),
            role_name: String::new(),
            role_id: String::new(),
        };

        let message_replies = Arc::new(Mutex::new(Default::default()));
        let (message_sender, message_receiver) = {
            let (base_url, client_id, project_name, message_replies) = (context.base_url.clone(), context.client_id.clone(), context.project_name.clone(), message_replies.clone());
            let (out_sender, out_receiver) = channel();
            let (in_sender, in_receiver) = channel();

            #[tokio::main(flavor = "multi_thread", worker_threads = 1)]
            async fn handler(base_url: String, client_id: String, project_name: String, message_replies: Arc<Mutex<MessageReplies>>, out_receiver: Receiver<OutgoingMessage>, in_sender: Sender<IncomingMessage>) {
                let ws_url = if let Some(x) = base_url.strip_prefix("http") { format!("ws{}", x) } else { format!("wss://{}", base_url) };
                let (ws, _) = tokio_tungstenite::connect_async(ws_url).await.unwrap();
                let (mut ws_sender, ws_receiver) = ws.split();
                let (ws_sender_sender, ws_sender_receiver) = async_channel::unbounded();

                tokio::spawn(async move {
                    while let Ok(msg) = ws_sender_receiver.recv().await {
                        ws_sender.send(msg).await.unwrap();
                    }
                });

                let ws_sender_sender_clone = ws_sender_sender.clone();
                tokio::spawn(async move {
                    ws_receiver.for_each(move |packet| {
                        let ws_sender_sender_clone = ws_sender_sender_clone.clone();
                        let in_sender = in_sender.clone();
                        let message_replies = message_replies.clone();
                        async move {
                            let mut msg = match packet {
                                Ok(Message::Text(raw)) => match serde_json::from_str::<BTreeMap<String, Json>>(&raw) {
                                    Ok(x) => x,
                                    Err(_) => return,
                                }
                                _ => return,
                            };
                            match msg.get("type").and_then(|x| x.as_str()).unwrap_or("unknown") {
                                "ping" => ws_sender_sender_clone.send(Message::Text(json!({ "type": "pong" }).to_string())).await.unwrap(),
                                "message" => {
                                    let (msg_type, values) = match (msg.remove("msgType"), msg.remove("content")) {
                                        (Some(Json::String(msg_type)), Some(Json::Object(values))) => (msg_type, values),
                                        _ => return,
                                    };
                                    if msg_type == "__reply__" {
                                        let (value, reply_key) = match ({ values }.remove("body"), msg.remove("requestId")) {
                                            (Some(value), Some(Json::String(request_id))) => (value, ExternReplyKey { request_id }),
                                            _ => return,
                                        };
                                        if let Some(entry) = message_replies.lock().unwrap().get_mut(&reply_key) {
                                            if entry.value.is_none() {
                                                entry.value = Some(value);
                                            }
                                        }
                                    } else {
                                        let reply_key = match msg.contains_key("requestId") {
                                            true => match (msg.remove("srcId"), msg.remove("requestId")) {
                                                (Some(Json::String(src_id)), Some(Json::String(request_id))) => Some(InternReplyKey { src_id, request_id }),
                                                _ => return,
                                            }
                                            false => None,
                                        };
                                        in_sender.send(IncomingMessage { msg_type, values: values.into_iter().collect(), reply_key }).unwrap();
                                    }
                                }
                                _ => (),
                            }
                        }
                    }).await;
                });

                ws_sender_sender.send(Message::Text(json!({ "type": "set-uuid", "clientId": client_id }).to_string())).await.unwrap();

                while let Ok(request) = out_receiver.recv() {
                    let msg = match request {
                        OutgoingMessage::Normal { msg_type, values, targets } => json!({
                            "type": "message",
                            "dstId": targets,
                            "srcId": format!("{}@{}", project_name, client_id),
                            "msgType": msg_type,
                            "content": values.into_iter().collect::<serde_json::Map<_,_>>(),
                        }),
                        OutgoingMessage::Blocking { msg_type, values, targets, reply_key } => json!({
                            "type": "message",
                            "dstId": targets,
                            "srcId": format!("{}@{}", project_name, client_id),
                            "msgType": msg_type,
                            "requestId": reply_key.request_id,
                            "content": values.into_iter().collect::<serde_json::Map<_,_>>(),
                        }),
                        OutgoingMessage::Reply { value, reply_key } => json!({
                            "type": "message",
                            "dstId": reply_key.src_id,
                            "msgType": "__reply__",
                            "requestId": reply_key.request_id,
                            "content": { "body": value },
                        }),
                    };
                    ws_sender_sender.send(Message::Text(msg.to_string())).await.unwrap();
                }
            }
            thread::spawn(move || handler(base_url, client_id, project_name, message_replies, out_receiver, in_sender));

            (out_sender, in_receiver)
        };

        let client = Arc::new(reqwest::Client::builder().build().unwrap());
        let meta = client.post(format!("{}/api/newProject", context.base_url))
            .json(&json!({ "clientId": context.client_id, "roleName": "monad" }))
            .send().await.unwrap()
            .json::<BTreeMap<String, Json>>().await.unwrap();
        context.project_id = meta["projectId"].as_str().unwrap().to_owned();
        context.role_id = meta["roleId"].as_str().unwrap().to_owned();
        context.role_name = meta["roleName"].as_str().unwrap().to_owned();

        let meta = client.post(format!("{}/api/setProjectName", context.base_url))
            .json(&json!({ "projectId": context.project_id, "name": context.project_name }))
            .send().await.unwrap()
            .json::<BTreeMap<String, Json>>().await.unwrap();
        context.project_name = meta["name"].as_str().unwrap().to_owned();

        let context = Arc::new(context);
        let rpc_request_pipe = {
            let (client, context) = (client.clone(), context.clone());
            let (sender, receiver) = channel();

            #[tokio::main(flavor = "multi_thread", worker_threads = 1)]
            async fn handler(client: Arc<reqwest::Client>, context: Arc<Context>, receiver: Receiver<RpcRequest>) {
                while let Ok(request) = receiver.recv() {
                    let (client, context) = (client.clone(), context.clone());
                    tokio::spawn(async move {
                        let res = call_rpc_async(&context, &client, &request.service, &request.rpc, &request.args.iter().map(|x| (x.0.as_str(), &x.1)).collect::<Vec<_>>()).await;
                        request.key.complete(res);
                    });
                }
            }
            thread::spawn(move || handler(client, context, receiver));

            sender
        };

        let mut seed: <ChaChaRng as SeedableRng>::Seed = Default::default();
        getrandom::getrandom(&mut seed).expect("failed to generate random seed");

        Self {
            config, context, client,
            start_time: Instant::now(),
            rng: Mutex::new(ChaChaRng::from_seed(seed)),
            rpc_request_pipe,
            message_replies, message_sender, message_receiver,
        }
    }

    /// Asynchronously calls an RPC and returns the result.
    /// This function directly makes requests to NetsBlox, bypassing any RPC hook defined by [`Config`].
    pub async fn call_rpc_async(&self, service: &str, rpc: &str, args: &[(&str, &Json)]) -> Result<Json, String> {
        call_rpc_async(&self.context, &self.client, service, rpc, args).await
    }

    /// Gets the public id of the running system that can be used to send messages to this client.
    pub fn get_public_id(&self) -> String {
        format!("{}@{}", self.context.project_name, self.context.client_id)
    }
}
impl<C: CustomTypes> System for StdSystem<C> {
    type SyscallKey = SyscallKey<C>;
    type RpcKey = RpcKey;
    type InputKey = InputKey;
    type ExternReplyKey = ExternReplyKey;
    type InternReplyKey = InternReplyKey;
    type NativeValue = C::NativeValue;

    fn rand<T, R>(&self, range: R) -> Result<T, ErrorCause<StdSystem<C>>> where T: SampleUniform, R: SampleRange<T> {
        Ok(self.rng.lock().unwrap().gen_range(range))
    }

    fn time_ms(&self) -> Result<u64, ErrorCause<StdSystem<C>>> {
        Ok(self.start_time.elapsed().as_millis() as u64)
    }

    fn print<'gc>(&self, mc: MutationContext<'gc, '_>, value: Option<Value<'gc, Self>>, entity: &Entity<'gc, Self>) -> Result<(), ErrorCause<Self>> {
        match self.config.print.as_ref() {
            Some(print) => print(self, mc, value, entity),
            None => Err(SystemError::NotSupported { feature: SystemFeature::Print }.into()),
        }
    }

    fn syscall<'gc>(&self, mc: MutationContext<'gc, '_>, name: String, args: Vec<Value<'gc, Self>>) -> Result<MaybeAsync<Result<Value<'gc, Self>, String>, Self::SyscallKey>, ErrorCause<StdSystem<C>>> {
        match self.config.syscall.as_ref() {
            Some(syscall) => {
                let key = SyscallKey(AsyncResultHandle::pending());
                syscall(self, mc, SyscallKey(key.0.clone()), name, args)?;
                Ok(MaybeAsync::Async(key))
            }
            None => Err(SystemError::NotSupported { feature: SystemFeature::Syscall { name } }.into()),
        }
    }
    fn poll_syscall<'gc>(&self, mc: MutationContext<'gc, '_>, key: &Self::SyscallKey) -> Result<AsyncPoll<Result<Value<'gc, Self>, String>>, ErrorCause<StdSystem<C>>> {
        Ok(match key.poll() {
            AsyncPoll::Completed(x) => match x {
                Ok(x) => AsyncPoll::Completed(Ok(C::from_intermediate(mc, x)?)),
                Err(x) => AsyncPoll::Completed(Err(x)),
            }
            AsyncPoll::Pending => AsyncPoll::Pending,
        })
    }

    fn call_rpc<'gc>(&self, mc: MutationContext<'gc, '_>, service: String, rpc: String, args: Vec<(String, Value<'gc, Self>)>) -> Result<MaybeAsync<Result<Value<'gc, Self>, String>, Self::RpcKey>, ErrorCause<StdSystem<C>>> {
        let key = RpcKey(AsyncResultHandle::pending());
        let res = match self.config.intercept_rpc.as_ref() {
            Some(intercept_rpc) => intercept_rpc(self, mc, RpcKey(key.0.clone()), service, rpc, args)?,
            None => RpcIntercept::UseDefault { key: RpcKey(key.0.clone()), service, rpc, args },
        };
        match res {
            RpcIntercept::Intercepted => (),
            RpcIntercept::UseDefault { key, service, rpc, args } => {
                let args = args.into_iter().map(|(k, v)| Ok::<(String, Json), ToJsonError<StdSystem<C>>>((k, v.to_json()?))).collect::<Result<_,_>>()?;
                self.rpc_request_pipe.send(RpcRequest { service, rpc, args, key }).unwrap();
            }
        }
        Ok(MaybeAsync::Async(key))
    }
    fn poll_rpc<'gc>(&self, mc: MutationContext<'gc, '_>, key: &Self::RpcKey) -> Result<AsyncPoll<Result<Value<'gc, Self>, String>>, ErrorCause<Self>> {
        Ok(match key.poll() {
            AsyncPoll::Completed(x) => match x {
                Ok(x) => AsyncPoll::Completed(Ok(Value::from_json(mc, x)?)),
                Err(x) => AsyncPoll::Completed(Err(x)),
            }
            AsyncPoll::Pending => AsyncPoll::Pending,
        })
    }

    fn input<'gc>(&self, mc: MutationContext<'gc, '_>, prompt: Option<Value<'gc, Self>>, entity: &Entity<'gc, Self>) -> Result<MaybeAsync<String, Self::InputKey>, ErrorCause<StdSystem<C>>> {
        match self.config.input.as_ref() {
            Some(input) => {
                let key = InputKey(AsyncResultHandle::pending());
                input(self, mc, InputKey(key.0.clone()), prompt, entity)?;
                Ok(MaybeAsync::Async(key))
            }
            None => Err(SystemError::NotSupported { feature: SystemFeature::Input }.into()),
        }
    }
    fn poll_input<'gc>(&self, _: MutationContext<'gc, '_>, key: &Self::InputKey) -> Result<AsyncPoll<String>, ErrorCause<Self>> {
        Ok(key.poll())
    }

    fn send_message(&self, msg_type: String, values: Vec<(String, Json)>, targets: Vec<String>, expect_reply: bool) -> Result<Option<Self::ExternReplyKey>, ErrorCause<StdSystem<C>>> {
        let (msg, reply_key) = match expect_reply {
            false => (OutgoingMessage::Normal { msg_type, values, targets }, None),
            true => {
                let reply_key = ExternReplyKey { request_id: Uuid::new_v4().to_string() };
                self.message_replies.lock().unwrap().insert(reply_key.clone(), ReplyEntry { timestamp: Instant::now(), value: None });
                (OutgoingMessage::Blocking { msg_type, values, targets, reply_key: reply_key.clone() }, Some(reply_key))
            }
        };
        self.message_sender.send(msg).unwrap();
        Ok(reply_key)
    }
    fn poll_reply(&self, key: &Self::ExternReplyKey) -> AsyncPoll<Option<Json>> {
        let mut message_replies = self.message_replies.lock().unwrap();
        let entry = message_replies.get(key).unwrap();
        if entry.value.is_some() {
            return AsyncPoll::Completed(message_replies.remove(key).unwrap().value);
        }
        if entry.timestamp.elapsed().as_millis() as u32 >= MESSAGE_REPLY_TIMEOUT_MS {
            message_replies.remove(key).unwrap();
            return AsyncPoll::Completed(None);
        }
        AsyncPoll::Pending
    }
    fn send_reply(&self, key: Self::InternReplyKey, value: Json) -> Result<(), ErrorCause<Self>> {
        self.message_sender.send(OutgoingMessage::Reply { value, reply_key: key }).unwrap();
        Ok(())
    }
    fn receive_message(&self) -> Option<(String, Vec<(String, Json)>, Option<Self::InternReplyKey>)> {
        self.message_receiver.try_recv().ok().map(|x| (x.msg_type, x.values, x.reply_key))
    }
}