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
struct RpcRequest<C: CustomTypes> {
    service: String,
    rpc: String,
    args: Vec<(String, Json)>,
    key: RequestKey<C>,
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

/// The status of a potentially-handled request.
pub enum RequestStatus<'gc, C: CustomTypes> {
    /// The request was handled by the overriding client.
    Handled,
    /// The request was not handled by the overriding client,
    /// and the default system implementation should be used instead.
    UseDefault { key: RequestKey<C>, request: Request<'gc, StdSystem<C>> },
}
/// The status of a potentially-handled command.
pub enum CommandStatus<'gc, C: CustomTypes> {
    /// The command was handled by the overriding client.
    Handled,
    /// The command was not handled by the overriding client,
    /// and the default system implementation should be used instead.
    UseDefault { key: CommandKey, command: Command<'gc, StdSystem<C>> },
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

/// A [`StdSystem`] key type for an asynchronous request.
pub struct RequestKey<C: CustomTypes>(AsyncResultHandle<Result<C::Intermediate, String>>);
impl<C: CustomTypes> RequestKey<C> {
    /// Completes the request with the given result.
    /// A value of [`Ok`] denotes a successful request, whose value will be returned to the system
    /// after conversion under [`CustomTypes::from_intermediate`].
    /// A value of [`Err`] denotes a failed request, which will be returned as an error to the runtime,
    /// subject to the caller's [`ErrorScheme`](crate::process::ErrorScheme) setting.
    pub fn complete(self, result: Result<C::Intermediate, String>) { self.0.complete(result) }
    pub(crate) fn poll(&self) -> AsyncPoll<Result<C::Intermediate, String>> { self.0.poll() }
}

/// A [`StdSystem`] key type for an asynchronous command.
pub struct CommandKey(AsyncResultHandle<Result<(), String>>);
impl CommandKey {
    /// Completes the command.
    /// A value of [`Ok`] denotes a successful command.
    /// A value of [`Err`] denotes a failed command, which will be returned as an error to the runtime,
    /// subject to the caller's [`ErrorScheme`](crate::process::ErrorScheme) setting.
    pub fn complete(self, result: Result<(), String>) { self.0.complete(result) }
    pub(crate) fn poll(&self) -> AsyncPoll<Result<(), String>> { self.0.poll() }
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
    type Intermediate: 'static + Send + From<Json>;

    /// Converts a [`Value`] into a [`CustomTypes::Intermediate`] for use outside of gc context.
    fn from_intermediate<'gc>(mc: MutationContext<'gc, '_>, value: Self::Intermediate) -> Result<Value<'gc, StdSystem<Self>>, ErrorCause<StdSystem<Self>>>;
    /// Converts a [`CustomTypes::Intermediate`] into a [`Value`] for use inside the runtime's gc context.
    fn to_intermediate<'gc>(value: Value<'gc, StdSystem<Self>>) -> Result<Self::Intermediate, ErrorCause<StdSystem<Self>>>;
}

/// A collection of implementation options for [`StdSystem`].
#[derive(Educe)]
#[educe(Default, Clone)]
pub struct Config<C: CustomTypes> {
    /// A function used to perform asynchronous requests that yield a value back to the runtime.
    pub request: Option<Rc<dyn for<'gc> Fn(&StdSystem<C>, MutationContext<'gc, '_>, RequestKey<C>, Request<'gc, StdSystem<C>>, &Entity<'gc, StdSystem<C>>) -> Result<RequestStatus<'gc, C>, ErrorCause<StdSystem<C>>>>>,
    /// A function used to perform asynchronous tasks whose completion is awaited by the runtime.
    pub command: Option<Rc<dyn for<'gc> Fn(&StdSystem<C>, MutationContext<'gc, '_>, CommandKey, Command<'gc, StdSystem<C>>, &Entity<'gc, StdSystem<C>>) -> Result<CommandStatus<'gc, C>, ErrorCause<StdSystem<C>>>>>,
}
impl<C: CustomTypes> Config<C> {
    /// Composes two [`Config`] objects, prioritizing the implementation of `self`.
    pub fn fallback(&self, other: &Self) -> Self {
        Self {
            request: match (self.request.clone(), other.request.clone()) {
                (Some(a), Some(b)) => Some(Rc::new(move |system, mc, key, request, entity| {
                    match a(system, mc, key, request, entity)? {
                        RequestStatus::Handled => Ok(RequestStatus::Handled),
                        RequestStatus::UseDefault { key, request } => b(system, mc, key, request, entity),
                    }
                })),
                (Some(a), None) | (None, Some(a)) => Some(a),
                (None, None) => None,
            },
            command: match (self.command.clone(), other.command.clone()) {
                (Some(a), Some(b)) => Some(Rc::new(move |system, mc, key, command, entity| {
                    match a(system, mc, key, command, entity)? {
                        CommandStatus::Handled => Ok(CommandStatus::Handled),
                        CommandStatus::UseDefault { key, command } => b(system, mc, key, command, entity),
                    }
                })),
                (Some(a), None) | (None, Some(a)) => Some(a),
                (None, None) => None,
            },
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

    rpc_request_pipe: Sender<RpcRequest<C>>,

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
            async fn handler<C: CustomTypes>(client: Arc<reqwest::Client>, context: Arc<Context>, receiver: Receiver<RpcRequest<C>>) {
                while let Ok(request) = receiver.recv() {
                    let (client, context) = (client.clone(), context.clone());
                    tokio::spawn(async move {
                        let res = call_rpc_async(&context, &client, &request.service, &request.rpc, &request.args.iter().map(|x| (x.0.as_str(), &x.1)).collect::<Vec<_>>()).await;
                        request.key.complete(res.map(Into::into));
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
    type NativeValue = C::NativeValue;

    type RequestKey = RequestKey<C>;
    type CommandKey = CommandKey;

    type ExternReplyKey = ExternReplyKey;
    type InternReplyKey = InternReplyKey;

    fn rand<T, R>(&self, range: R) -> Result<T, ErrorCause<StdSystem<C>>> where T: SampleUniform, R: SampleRange<T> {
        Ok(self.rng.lock().unwrap().gen_range(range))
    }

    fn time_ms(&self) -> Result<u64, ErrorCause<StdSystem<C>>> {
        Ok(self.start_time.elapsed().as_millis() as u64)
    }

    fn perform_request<'gc>(&self, mc: MutationContext<'gc, '_>, request: Request<'gc, Self>, entity: &Entity<'gc, Self>) -> Result<MaybeAsync<Result<Value<'gc, Self>, String>, Self::RequestKey>, ErrorCause<Self>> {
        let key = RequestKey(AsyncResultHandle::pending());
        let use_default = match self.config.request.as_ref() {
            Some(handler) => {
                match handler(self, mc, RequestKey(key.0.clone()), request, entity)? {
                    RequestStatus::Handled => None,
                    RequestStatus::UseDefault { key, request } => Some((key, request)),
                }
            }
            None => Some((RequestKey(key.0.clone()), request)),
        };
        if let Some((key, request)) = use_default {
            match request {
                Request::Rpc { service, rpc, args } => {
                    let args = args.into_iter().map(|(k, v)| Ok((k, v.to_json()?))).collect::<Result<_,ToJsonError<_>>>()?;
                    self.rpc_request_pipe.send(RpcRequest { service, rpc, args, key }).unwrap();
                }
                _ => return Err(ErrorCause::NotSupported { feature: request.feature() }.into()),
            }
        }
        Ok(MaybeAsync::Async(key))
    }
    fn poll_request<'gc>(&self, mc: MutationContext<'gc, '_>, key: &Self::RequestKey, _: &Entity<'gc, Self>) -> Result<AsyncPoll<Result<Value<'gc, Self>, String>>, ErrorCause<Self>> {
        Ok(match key.poll() {
            AsyncPoll::Completed(x) => match x {
                Ok(x) => AsyncPoll::Completed(Ok(C::from_intermediate(mc, x)?)),
                Err(x) => AsyncPoll::Completed(Err(x)),
            }
            AsyncPoll::Pending => AsyncPoll::Pending,
        })
    }

    fn perform_command<'gc>(&self, mc: MutationContext<'gc, '_>, command: Command<'gc, Self>, entity: &Entity<'gc, Self>) -> Result<MaybeAsync<Result<(), String>, Self::CommandKey>, ErrorCause<Self>> {
        match self.config.command.as_ref() {
            Some(handler) => {
                let key = CommandKey(AsyncResultHandle::pending());
                match handler(self, mc, CommandKey(key.0.clone()), command, entity)? {
                    CommandStatus::Handled => (),
                    CommandStatus::UseDefault { key: _, command } => return Err(ErrorCause::NotSupported { feature: command.feature() }.into()),
                }
                Ok(MaybeAsync::Async(key))
            }
            None => Err(ErrorCause::NotSupported { feature: command.feature() }.into()),
        }
    }
    fn poll_command<'gc>(&self, _: MutationContext<'gc, '_>, key: &Self::CommandKey, _: &Entity<'gc, Self>) -> Result<AsyncPoll<Result<(), String>>, ErrorCause<Self>> {
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