//! An customizable implementation of [`System`].
//! 
//! This submodule is only available with the [`std`](crate) feature flag.
//! 
//! The primary type of interest is [`StdSystem`], which implements [`System`].
//! [`StdSystem`] can be configured with [`CustomTypes`] and [`Config`],
//! which together allow for the definition of any external features (e.g., defining syscalls),
//! as well as overriding default behavior (e.g., rpc intercepting).

use alloc::string::{String, ToString};
use alloc::collections::BTreeMap;
use alloc::borrow::ToOwned;
use alloc::vec::Vec;
use alloc::rc::Rc;

use std::time::{Instant, SystemTime, UNIX_EPOCH};
use std::sync::{Arc, Mutex};
use std::sync::mpsc::{Sender, Receiver, channel};
use std::thread;

use rand::distributions::uniform::{SampleUniform, SampleRange};
use rand_chacha::ChaChaRng;
use rand::{Rng, SeedableRng};
use tokio_tungstenite::tungstenite::Message;
use futures::{StreamExt, SinkExt};
use uuid::Uuid;

use crate::real_time::*;
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
struct RpcRequest<C: CustomTypes<StdSystem<C>>> {
    service: String,
    rpc: String,
    args: Vec<(String, Json)>,
    key: RequestKey<C>,
}
struct ReplyEntry {
    timestamp: Instant,
    value: Option<Json>,
}

/// A [`StdSystem`] key type for an asynchronous request.
pub struct RequestKey<C: CustomTypes<StdSystem<C>>>(Arc<Mutex<AsyncResult<Result<C::Intermediate, String>>>>);
impl<C: CustomTypes<StdSystem<C>>> RequestKey<C> {
    pub(crate) fn poll(&self) -> AsyncResult<Result<C::Intermediate, String>> { self.0.lock().unwrap().poll() }
}
impl<C: CustomTypes<StdSystem<C>>> Key<Result<C::Intermediate, String>> for RequestKey<C> {
    /// Completes the request with the given result.
    /// A value of [`Ok`] denotes a successful request, whose value will be returned to the system
    /// after conversion under [`CustomTypes::from_intermediate`].
    /// A value of [`Err`] denotes a failed request, which will be returned as an error to the runtime,
    /// subject to the caller's [`ErrorScheme`](crate::runtime::ErrorScheme) setting.
    fn complete(self, value: Result<C::Intermediate, String>) {
        assert!(self.0.lock().unwrap().complete(value).is_ok())
    }
}

/// A [`StdSystem`] key type for an asynchronous command.
pub struct CommandKey(Arc<Mutex<AsyncResult<Result<(), String>>>>);
impl CommandKey {
    pub(crate) fn poll(&self) -> AsyncResult<Result<(), String>> { self.0.lock().unwrap().poll() }
}
impl Key<Result<(), String>> for CommandKey {
    /// Completes the command.
    /// A value of [`Ok`] denotes a successful command.
    /// A value of [`Err`] denotes a failed command, which will be returned as an error to the runtime,
    /// subject to the caller's [`ErrorScheme`](crate::runtime::ErrorScheme) setting.
    fn complete(self, value: Result<(), String>) {
        assert!(self.0.lock().unwrap().complete(value).is_ok())
    }
}

type MessageReplies = BTreeMap<ExternReplyKey, ReplyEntry>;

async fn call_rpc_async<C: CustomTypes<StdSystem<C>>>(context: &Context, client: &reqwest::Client, service: &str, rpc: &str, args: &[(&str, &Json)]) -> Result<C::Intermediate, String> {
    let time = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_millis();
    let url = format!("{base_url}/services/{service}/{rpc}?uuid={client_id}&projectId={project_id}&roleId={role_id}&t={time}",
        base_url = context.base_url, client_id = context.client_id, project_id = context.project_id, role_id = context.role_id);
    let args: BTreeMap<&str, &Json> = args.iter().copied().collect();

    let res = match client.post(url).json(&args).send().await {
        Ok(x) => x,
        Err(_) => return Err(format!("Failed to reach {}", context.base_url)),
    };

    let content_type = res.headers().get("Content-Type").and_then(|x| String::from_utf8(x.as_bytes().to_owned()).ok()).map(|x| x.to_lowercase()).unwrap_or_else(|| "unknown".into());
    let status = res.status();

    let res = match res.bytes().await {
        Ok(res) => (&*res).to_owned(),
        Err(_) => return Err("Failed to read response body".to_owned()),
    };

    if !status.is_success() {
        return Err(String::from_utf8(res).ok().unwrap_or_else(|| "Received ill-formed error message".into()));
    }

    if content_type.contains("image/") {
        Ok(C::Intermediate::from_image(res))
    } else if content_type.contains("audio/") {
        Ok(C::Intermediate::from_audio(res))
    } else if let Ok(x) = parse_json_slice::<Json>(&res) {
        Ok(C::Intermediate::from_json(x))
    } else if let Ok(x) = String::from_utf8(res) {
        Ok(C::Intermediate::from_json(Json::String(x)))
    } else {
        Err("Received ill-formed success value".into())
    }
}

/// A type implementing the [`System`] trait which supports all features.
pub struct StdSystem<C: CustomTypes<StdSystem<C>>> {
    config: Config<C, Self>,
    context: Arc<Context>,
    client: Arc<reqwest::Client>,
    rng: Mutex<ChaChaRng>,
    utc_offset: UtcOffset,

    rpc_request_pipe: Sender<RpcRequest<C>>,

    message_replies: Arc<Mutex<MessageReplies>>,
    message_sender: Sender<OutgoingMessage<C, Self>>,
    message_injector: Sender<IncomingMessage<C, Self>>,
    message_receiver: Receiver<IncomingMessage<C, Self>>,
}
impl<C: CustomTypes<StdSystem<C>>> StdSystem<C> {
    /// Initializes a new instance of [`StdSystem`] targeting the given NetsBlox server base url (e.g., `https://editor.netsblox.org`).
    #[tokio::main(flavor = "current_thread")]
    pub async fn new(base_url: String, project_name: Option<&str>, config: Config<C, Self>, utc_offset: UtcOffset) -> Self {
        let mut context = Context {
            base_url,
            client_id: format!("vm-{}", names::Generator::default().next().unwrap()),
            project_name: project_name.unwrap_or("untitled").to_owned(),

            project_id: String::new(),
            role_name: String::new(),
            role_id: String::new(),
        };

        let message_replies = Arc::new(Mutex::new(Default::default()));
        let (message_sender, message_receiver, message_injector) = {
            let (base_url, client_id, project_name, message_replies) = (context.base_url.clone(), context.client_id.clone(), context.project_name.clone(), message_replies.clone());
            let (out_sender, out_receiver) = channel();
            let (in_sender, in_receiver) = channel();

            #[tokio::main(flavor = "multi_thread", worker_threads = 1)]
            async fn handler<C: CustomTypes<StdSystem<C>>>(base_url: String, client_id: String, project_name: String, message_replies: Arc<Mutex<MessageReplies>>, out_receiver: Receiver<OutgoingMessage<C, StdSystem<C>>>, in_sender: Sender<IncomingMessage<C, StdSystem<C>>>) {
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
                                Ok(Message::Text(raw)) => match parse_json::<BTreeMap<String, Json>>(&raw) {
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
                            "content": values.into_iter().collect::<JsonMap<_,_>>(),
                        }),
                        OutgoingMessage::Blocking { msg_type, values, targets, reply_key } => json!({
                            "type": "message",
                            "dstId": targets,
                            "srcId": format!("{}@{}", project_name, client_id),
                            "msgType": msg_type,
                            "requestId": reply_key.request_id,
                            "content": values.into_iter().collect::<JsonMap<_,_>>(),
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
            let in_sender_clone = in_sender.clone();
            thread::spawn(move || handler(base_url, client_id, project_name, message_replies, out_receiver, in_sender_clone));

            (out_sender, in_receiver, in_sender)
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
            async fn handler<C: CustomTypes<StdSystem<C>>>(client: Arc<reqwest::Client>, context: Arc<Context>, receiver: Receiver<RpcRequest<C>>) {
                while let Ok(request) = receiver.recv() {
                    let (client, context) = (client.clone(), context.clone());
                    tokio::spawn(async move {
                        let res = call_rpc_async::<C>(&context, &client, &request.service, &request.rpc, &request.args.iter().map(|x| (x.0.as_str(), &x.1)).collect::<Vec<_>>()).await;
                        request.key.complete(res);
                    });
                }
            }
            thread::spawn(move || handler(client, context, receiver));

            sender
        };

        let mut seed: <ChaChaRng as SeedableRng>::Seed = Default::default();
        getrandom::getrandom(&mut seed).expect("failed to generate random seed");

        let config = config.fallback(&Config {
            request: Some(Rc::new(|system, _, key, request, _| {
                match request {
                    Request::Rpc { service, rpc, args } => {
                        match args.into_iter().map(|(k, v)| Ok((k, v.to_json()?))).collect::<Result<_,ToJsonError<_,_>>>() {
                            Ok(args) => system.rpc_request_pipe.send(RpcRequest { service, rpc, args, key }).unwrap(),
                            Err(err) => key.complete(Err(format!("failed to convert RPC args to json: {err:?}"))),
                        }
                        RequestStatus::Handled
                    }
                    _ => RequestStatus::UseDefault { key, request },
                }
            })),
            command: None,
        });

        Self {
            config, context, client, utc_offset,
            rng: Mutex::new(ChaChaRng::from_seed(seed)),
            rpc_request_pipe,
            message_replies, message_sender, message_receiver, message_injector,
        }
    }

    /// Asynchronously calls an RPC and returns the result.
    /// This function directly makes requests to NetsBlox, bypassing any RPC hook defined by [`Config`].
    pub async fn call_rpc_async(&self, service: &str, rpc: &str, args: &[(&str, &Json)]) -> Result<C::Intermediate, String> {
        call_rpc_async::<C>(&self.context, &self.client, service, rpc, args).await
    }

    /// Gets the public id of the running system that can be used to send messages to this client.
    pub fn get_public_id(&self) -> String {
        format!("{}@{}", self.context.project_name, self.context.client_id)
    }

    /// Injects a message into the receiving queue as if received over the network.
    pub fn inject_message(&self, msg_type: String, values: Vec<(String, Json)>) {
        self.message_injector.send(IncomingMessage { msg_type, values, reply_key: None }).unwrap();
    }
}
impl<C: CustomTypes<StdSystem<C>>> System<C> for StdSystem<C> {
    type RequestKey = RequestKey<C>;
    type CommandKey = CommandKey;

    type ExternReplyKey = ExternReplyKey;
    type InternReplyKey = InternReplyKey;

    fn rand<T: SampleUniform, R: SampleRange<T>>(&self, range: R) -> T {
        self.rng.lock().unwrap().gen_range(range)
    }

    fn time(&self) -> SysTime {
        SysTime::Real { local: OffsetDateTime::now_utc().to_offset(self.utc_offset) }
    }

    fn perform_request<'gc>(&self, mc: &Mutation<'gc>, request: Request<'gc, C, Self>, entity: &mut Entity<'gc, C, Self>) -> Result<MaybeAsync<Result<Value<'gc, C, Self>, String>, Self::RequestKey>, ErrorCause<C, Self>> {
        Ok(match self.config.request.as_ref() {
            Some(handler) => {
                let key = RequestKey(Arc::new(Mutex::new(AsyncResult::new())));
                match handler(self, mc, RequestKey(key.0.clone()), request, entity) {
                    RequestStatus::Handled => MaybeAsync::Async(key),
                    RequestStatus::UseDefault { key: _, request } => return Err(ErrorCause::NotSupported { feature: request.feature() }),
                }
            }
            None => return Err(ErrorCause::NotSupported { feature: request.feature() }),
        })
    }
    fn poll_request<'gc>(&self, mc: &Mutation<'gc>, key: &Self::RequestKey, _: &mut Entity<'gc, C, Self>) -> Result<AsyncResult<Result<Value<'gc, C, Self>, String>>, ErrorCause<C, Self>> {
        Ok(match key.poll() {
            AsyncResult::Completed(Ok(x)) => AsyncResult::Completed(Ok(C::from_intermediate(mc, x)?)),
            AsyncResult::Completed(Err(x)) => AsyncResult::Completed(Err(x)),
            AsyncResult::Pending => AsyncResult::Pending,
            AsyncResult::Consumed => AsyncResult::Consumed,
        })
    }

    fn perform_command<'gc, 'a>(&self, mc: &Mutation<'gc>, command: Command<'gc, 'a, C, Self>, entity: &mut Entity<'gc, C, Self>) -> Result<MaybeAsync<Result<(), String>, Self::CommandKey>, ErrorCause<C, Self>> {
        Ok(match self.config.command.as_ref() {
            Some(handler) => {
                let key = CommandKey(Arc::new(Mutex::new(AsyncResult::new())));
                match handler(self, mc, CommandKey(key.0.clone()), command, entity) {
                    CommandStatus::Handled => MaybeAsync::Async(key),
                    CommandStatus::UseDefault { key: _, command } => return Err(ErrorCause::NotSupported { feature: command.feature() }),
                }
            }
            None => return Err(ErrorCause::NotSupported { feature: command.feature() }),
        })
    }
    fn poll_command<'gc>(&self, _: &Mutation<'gc>, key: &Self::CommandKey, _: &mut Entity<'gc, C, Self>) -> Result<AsyncResult<Result<(), String>>, ErrorCause<C, Self>> {
        Ok(key.poll())
    }

    fn send_message(&self, msg_type: String, values: Vec<(String, Json)>, targets: Vec<String>, expect_reply: bool) -> Result<Option<Self::ExternReplyKey>, ErrorCause<C, StdSystem<C>>> {
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
    fn poll_reply(&self, key: &Self::ExternReplyKey) -> AsyncResult<Option<Json>> {
        let mut message_replies = self.message_replies.lock().unwrap();
        let entry = message_replies.get(key).unwrap();
        if entry.value.is_some() {
            return AsyncResult::Completed(message_replies.remove(key).unwrap().value);
        }
        if entry.timestamp.elapsed().as_millis() as u32 >= MESSAGE_REPLY_TIMEOUT_MS {
            message_replies.remove(key).unwrap();
            return AsyncResult::Completed(None);
        }
        AsyncResult::Pending
    }
    fn send_reply(&self, key: Self::InternReplyKey, value: Json) -> Result<(), ErrorCause<C, Self>> {
        Ok(self.message_sender.send(OutgoingMessage::Reply { value, reply_key: key }).unwrap())
    }
    fn receive_message(&self) -> Option<IncomingMessage<C, Self>> {
        self.message_receiver.try_recv().ok()
    }
}
