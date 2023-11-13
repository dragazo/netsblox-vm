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
use crate::process::*;
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
    services_url: String,

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
    fn poll(&self) -> AsyncResult<Result<C::Intermediate, String>> { self.0.lock().unwrap().poll() }
}
impl<C: CustomTypes<StdSystem<C>>> Key<Result<C::Intermediate, String>> for RequestKey<C> {
    /// Completes the request with the given result.
    /// A value of [`Ok`] denotes a successful request, whose value will be returned to the system
    /// after conversion under [`CustomTypes::from_intermediate`].
    /// A value of [`Err`] denotes a failed request, which will be returned as an error to the runtime,
    /// subject to the caller's [`ErrorScheme`] setting.
    fn complete(self, value: Result<C::Intermediate, String>) {
        assert!(self.0.lock().unwrap().complete(value).is_ok())
    }
}

/// A [`StdSystem`] key type for an asynchronous command.
pub struct CommandKey(Arc<Mutex<AsyncResult<Result<(), String>>>>);
impl CommandKey {
    fn poll(&self) -> AsyncResult<Result<(), String>> { self.0.lock().unwrap().poll() }
}
impl Key<Result<(), String>> for CommandKey {
    /// Completes the command.
    /// A value of [`Ok`] denotes a successful command.
    /// A value of [`Err`] denotes a failed command, which will be returned as an error to the runtime,
    /// subject to the caller's [`ErrorScheme`] setting.
    fn complete(self, value: Result<(), String>) {
        assert!(self.0.lock().unwrap().complete(value).is_ok())
    }
}

struct ClockCache {
    value: Mutex<OffsetDateTime>,
    precision: Precision,
}

/// A clock with optional coarse granularity.
pub struct Clock {
    utc_offset: UtcOffset,
    cache: Option<ClockCache>,
}
impl Clock {
    /// Creates a new [`Clock`] with the specified [`UtcOffset`] and (optional) cache [`Precision`] (see [`Clock::read`]).
    pub fn new(utc_offset: UtcOffset, cache_precision: Option<Precision>) -> Self {
        let mut res = Self { utc_offset, cache: None };
        if let Some(precision) = cache_precision {
            res.cache = Some(ClockCache { value: Mutex::new(res.update()), precision });
        }
        res
    }
    /// Reads the current time with the specified level of precision.
    /// If caching was enabled by [`Clock::new`], requests at or below the cache precision level will use the cached timestamp.
    /// In any other case, the real current time is fetched by [`Clock::update`] and the result is stored in the cache if caching is enabled.
    pub fn read(&self, precision: Precision) -> OffsetDateTime {
        match &self.cache {
            Some(cache) if precision <= cache.precision => *cache.value.lock().unwrap(),
            _ => self.update(),
        }
    }
    /// Reads the real world time and stores the result in the cache if caching was enabled by [`Clock::new`].
    pub fn update(&self) -> OffsetDateTime {
        let t = OffsetDateTime::now_utc().to_offset(self.utc_offset);
        if let Some(cache) = &self.cache {
            *cache.value.lock().unwrap() = t;
        }
        t
    }
}

type MessageReplies = BTreeMap<ExternReplyKey, ReplyEntry>;

async fn call_rpc_async<C: CustomTypes<StdSystem<C>>>(context: &Context, client: &reqwest::Client, service: &str, rpc: &str, args: &[(&str, &Json)]) -> Result<SimpleValue, String> {
    let time = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_millis();
    let url = format!("{services_url}/{service}/{rpc}?clientId={client_id}&t={time}",
        services_url = context.services_url, client_id = context.client_id);
    let args = args.iter().copied().collect::<BTreeMap<_,_>>();

    let res = match client.post(url).json(&args).send().await {
        Ok(x) => x,
        Err(_) => return Err(format!("Failed to reach {}", context.base_url)),
    };

    let content_type = res.headers().get("Content-Type").and_then(|x| String::from_utf8(x.as_bytes().to_owned()).ok()).map(|x| x.to_lowercase()).unwrap_or_else(|| "unknown".into());
    let status = res.status();

    let res = match res.bytes().await {
        Ok(res) => (*res).to_owned(),
        Err(_) => return Err("Failed to read response body".to_owned()),
    };

    if !status.is_success() {
        return Err(String::from_utf8(res).ok().unwrap_or_else(|| "Received ill-formed error message".into()));
    }

    if content_type.contains("image/") {
        Ok(SimpleValue::Image(Image { content: res, center: None }))
    } else if content_type.contains("audio/") {
        Ok(SimpleValue::Audio(Audio { content: res }))
    } else if let Some(x) = parse_json_slice::<Json>(&res).ok() {
        SimpleValue::from_netsblox_json(x).map_err(|e| format!("Received ill-formed success value: {e:?}"))
    } else if let Ok(x) = String::from_utf8(res) {
        Ok(SimpleValue::String(x))
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
    clock: Arc<Clock>,

    rpc_request_pipe: Sender<RpcRequest<C>>,

    message_replies: Arc<Mutex<MessageReplies>>,
    message_sender: Sender<OutgoingMessage<C, Self>>,
    message_injector: Sender<IncomingMessage<C, Self>>,
    message_receiver: Receiver<IncomingMessage<C, Self>>,
}
impl<C: CustomTypes<StdSystem<C>>> StdSystem<C> {
    /// Equivalent to [`StdSystem::new_async`] except that it can be executed outside of async context.
    /// Note that using this from within async context will result in a panic from `tokio` trying to create a runtime within a runtime.
    #[tokio::main(flavor = "current_thread")]
    pub async fn new_sync(base_url: String, project_name: Option<&str>, config: Config<C, Self>, clock: Arc<Clock>) -> Self {
        Self::new_async(base_url, project_name, config, clock).await
    }
    /// Initializes a new instance of [`StdSystem`] targeting the given NetsBlox server base url (e.g., `https://cloud.netsblox.org`).
    pub async fn new_async(base_url: String, project_name: Option<&str>, config: Config<C, Self>, clock: Arc<Clock>) -> Self {
        let configuration = reqwest::get(format!("{base_url}/configuration")).await.unwrap().json::<BTreeMap<String, Json>>().await.unwrap();
        let services_hosts = configuration["servicesHosts"].as_array().unwrap();

        let mut context = Context {
            base_url,
            services_url: services_hosts[0].as_object().unwrap().get("url").unwrap().as_str().unwrap().to_owned(),
            client_id: format!("_vm-{}", names::Generator::default().next().unwrap()),
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
                let ws_url = format!("{}/network/{client_id}/connect", if let Some(x) = base_url.strip_prefix("http") { format!("ws{x}") } else { format!("wss://{base_url}") });
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
                                        let values = values.into_iter().filter_map(|(k, v)| SimpleValue::from_netsblox_json(v).ok().map(|v| (k, v))).collect();
                                        in_sender.send(IncomingMessage { msg_type, values, reply_key }).unwrap();
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
                            "srcId": format!("{project_name}@{client_id}"),
                            "msgType": msg_type,
                            "content": values.into_iter().collect::<JsonMap<_,_>>(),
                        }),
                        OutgoingMessage::Blocking { msg_type, values, targets, reply_key } => json!({
                            "type": "message",
                            "dstId": targets,
                            "srcId": format!("{project_name}@{client_id}"),
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
        let meta = client.post(format!("{}/projects/", context.base_url))
            .json(&json!({ "clientId": context.client_id, "name": context.project_name }))
            .send().await.unwrap()
            .json::<BTreeMap<String, Json>>().await.unwrap();
        context.project_id = meta["id"].as_str().unwrap().to_owned();

        let roles = &meta["roles"].as_object().unwrap();
        let (first_role_id, first_role_meta) = roles.get_key_value(roles.keys().next().unwrap()).unwrap();
        let first_role_meta = first_role_meta.as_object().unwrap();
        context.role_id = first_role_id.to_owned();
        context.role_name = first_role_meta.get("name").unwrap().as_str().unwrap().to_owned();

        client.post(format!("{}/network/{}/state", context.base_url, context.client_id))
            .json(&json!({ "state": { "external": { "address": context.project_name, "appId": "vm" } } }))
            .send().await.unwrap();

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
                        request.key.complete(res.map(Into::into));
                    });
                }
            }
            thread::spawn(move || handler(client, context, receiver));

            sender
        };

        let mut seed: <ChaChaRng as SeedableRng>::Seed = Default::default();
        getrandom::getrandom(&mut seed).expect("failed to generate random seed");

        let context_clone = context.clone();
        let config = config.fallback(&Config {
            request: Some(Rc::new(move |system, _, key, request, _| {
                match request {
                    Request::Rpc { service, rpc, args } => match (service.as_str(), rpc.as_str(), args.as_slice()) {
                        ("PublicRoles", "getPublicRoleId", []) => {
                            key.complete(Ok(SimpleValue::String(format!("{}@{}#vm", context_clone.project_name, context_clone.client_id)).into()));
                            RequestStatus::Handled
                        }
                        _ => {
                            match args.into_iter().map(|(k, v)| Ok((k, v.to_simple()?.into_netsblox_json()?))).collect::<Result<_,ErrorCause<_,_>>>() {
                                Ok(args) => system.rpc_request_pipe.send(RpcRequest { service, rpc, args, key }).unwrap(),
                                Err(err) => key.complete(Err(format!("failed to convert RPC args to json: {err:?}"))),
                            }
                            RequestStatus::Handled
                        }
                    }
                    _ => RequestStatus::UseDefault { key, request },
                }
            })),
            command: None,
        });

        Self {
            config, context, client, clock,
            rng: Mutex::new(ChaChaRng::from_seed(seed)),
            rpc_request_pipe,
            message_replies, message_sender, message_receiver, message_injector,
        }
    }

    /// Asynchronously calls an RPC and returns the result.
    /// This function directly makes requests to NetsBlox, bypassing any RPC hook defined by [`Config`].
    pub async fn call_rpc_async(&self, service: &str, rpc: &str, args: &[(&str, &Json)]) -> Result<SimpleValue, String> {
        call_rpc_async::<C>(&self.context, &self.client, service, rpc, args).await
    }

    /// Gets the public id of the running system that can be used to send messages to this client.
    pub fn get_public_id(&self) -> String {
        format!("{}@{}#vm", self.context.project_name, self.context.client_id)
    }

    /// Injects a message into the receiving queue as if received over the network.
    pub fn inject_message(&self, msg_type: String, values: Vec<(String, SimpleValue)>) {
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

    fn time(&self, precision: Precision) -> SysTime {
        SysTime::Real { local: self.clock.read(precision) }
    }

    fn perform_request<'gc>(&self, mc: &Mutation<'gc>, request: Request<'gc, C, Self>, proc: &mut Process<'gc, C, Self>) -> Result<Self::RequestKey, ErrorCause<C, Self>> {
        Ok(match self.config.request.as_ref() {
            Some(handler) => {
                let key = RequestKey(Arc::new(Mutex::new(AsyncResult::new())));
                match handler(self, mc, RequestKey(key.0.clone()), request, proc) {
                    RequestStatus::Handled => key,
                    RequestStatus::UseDefault { key: _, request } => return Err(ErrorCause::NotSupported { feature: request.feature() }),
                }
            }
            None => return Err(ErrorCause::NotSupported { feature: request.feature() }),
        })
    }
    fn poll_request<'gc>(&self, mc: &Mutation<'gc>, key: &Self::RequestKey, _: &mut Process<'gc, C, Self>) -> Result<AsyncResult<Result<Value<'gc, C, Self>, String>>, ErrorCause<C, Self>> {
        Ok(match key.poll() {
            AsyncResult::Completed(Ok(x)) => AsyncResult::Completed(Ok(C::from_intermediate(mc, x)?)),
            AsyncResult::Completed(Err(x)) => AsyncResult::Completed(Err(x)),
            AsyncResult::Pending => AsyncResult::Pending,
            AsyncResult::Consumed => AsyncResult::Consumed,
        })
    }

    fn perform_command<'gc>(&self, mc: &Mutation<'gc>, command: Command<'gc, '_, C, Self>, proc: &mut Process<'gc, C, Self>) -> Result<Self::CommandKey, ErrorCause<C, Self>> {
        Ok(match self.config.command.as_ref() {
            Some(handler) => {
                let key = CommandKey(Arc::new(Mutex::new(AsyncResult::new())));
                match handler(self, mc, CommandKey(key.0.clone()), command, proc) {
                    CommandStatus::Handled => key,
                    CommandStatus::UseDefault { key: _, command } => return Err(ErrorCause::NotSupported { feature: command.feature() }),
                }
            }
            None => return Err(ErrorCause::NotSupported { feature: command.feature() }),
        })
    }
    fn poll_command<'gc>(&self, _: &Mutation<'gc>, key: &Self::CommandKey, _: &mut Process<'gc, C, Self>) -> Result<AsyncResult<Result<(), String>>, ErrorCause<C, Self>> {
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
        self.message_sender.send(OutgoingMessage::Reply { value, reply_key: key }).unwrap();
        Ok(())
    }
    fn receive_message(&self) -> Option<IncomingMessage<C, Self>> {
        self.message_receiver.try_recv().ok()
    }
}
