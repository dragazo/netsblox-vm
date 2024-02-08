//! An customizable implementation of [`System`] which depends on the standard library.
//! 
//! This submodule is only available with the [`std-system`](crate) feature flag.

use alloc::string::ToString;
use alloc::collections::BTreeMap;
use alloc::borrow::ToOwned;
use alloc::vec::Vec;
use alloc::rc::Rc;

use std::time::{Duration, SystemTime, UNIX_EPOCH};
use std::sync::{Arc, Mutex};
use std::sync::mpsc::{Sender, Receiver, channel};
use std::thread;

use rand::distributions::uniform::{SampleUniform, SampleRange};
use rand_chacha::ChaChaRng;
use rand::{Rng, SeedableRng};
use tokio_tungstenite::tungstenite::Message;
use futures::{StreamExt, SinkExt};
use uuid::Uuid;

use crate::runtime::*;
use crate::process::*;
use crate::json::*;
use crate::gc::*;
use crate::std_util::*;
use crate::vecmap::*;
use crate::compact_str::*;
use crate::*;

const MESSAGE_REPLY_TIMEOUT: Duration = Duration::from_millis(1500);

async fn call_rpc_async<C: CustomTypes<S>, S: System<C>>(context: &NetsBloxContext, client: &reqwest::Client, host: Option<&str>, service: &str, rpc: &str, args: &[(&str, &Json)]) -> Result<SimpleValue, CompactString> {
    let time = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_millis();
    let url = format!("{service_host}/{service}/{rpc}?clientId={client_id}&t={time}",
        service_host = host.unwrap_or(context.default_service_host.as_str()), client_id = context.client_id);
    let args = args.iter().copied().collect::<BTreeMap<_,_>>();

    let res = match client.post(url).json(&args).send().await {
        Ok(x) => x,
        Err(_) => return Err(format_compact!("Failed to reach {}", context.base_url)),
    };

    let content_type = res.headers().get("Content-Type").and_then(|x| CompactString::from_utf8(x.as_bytes().to_owned()).ok()).map(|x| x.to_lowercase()).unwrap_or_else(|| "unknown".into());
    let status = res.status();

    let res = match res.bytes().await {
        Ok(res) => (*res).to_owned(),
        Err(_) => return Err(CompactString::new("Failed to read response body")),
    };

    if !status.is_success() {
        return Err(CompactString::from_utf8(res).ok().unwrap_or_else(|| "Received ill-formed error message".into()));
    }

    if content_type.contains("image/") {
        Ok(SimpleValue::Image(Image { content: res, center: None }))
    } else if content_type.contains("audio/") {
        Ok(SimpleValue::Audio(Audio { content: res }))
    } else if let Some(x) = parse_json_slice::<Json>(&res).ok() {
        SimpleValue::from_netsblox_json(x).map_err(|e| format_compact!("Received ill-formed success value: {e:?}"))
    } else if let Ok(x) = CompactString::from_utf8(res) {
        Ok(SimpleValue::String(x))
    } else {
        Err("Received ill-formed success value".into())
    }
}

/// A type implementing the [`System`] trait which supports all features.
/// 
/// [`StdSystem`] can be configured with [`CustomTypes`] and [`Config`],
/// which together allow for the definition of any external features (e.g., defining syscalls),
/// as well as overriding default behavior (e.g., rpc intercepting).
pub struct StdSystem<C: CustomTypes<StdSystem<C>>> {
    config: Config<C, Self>,
    context: Arc<NetsBloxContext>,
    client: reqwest::Client,
    rng: Mutex<ChaChaRng>,
    clock: Arc<Clock>,

    rpc_request_pipe: Sender<RpcRequest<C, Self>>,

    message_replies: Arc<Mutex<BTreeMap<ExternReplyKey, ReplyEntry>>>,
    message_sender: Sender<OutgoingMessage>,
    message_injector: Sender<IncomingMessage>,
    message_receiver: Receiver<IncomingMessage>,
}
impl<C: CustomTypes<StdSystem<C>>> StdSystem<C> {
    /// Equivalent to [`StdSystem::new_async`] except that it can be executed outside of async context.
    /// Note that using this from within async context can result in a panic from, e.g., `tokio` trying to create a runtime within a runtime.
    #[tokio::main(flavor = "current_thread")]
    pub async fn new_sync(base_url: CompactString, project_name: Option<&str>, config: Config<C, Self>, clock: Arc<Clock>) -> Self {
        Self::new_async(base_url, project_name, config, clock).await
    }
    /// Initializes a new instance of [`StdSystem`] targeting the given NetsBlox server base url, e.g., `https://cloud.netsblox.org`.
    pub async fn new_async(base_url: CompactString, project_name: Option<&str>, config: Config<C, Self>, clock: Arc<Clock>) -> Self {
        let client = reqwest::Client::builder().build().unwrap();
        let default_service_host = {
            let configuration = client.get(format!("{base_url}/configuration")).send().await.unwrap().json::<BTreeMap<CompactString, Json>>().await.unwrap();
            let services_hosts = configuration["servicesHosts"].as_array().unwrap();
            services_hosts[0].as_object().unwrap().get("url").unwrap().as_str().unwrap().into()
        };

        let mut context = NetsBloxContext {
            base_url,
            default_service_host,
            client_id: format_compact!("_vm-{}", names::Generator::default().next().unwrap()),
            project_name: project_name.unwrap_or("untitled").into(),

            project_id: CompactString::default(),
            role_name: CompactString::default(),
            role_id: CompactString::default(),
        };

        let message_replies = Arc::new(Mutex::new(Default::default()));
        let (message_sender, message_receiver, message_injector, ws_finish_flag) = {
            let (base_url, client_id, project_name, message_replies) = (context.base_url.clone(), context.client_id.clone(), context.project_name.clone(), message_replies.clone());
            let (out_sender, out_receiver) = channel();
            let (in_sender, in_receiver) = channel();
            let finish_flag = Arc::new(());

            #[tokio::main(flavor = "multi_thread", worker_threads = 1)]
            async fn handler(base_url: CompactString, client_id: CompactString, project_name: CompactString, message_replies: Arc<Mutex<BTreeMap<ExternReplyKey, ReplyEntry>>>, out_receiver: Receiver<OutgoingMessage>, in_sender: Sender<IncomingMessage>, finish_flag: Arc<()>) {
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
                                Ok(Message::Text(raw)) => match parse_json::<BTreeMap<CompactString, Json>>(&raw) {
                                    Ok(x) => x,
                                    Err(_) => return,
                                }
                                _ => return,
                            };
                            match msg.get("type").and_then(|x| x.as_str()).unwrap_or("unknown") {
                                "ping" => ws_sender_sender_clone.send(Message::Text(json!({ "type": "pong" }).to_string())).await.unwrap(),
                                "message" => {
                                    let (msg_type, values) = match (msg.remove("msgType"), msg.remove("content")) {
                                        (Some(Json::String(msg_type)), Some(Json::Object(values))) => (msg_type.into(), values),
                                        _ => return,
                                    };
                                    if msg_type == "__reply__" {
                                        let (value, reply_key) = match ({ values }.remove("body"), msg.remove("requestId")) {
                                            (Some(value), Some(Json::String(request_id))) => (value, ExternReplyKey { request_id: request_id.into() }),
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
                                                (Some(Json::String(src_id)), Some(Json::String(request_id))) => Some(InternReplyKey { src_id: src_id.into(), request_id: request_id.into() }),
                                                _ => return,
                                            }
                                            false => None,
                                        };
                                        let values = values.into_iter().filter_map(|(k, v)| SimpleValue::from_netsblox_json(v).ok().map(|v| (k.into(), v))).collect();
                                        in_sender.send(IncomingMessage { msg_type, values, reply_key }).unwrap();
                                    }
                                }
                                _ => (),
                            }
                        }
                    }).await;
                });

                ws_sender_sender.send(Message::Text(json!({ "type": "set-uuid", "clientId": client_id }).to_string())).await.unwrap();
                drop(finish_flag);

                let src_id = format_compact!("{project_name}@{client_id}#vm");
                fn resolve_targets<'a>(targets: &'a mut [CompactString], src_id: &CompactString) -> &'a mut [CompactString] {
                    for target in targets.iter_mut() {
                        if *target == "everyone in room" {
                            target.clone_from(src_id);
                        }
                    }
                    targets
                }
                while let Ok(request) = out_receiver.recv() {
                    let msg = match request {
                        OutgoingMessage::Normal { msg_type, values, mut targets } => json!({
                            "type": "message",
                            "dstId": resolve_targets(&mut targets, &src_id),
                            "srcId": src_id,
                            "msgType": msg_type,
                            "content": values.into_iter().collect::<BTreeMap<_,_>>(),
                        }),
                        OutgoingMessage::Blocking { msg_type, values, mut targets, reply_key } => json!({
                            "type": "message",
                            "dstId": resolve_targets(&mut targets, &src_id),
                            "srcId": src_id,
                            "msgType": msg_type,
                            "requestId": reply_key.request_id,
                            "content": values.into_iter().collect::<BTreeMap<_,_>>(),
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
            let finish_flag_clone = finish_flag.clone();
            thread::spawn(move || handler(base_url, client_id, project_name, message_replies, out_receiver, in_sender_clone, finish_flag_clone));

            (out_sender, in_receiver, in_sender, Arc::downgrade(&finish_flag))
        };

        while ws_finish_flag.upgrade().is_some() {
            tokio::time::sleep(Duration::from_millis(10)).await;
        }

        let meta = client.post(format!("{}/projects/", context.base_url))
            .json(&json!({ "clientId": context.client_id, "name": context.project_name }))
            .send().await.unwrap()
            .json::<BTreeMap<CompactString, Json>>().await.unwrap();
        context.project_id = meta["id"].as_str().unwrap().into();

        let roles = meta["roles"].as_object().unwrap();
        let (first_role_id, first_role_meta) = roles.get_key_value(roles.keys().next().unwrap()).unwrap();
        let first_role_meta = first_role_meta.as_object().unwrap();
        context.role_id = first_role_id.into();
        context.role_name = first_role_meta.get("name").unwrap().as_str().unwrap().into();

        client.post(format!("{}/network/{}/state", context.base_url, context.client_id))
            .json(&json!({ "state": { "external": { "address": context.project_name, "appId": "vm" } } }))
            .send().await.unwrap();

        let context = Arc::new(context);
        let rpc_request_pipe = {
            let (client, context) = (client.clone(), context.clone());
            let (sender, receiver) = channel();

            #[tokio::main(flavor = "multi_thread", worker_threads = 1)]
            async fn handler<C: CustomTypes<StdSystem<C>>>(client: reqwest::Client, context: Arc<NetsBloxContext>, receiver: Receiver<RpcRequest<C, StdSystem<C>>>) {
                while let Ok(RpcRequest { key, host, service, rpc, args }) = receiver.recv() {
                    let (client, context) = (client.clone(), context.clone());
                    tokio::spawn(async move {
                        let res = call_rpc_async::<C, StdSystem<C>>(&context, &client, host.as_deref(), &service, &rpc, &args.iter().map(|x| (x.0.as_str(), x.1)).collect::<Vec<_>>()).await;
                        key.complete(res.map(Into::into));
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
            request: Some(Rc::new(move |_, key, request, proc| {
                match request {
                    Request::Rpc { host, service, rpc, args } => match (host.as_deref(), service.as_str(), rpc.as_str(), args.as_slice()) {
                        (_, "PublicRoles", "getPublicRoleId", []) => {
                            key.complete(Ok(SimpleValue::String(format_compact!("{}@{}#vm", context_clone.project_name, context_clone.client_id)).into()));
                            RequestStatus::Handled
                        }
                        _ => {
                            match args.into_iter().map(|(k, v)| Ok((k, v.to_simple()?.into_netsblox_json()))).collect::<Result<_,ToSimpleError<_,_>>>() {
                                Ok(args) => proc.global_context.borrow().system.rpc_request_pipe.send(RpcRequest { host, service, rpc, args, key }).unwrap(),
                                Err(err) => key.complete(Err(format_compact!("failed to convert RPC args to json: {err:?}"))),
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
    pub async fn call_rpc_async(&self, host: Option<&str>, service: &str, rpc: &str, args: &[(&str, &Json)]) -> Result<SimpleValue, CompactString> {
        call_rpc_async::<C, Self>(&self.context, &self.client, host, service, rpc, args).await
    }

    /// Gets the public id of the running system that can be used to send messages to this client.
    pub fn get_public_id(&self) -> CompactString {
        format_compact!("{}@{}#vm", self.context.project_name, self.context.client_id)
    }

    /// Injects a message into the receiving queue as if received over the network.
    pub fn inject_message(&self, msg_type: CompactString, values: VecMap<CompactString, SimpleValue, false>) {
        self.message_injector.send(IncomingMessage { msg_type, values, reply_key: None }).unwrap();
    }

    #[cfg(debug_assertions)]
    fn check_runtime_borrows<'gc>(mc: &Mutation<'gc>, proc: &mut Process<'gc, C, Self>) {
        fn check_symbols<'gc, C: CustomTypes<StdSystem<C>>>(mc: &Mutation<'gc>, symbols: &SymbolTable<'gc, C, StdSystem<C>>) {
            for symbol in symbols.iter() {
                match &*symbol.1.get() {
                    Value::Bool(_) | Value::Number(_) | Value::String(_) | Value::Audio(_) | Value::Image(_) | Value::Native(_) => (),
                    Value::List(x) => { x.borrow_mut(mc); }
                    Value::Closure(x) => { x.borrow_mut(mc); }
                    Value::Entity(x) => { x.borrow_mut(mc); }
                }
            }
        }
        fn check_entity<'gc, C: CustomTypes<StdSystem<C>>>(mc: &Mutation<'gc>, entity: &mut Entity<'gc, C, StdSystem<C>>) {
            check_symbols(mc, &entity.fields);
            if let Some(original) = entity.original {
                check_entity(mc, &mut *original.borrow_mut(mc));
            }
        }

        let global_context = proc.global_context.borrow_mut(mc);
        check_symbols(mc, &global_context.globals);
        for entry in proc.get_call_stack() {
            check_symbols(mc, &entry.locals);
            check_entity(mc, &mut entry.entity.borrow_mut(mc));
        }
        for entity in global_context.entities.iter() {
            check_entity(mc, &mut *entity.1.borrow_mut(mc));
        }
    }
}
impl<C: CustomTypes<StdSystem<C>>> System<C> for StdSystem<C> {
    type RequestKey = AsyncKey<Result<C::Intermediate, CompactString>>;
    type CommandKey = AsyncKey<Result<(), CompactString>>;

    fn rand<T: SampleUniform, R: SampleRange<T>>(&self, range: R) -> T {
        self.rng.lock().unwrap().gen_range(range)
    }

    fn time(&self, precision: Precision) -> SysTime {
        SysTime::Real { local: self.clock.read(precision) }
    }

    fn perform_request<'gc>(&self, mc: &Mutation<'gc>, request: Request<'gc, C, Self>, proc: &mut Process<'gc, C, Self>) -> Result<Self::RequestKey, ErrorCause<C, Self>> {
        #[cfg(debug_assertions)]
        Self::check_runtime_borrows(mc, proc);

        Ok(match self.config.request.as_ref() {
            Some(handler) => {
                let key = AsyncKey::new();
                match handler(mc, key.clone(), request, proc) {
                    RequestStatus::Handled => key,
                    RequestStatus::UseDefault { key: _, request } => return Err(ErrorCause::NotSupported { feature: request.feature() }),
                }
            }
            None => return Err(ErrorCause::NotSupported { feature: request.feature() }),
        })
    }
    fn poll_request<'gc>(&self, mc: &Mutation<'gc>, key: &Self::RequestKey, _proc: &mut Process<'gc, C, Self>) -> Result<AsyncResult<Result<Value<'gc, C, Self>, CompactString>>, ErrorCause<C, Self>> {
        #[cfg(debug_assertions)]
        Self::check_runtime_borrows(mc, _proc);

        Ok(match key.poll() {
            AsyncResult::Completed(Ok(x)) => AsyncResult::Completed(Ok(C::from_intermediate(mc, x))),
            AsyncResult::Completed(Err(x)) => AsyncResult::Completed(Err(x)),
            AsyncResult::Pending => AsyncResult::Pending,
            AsyncResult::Consumed => AsyncResult::Consumed,
        })
    }

    fn perform_command<'gc>(&self, mc: &Mutation<'gc>, command: Command<'gc, '_, C, Self>, proc: &mut Process<'gc, C, Self>) -> Result<Self::CommandKey, ErrorCause<C, Self>> {
        #[cfg(debug_assertions)]
        Self::check_runtime_borrows(mc, proc);

        Ok(match self.config.command.as_ref() {
            Some(handler) => {
                let key = AsyncKey::new();
                match handler(mc, key.clone(), command, proc) {
                    CommandStatus::Handled => key,
                    CommandStatus::UseDefault { key: _, command } => return Err(ErrorCause::NotSupported { feature: command.feature() }),
                }
            }
            None => return Err(ErrorCause::NotSupported { feature: command.feature() }),
        })
    }
    fn poll_command<'gc>(&self, _mc: &Mutation<'gc>, key: &Self::CommandKey, _proc: &mut Process<'gc, C, Self>) -> Result<AsyncResult<Result<(), CompactString>>, ErrorCause<C, Self>> {
        #[cfg(debug_assertions)]
        Self::check_runtime_borrows(_mc, _proc);

        Ok(key.poll())
    }

    fn send_message(&self, msg_type: CompactString, values: VecMap<CompactString, Json, false>, targets: Vec<CompactString>, expect_reply: bool) -> Result<Option<ExternReplyKey>, ErrorCause<C, StdSystem<C>>> {
        let (msg, reply_key) = match expect_reply {
            false => (OutgoingMessage::Normal { msg_type, values, targets }, None),
            true => {
                let reply_key = ExternReplyKey { request_id: format_compact!("{}", Uuid::new_v4()) };
                let expiry = self.clock.read(Precision::Medium) + MESSAGE_REPLY_TIMEOUT;
                self.message_replies.lock().unwrap().insert(reply_key.clone(), ReplyEntry { expiry, value: None });
                (OutgoingMessage::Blocking { msg_type, values, targets, reply_key: reply_key.clone() }, Some(reply_key))
            }
        };
        self.message_sender.send(msg).unwrap();
        Ok(reply_key)
    }
    fn poll_reply(&self, key: &ExternReplyKey) -> AsyncResult<Option<Json>> {
        let mut message_replies = self.message_replies.lock().unwrap();
        let entry = message_replies.get(key).unwrap();
        if entry.value.is_some() {
            return AsyncResult::Completed(message_replies.remove(key).unwrap().value);
        }
        if self.clock.read(Precision::Low) > entry.expiry {
            message_replies.remove(key).unwrap();
            return AsyncResult::Completed(None);
        }
        AsyncResult::Pending
    }
    fn send_reply(&self, key: InternReplyKey, value: Json) -> Result<(), ErrorCause<C, Self>> {
        self.message_sender.send(OutgoingMessage::Reply { value, reply_key: key }).unwrap();
        Ok(())
    }
    fn receive_message(&self) -> Option<IncomingMessage> {
        self.message_receiver.try_recv().ok()
    }
}
