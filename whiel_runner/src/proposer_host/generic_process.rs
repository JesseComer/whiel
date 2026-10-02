//! Persistent, provider-neutral process endpoint for proposer API wire 3.

use std::ffi::OsString;
use std::future::Future;
use std::io::{self, Read};
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::{DirBuilderExt, PermissionsExt};
use std::path::PathBuf;
use std::pin::Pin;
use std::process::Command;
use std::sync::Arc;
use std::sync::atomic::{AtomicU8, AtomicU64, Ordering};
use std::task::Poll;
use std::time::Duration;

use tokio::net::unix::OwnedWriteHalf;
use tokio::net::{UnixListener, UnixStream};
use tokio::sync::mpsc;
use tokio::task::JoinHandle;

use crate::framework2::strict_json::decode_strict_json;
use crate::proposer_api::wire::{
    Frame, MAX_PACKET_BYTES, Operation, ProposerCleanupError, ProposerCleanupFuture,
    RequestOutcome, SOCKET_ENV, ShutdownReason, TOKEN_ENV, TransportRejection, next_sequence,
};
use crate::proposer_api::{
    AgentProvider, AgentPush, AgentResponseWriter, AgentSourceCancellation, AgentSourceFuture,
    AgentSourceOutcome, AgentToolResponse, AgentToolSurface, ApiCapabilities, NegotiatedApi,
    ProposerTerminalFailure,
};
use crate::runtime::CancellationToken;

use super::generic_child::{ChildCleanup, EndpointChild, OwnedDirectory};
use super::generic_io::{
    ApiTrafficLimits, ApiTrafficUsage, Budget, Packet, read_packet, write_packet,
};

const IDLE: u8 = 0;
const REQUEST: u8 = 1;
const SHUTDOWN: u8 = 2;

#[derive(Clone, Debug)]
pub struct GenericProcessConfig {
    pub executable: PathBuf,
    pub arguments: Vec<OsString>,
    pub scratch_parent: PathBuf,
    pub startup_timeout: Duration,
    pub shutdown_timeout: Duration,
    pub fallback_timeout: Duration,
    pub traffic_limits: ApiTrafficLimits,
}

impl GenericProcessConfig {
    pub fn new(executable: PathBuf, arguments: Vec<OsString>) -> Self {
        Self {
            executable,
            arguments,
            scratch_parent: PathBuf::from("/tmp"),
            startup_timeout: Duration::from_secs(15),
            shutdown_timeout: Duration::from_secs(2),
            fallback_timeout: Duration::from_secs(5),
            traffic_limits: ApiTrafficLimits::default(),
        }
    }
}

/// Typed B-host startup causes; callers must not infer them from diagnostic text.
/// Cancelled is returned only after any started endpoint has joined cleanup.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GenericProcessStartupError {
    Cancelled,
    TimedOut,
    ResourceExhausted,
    CleanupFailed(ProposerCleanupError),
    ResourceExhaustedCleanupFailed(ProposerCleanupError),
}

impl std::fmt::Display for GenericProcessStartupError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Cancelled => f.write_str("proposer startup cancelled"),
            Self::TimedOut => f.write_str("proposer startup timed out"),
            Self::ResourceExhausted => {
                f.write_str("proposer API traffic allowance exhausted during startup")
            }
            Self::CleanupFailed(error) => write!(f, "proposer startup cleanup: {error}"),
            Self::ResourceExhaustedCleanupFailed(error) => write!(
                f,
                "proposer startup cleanup: {error}; proposer API traffic allowance exhausted during startup"
            ),
        }
    }
}
impl std::error::Error for GenericProcessStartupError {}

fn startup_error(reason: GenericProcessStartupError) -> io::Error {
    let kind = match reason {
        GenericProcessStartupError::Cancelled => io::ErrorKind::Interrupted,
        GenericProcessStartupError::TimedOut => io::ErrorKind::TimedOut,
        GenericProcessStartupError::ResourceExhausted => io::ErrorKind::Other,
        GenericProcessStartupError::CleanupFailed(_)
        | GenericProcessStartupError::ResourceExhaustedCleanupFailed(_) => io::ErrorKind::Other,
    };
    io::Error::new(kind, reason)
}

fn startup_cleanup_error(error: ProposerCleanupError, budget: &Budget) -> io::Error {
    startup_error(if budget.failure().is_some() {
        GenericProcessStartupError::ResourceExhaustedCleanupFailed(error)
    } else {
        GenericProcessStartupError::CleanupFailed(error)
    })
}

#[derive(Debug)]
struct RequestWriteCancelled;

impl std::fmt::Display for RequestWriteCancelled {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("proposer request write cancelled")
    }
}
impl std::error::Error for RequestWriteCancelled {}

fn is_cancelled_write(error: &io::Error) -> bool {
    error
        .get_ref()
        .is_some_and(|cause| cause.is::<RequestWriteCancelled>())
}

async fn request_write(
    write: impl Future<Output = io::Result<()>>,
    cancellation: &AgentSourceCancellation,
) -> io::Result<()> {
    tokio::select! {
        biased;
        _ = cancellation.cancelled() => Err(io::Error::new(io::ErrorKind::Interrupted, RequestWriteCancelled)),
        result = write => result,
    }
}

struct Connection {
    token: String,
    next_send: u64,
    writer: OwnedWriteHalf,
    incoming: mpsc::Receiver<io::Result<Packet>>,
    reader: Option<JoinHandle<()>>,
    reader_stop: CancellationToken,
    request_scope: Arc<AtomicU64>,
    phase: Arc<AtomicU8>,
}

impl Connection {
    fn new(stream: UnixStream, token: String, budget: Budget) -> Self {
        let (mut reader, writer) = stream.into_split();
        let (send, incoming) = mpsc::channel(1);
        let stop = CancellationToken::new();
        let reader_stop = stop.clone();
        let reader_token = token.clone();
        let request_scope = Arc::new(AtomicU64::new(0));
        let scope = Arc::clone(&request_scope);
        let phase = Arc::new(AtomicU8::new(IDLE));
        let reader_phase = Arc::clone(&phase);
        let reader = tokio::spawn(async move {
            let mut sequence = 1;
            loop {
                let result = tokio::select! {
                    biased;
                    _ = stop.cancelled() => break,
                    result = read_packet(&mut reader, &reader_token, sequence, &budget) => result,
                }
                .and_then(|packet| {
                    let phase = reader_phase.load(Ordering::Acquire);
                    let expected = if phase == SHUTDOWN {
                        None
                    } else {
                        Some(scope.load(Ordering::Acquire))
                    };
                    if phase == IDLE || packet.frame.request_id != expected {
                        return Err(io::Error::new(
                            io::ErrorKind::InvalidData,
                            "proposer message outside its active scope",
                        ));
                    }
                    Ok(packet)
                });
                let terminal = result.is_err();
                let delivered = tokio::select! {
                    biased;
                    _ = stop.cancelled() => false,
                    result = send.send(result) => result.is_ok(),
                };
                if terminal || !delivered {
                    break;
                }
                sequence = match next_sequence(sequence) {
                    Ok(value) => value,
                    Err(_) => break,
                };
            }
        });
        Self {
            token,
            next_send: 1,
            writer,
            incoming,
            reader: Some(reader),
            reader_stop,
            request_scope,
            phase,
        }
    }

    async fn send(
        &mut self,
        request_id: Option<u64>,
        operation: Operation,
        attachments: &[&[u8]],
        budget: &Budget,
        emergency: bool,
    ) -> io::Result<()> {
        let next = next_sequence(self.next_send)?;
        let frame = Frame::new(self.token.clone(), self.next_send, request_id, operation);
        write_packet(&mut self.writer, &frame, attachments, budget, emergency).await?;
        self.next_send = next;
        Ok(())
    }

    async fn receive(&mut self) -> io::Result<Packet> {
        self.incoming.recv().await.unwrap_or_else(|| {
            Err(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "proposer endpoint disconnected",
            ))
        })
    }

    async fn stop_reader(&mut self, timeout: Duration) -> Result<(), ProposerCleanupError> {
        self.reader_stop.cancel();
        if let Some(reader) = self.reader.as_mut() {
            tokio::time::timeout(timeout, reader)
                .await
                .map_err(|_| ProposerCleanupError::TimedOut)?
                .map_err(|_| ProposerCleanupError::Failed)?;
        }
        self.reader = None;
        Ok(())
    }
}

impl Drop for Connection {
    fn drop(&mut self) {
        self.reader_stop.cancel();
    }
}

struct RequestState {
    id: u64,
    complete: bool,
    joined: bool,
    cancellation: CancellationToken,
}

type PendingQuery<'a> = Pin<Box<dyn Future<Output = (u64, AgentToolResponse)> + Send + 'a>>;

async fn next_query(queries: &mut Vec<PendingQuery<'_>>) -> (u64, AgentToolResponse) {
    std::future::poll_fn(|context| {
        for (index, query) in queries.iter_mut().enumerate() {
            if let Poll::Ready(value) = query.as_mut().poll(context) {
                drop(queries.swap_remove(index));
                return Poll::Ready(value);
            }
        }
        Poll::Pending
    })
    .await
}

/// Explicit fallback join retained across fallible consuming engine constructors.
/// Normal input completion should use the provider's protocol shutdown first.
#[derive(Clone)]
pub struct GenericProcessCleanup {
    child: Arc<std::sync::Mutex<ChildCleanup>>,
    timeout: Duration,
}

impl GenericProcessCleanup {
    pub async fn stop_and_join(&self) -> Result<(), ProposerCleanupError> {
        let child = self.child.lock().unwrap_or_else(|p| p.into_inner()).clone();
        child.stop();
        let exit = child.join(self.timeout).await?;
        if exit.cleaned {
            Ok(())
        } else {
            Err(ProposerCleanupError::Failed)
        }
    }
}

/// Read-only cumulative API accounting, retained across moves and restarts.
#[derive(Clone)]
pub struct GenericProcessResourceStatus {
    budget: Budget,
}

impl GenericProcessResourceStatus {
    pub fn usage(&self) -> ApiTrafficUsage {
        self.budget.usage()
    }
    pub fn failure(&self) -> Option<String> {
        self.budget.failure()
    }
}

/// Keeps an engine-owned scratch root present while disk monitoring retains it.
/// This lease grants no endpoint or process-lifecycle authority.
#[derive(Clone)]
pub struct GenericProcessScratchLease {
    directory: Arc<OwnedDirectory>,
}

impl GenericProcessScratchLease {
    pub fn path(&self) -> &std::path::Path {
        &self.directory.0
    }
}

pub struct GenericProcessProposer {
    config: GenericProcessConfig,
    child: EndpointChild,
    cleanup_child: Arc<std::sync::Mutex<ChildCleanup>>,
    connection: Option<Connection>,
    directory: Arc<OwnedDirectory>,
    budget: Budget,
    api: NegotiatedApi,
    request: Option<RequestState>,
    next_request: Option<u64>,
    terminal: bool,
    terminal_failure: Option<ProposerTerminalFailure>,
    shutdown_result: Option<Result<(), ProposerCleanupError>>,
    cleanup_error: Option<ProposerCleanupError>,
    restart_after_cancel: bool,
}

impl GenericProcessProposer {
    /// Complete process startup and capability negotiation before the controller
    /// constructs its first immutable request. Config construction is process-free.
    pub async fn start(
        config: GenericProcessConfig,
        permitted: &[&str],
        cancellation: &CancellationToken,
    ) -> io::Result<Self> {
        if !config.executable.is_absolute()
            || config.startup_timeout.is_zero()
            || config.shutdown_timeout.is_zero()
            || config.fallback_timeout.is_zero()
        {
            return Err(io::Error::other(
                "invalid generic proposer launch configuration",
            ));
        }
        if cancellation.should_stop() {
            return Err(startup_error(GenericProcessStartupError::Cancelled));
        }
        let (directory, token) = scratch(&config.scratch_parent)?;
        let budget = Budget::new(config.traffic_limits);
        Self::start_in_directory(
            config,
            directory,
            token,
            budget,
            permitted,
            cancellation,
            None,
        )
        .await
    }

    async fn start_in_directory(
        config: GenericProcessConfig,
        directory: Arc<OwnedDirectory>,
        token: String,
        budget: Budget,
        permitted: &[&str],
        cancellation: &CancellationToken,
        cleanup_child: Option<Arc<std::sync::Mutex<ChildCleanup>>>,
    ) -> io::Result<Self> {
        if cancellation.should_stop() {
            return Err(startup_error(GenericProcessStartupError::Cancelled));
        }
        let path = directory.0.join("api.sock");
        let listener = UnixListener::bind(&path)?;
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o600))?;
        let mut command = Command::new(&config.executable);
        command
            .args(&config.arguments)
            .current_dir(&directory.0)
            .env(SOCKET_ENV, &path)
            .env(TOKEN_ENV, &token);
        let child = EndpointChild::start(command, Arc::clone(&directory));
        let cleanup_child =
            cleanup_child.unwrap_or_else(|| Arc::new(std::sync::Mutex::new(child.cleanup())));
        *cleanup_child.lock().unwrap_or_else(|p| p.into_inner()) = child.cleanup();
        let negotiation = async {
            let (mut stream, _) = listener.accept().await?;
            let hello = read_packet(&mut stream, &token, 0, &budget).await?;
            let Operation::Hello { capabilities } = hello.frame.operation else {
                return Err(io::Error::other("proposer handshake requires hello"));
            };
            let api = capabilities
                .negotiate(permitted)
                .map_err(io::Error::other)?;
            let ready = Frame::new(
                token.clone(),
                0,
                None,
                Operation::Ready { api: api.clone() },
            );
            write_packet(&mut stream, &ready, &[], &budget, false).await?;
            Ok::<_, io::Error>((stream, api))
        };
        let result = tokio::select! {
            biased;
            _ = cancellation.cancelled() => Err(startup_error(GenericProcessStartupError::Cancelled)),
            result = tokio::time::timeout(config.startup_timeout, negotiation) =>
                result.unwrap_or_else(|_| Err(startup_error(GenericProcessStartupError::TimedOut))),
            _ = wait_for_exit(&child) => Err(io::Error::other("proposer exited during startup")),
        };
        let (stream, api) = match result {
            Ok(value) => value,
            Err(error) => {
                child.stop();
                match child.join(config.fallback_timeout).await {
                    Ok(exit) if exit.cleaned => {}
                    Ok(_) => {
                        return Err(startup_cleanup_error(ProposerCleanupError::Failed, &budget));
                    }
                    Err(error) => {
                        return Err(startup_cleanup_error(error, &budget));
                    }
                }
                return Err(if budget.failure().is_some() {
                    startup_error(GenericProcessStartupError::ResourceExhausted)
                } else {
                    error
                });
            }
        };
        Ok(Self {
            connection: Some(Connection::new(stream, token, budget.clone())),
            config,
            child,
            cleanup_child,
            directory,
            budget,
            api,
            request: None,
            next_request: Some(1),
            terminal: false,
            terminal_failure: None,
            shutdown_result: None,
            cleanup_error: None,
            restart_after_cancel: false,
        })
    }

    async fn restart_cancelled_endpoint(
        &mut self,
        cancellation: &AgentSourceCancellation,
    ) -> io::Result<()> {
        // Only a completely joined cancellation fallback may be restarted.
        // Reuse the monitored root, but never the old socket/token/connection.
        if self.shutdown_result != Some(Ok(()))
            || self.connection.is_some()
            || self.request.is_some()
        {
            return Err(io::Error::other(
                "cancelled proposer endpoint was not joined",
            ));
        }
        if cancellation.is_cancelled() {
            return Err(io::Error::new(
                io::ErrorKind::Interrupted,
                RequestWriteCancelled,
            ));
        }
        match std::fs::remove_file(self.directory.0.join("api.sock")) {
            Ok(()) => {}
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => return Err(error),
        }
        let permitted = self
            .api
            .operations
            .iter()
            .map(String::as_str)
            .collect::<Vec<_>>();
        let mut replacement = Self::start_in_directory(
            self.config.clone(),
            Arc::clone(&self.directory),
            fresh_token()?,
            self.budget.clone(),
            &permitted,
            cancellation.token(),
            Some(Arc::clone(&self.cleanup_child)),
        )
        .await?;
        if replacement.api != self.api {
            let cleanup = replacement.fallback(Ok(())).await;
            if let Err(error) = cleanup {
                return Err(startup_cleanup_error(error, &self.budget));
            }
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "restarted proposer changed negotiated capabilities",
            ));
        }
        *self = replacement;
        Ok(())
    }

    pub fn cleanup_handle(&self) -> GenericProcessCleanup {
        GenericProcessCleanup {
            child: Arc::clone(&self.cleanup_child),
            timeout: self.config.fallback_timeout,
        }
    }
    pub fn api_usage(&self) -> ApiTrafficUsage {
        self.budget.usage()
    }
    pub fn resource_status(&self) -> GenericProcessResourceStatus {
        GenericProcessResourceStatus {
            budget: self.budget.clone(),
        }
    }
    pub fn scratch_directory(&self) -> &std::path::Path {
        &self.directory.0
    }
    pub fn scratch_lease(&self) -> GenericProcessScratchLease {
        GenericProcessScratchLease {
            directory: Arc::clone(&self.directory),
        }
    }

    async fn run_request(
        &mut self,
        push: &AgentPush,
        tools: &dyn AgentToolSurface,
        response: &mut AgentResponseWriter,
        cancellation: AgentSourceCancellation,
    ) -> AgentSourceOutcome {
        if self.restart_after_cancel
            && let Err(error) = self.restart_cancelled_endpoint(&cancellation).await
        {
            let startup = error
                .get_ref()
                .and_then(|cause| cause.downcast_ref::<GenericProcessStartupError>());
            if let Some(
                GenericProcessStartupError::CleanupFailed(error)
                | GenericProcessStartupError::ResourceExhaustedCleanupFailed(error),
            ) = startup
            {
                self.cleanup_error = Some(*error);
                self.shutdown_result = Some(Err(*error));
            } else if !is_cancelled_write(&error)
                && startup != Some(&GenericProcessStartupError::Cancelled)
                && self.budget.failure().is_none()
            {
                self.terminal_failure = Some(ProposerTerminalFailure::EndpointFailure);
                self.restart_after_cancel = false;
            }
            response.discard_for_resource_failure();
            return AgentSourceOutcome::TransportFailure;
        }
        if self.terminal {
            response.discard_for_resource_failure();
            return AgentSourceOutcome::TransportFailure;
        }
        if self.request.is_some() || self.child.finished() || push.negotiated_api() != &self.api {
            self.terminal = true;
            self.terminal_failure = Some(ProposerTerminalFailure::EndpointFailure);
            response.discard_for_resource_failure();
            return AgentSourceOutcome::TransportFailure;
        }
        let Some(id) = self.next_request else {
            self.terminal = true;
            self.terminal_failure = Some(ProposerTerminalFailure::EndpointFailure);
            return AgentSourceOutcome::TransportFailure;
        };
        self.next_request = id.checked_add(1);
        self.request = Some(RequestState {
            id,
            complete: false,
            joined: false,
            cancellation: cancellation.token().clone(),
        });
        let mut queries: Vec<PendingQuery<'_>> = Vec::new();
        let result = self
            .exchange(push, tools, response, &cancellation, id, &mut queries)
            .await;
        if let Err(error) = &result {
            self.terminal = true;
            self.restart_after_cancel = is_cancelled_write(error);
            if !self.restart_after_cancel && self.budget.failure().is_none() {
                self.terminal_failure.get_or_insert(match error.kind() {
                    io::ErrorKind::InvalidData => ProposerTerminalFailure::ProtocolViolation,
                    io::ErrorKind::UnexpectedEof
                    | io::ErrorKind::BrokenPipe
                    | io::ErrorKind::ConnectionReset => ProposerTerminalFailure::EndpointExited,
                    _ => ProposerTerminalFailure::EndpointFailure,
                });
            }
        }
        let externally_cancelled = cancellation.is_cancelled();
        let completed = result.is_ok();
        cancellation.token().cancel();
        let joined = tokio::time::timeout(self.config.fallback_timeout, async {
            while !queries.is_empty() {
                let _ = next_query(&mut queries).await;
            }
        })
        .await
        .is_ok();
        if !joined {
            self.cleanup_error = Some(ProposerCleanupError::TimedOut);
            self.terminal = true;
        }
        let outcome = match result {
            Ok(outcome) if joined && self.budget.failure().is_none() && !externally_cancelled => {
                outcome
            }
            _ => {
                response.discard_for_resource_failure();
                if self.budget.failure().is_some() {
                    self.terminal = true;
                    AgentSourceOutcome::SourceExhausted
                } else {
                    AgentSourceOutcome::TransportFailure
                }
            }
        };
        if let Some(request) = &mut self.request {
            request.complete = joined && completed;
            request.joined = joined;
        }
        outcome
    }

    async fn exchange<'a>(
        &mut self,
        push: &AgentPush,
        tools: &'a dyn AgentToolSurface,
        response: &mut AgentResponseWriter,
        cancellation: &AgentSourceCancellation,
        id: u64,
        queries: &mut Vec<PendingQuery<'a>>,
    ) -> io::Result<AgentSourceOutcome> {
        let observation = crate::framing::bounded_json(push.observation(), MAX_PACKET_BYTES)?;
        let example = crate::framing::bounded_json(
            &push
                .candidate_clauses_example()
                .ok_or_else(|| io::Error::other("request lacks proposal example"))?,
            MAX_PACKET_BYTES,
        )?;
        let remaining = push
            .remaining_request_budget_ns()?
            .map(|value| value.to_string());
        let connection = self
            .connection
            .as_mut()
            .ok_or_else(|| io::Error::other("proposer connection absent"))?;
        connection.request_scope.store(id, Ordering::Release);
        connection.phase.store(REQUEST, Ordering::Release);
        let request_attachments = [observation.as_slice(), example.as_slice()];
        let sent = tokio::select! {
            biased;
            result = request_write(connection.send(Some(id), Operation::Request {
                observation_bytes: observation.len() as u32, response_example_bytes: example.len() as u32,
                remaining_request_budget_ns: remaining,
            }, &request_attachments, &self.budget, false), cancellation) => result,
            _ = wait_for_exit(&self.child) => Err(io::Error::new(io::ErrorKind::UnexpectedEof, "proposer exited during request write")),
        };
        sent?;
        let mut next_query_id = Some(1);
        let mut submitted = false;
        let mut receipt = false;
        loop {
            enum Event {
                Packet(io::Result<Packet>),
                Query(u64, AgentToolResponse),
                Cancelled,
                Exited,
            }
            let event = tokio::select! {
                biased;
                _ = cancellation.cancelled() => Event::Cancelled,
                _ = wait_for_exit(&self.child) => Event::Exited,
                packet = connection.receive() => Event::Packet(packet),
                (id, result) = next_query(queries), if !queries.is_empty() => Event::Query(id, result),
            };
            match event {
                Event::Cancelled => {
                    response.discard_for_resource_failure();
                    let cancelled = async {
                        connection
                            .send(
                                Some(id),
                                Operation::Cancel {
                                    reason: cancellation.reason(),
                                },
                                &[],
                                &self.budget,
                                self.budget.failure().is_some(),
                            )
                            .await?;
                        {
                            let packet = connection.receive().await?;
                            if packet.frame.request_id == Some(id)
                                && matches!(
                                    packet.frame.operation,
                                    Operation::Complete {
                                        outcome: RequestOutcome::Failure
                                    }
                                )
                            {
                                return Ok::<_, io::Error>(());
                            }
                            Err(io::Error::new(
                                io::ErrorKind::InvalidData,
                                "late proposer traffic after cancellation",
                            ))
                        }
                    };
                    tokio::time::timeout(self.config.shutdown_timeout, cancelled)
                        .await
                        .map_err(|_| {
                            io::Error::new(
                                io::ErrorKind::TimedOut,
                                "proposer cancellation timed out",
                            )
                        })??;
                    connection.phase.store(IDLE, Ordering::Release);
                    return Ok(AgentSourceOutcome::TransportFailure);
                }
                Event::Exited => {
                    return Err(io::Error::new(
                        io::ErrorKind::UnexpectedEof,
                        "proposer exited before request completion",
                    ));
                }
                Event::Query(query_id, result) => {
                    let result = crate::framing::bounded_json(&result, MAX_PACKET_BYTES)?;
                    let query_attachments = [result.as_slice()];
                    request_write(
                        connection.send(
                            Some(id),
                            Operation::QueryResult {
                                query_id,
                                result_bytes: result.len() as u32,
                            },
                            &query_attachments,
                            &self.budget,
                            false,
                        ),
                        cancellation,
                    )
                    .await?;
                }
                Event::Packet(packet) => {
                    let Packet { frame, attachments } = packet?;
                    if frame.request_id != Some(id) {
                        return Err(io::Error::new(
                            io::ErrorKind::InvalidData,
                            "wrong proposer request scope",
                        ));
                    }
                    match frame.operation {
                        Operation::Query { query_id, name, .. } => {
                            if submitted || Some(query_id) != next_query_id {
                                return Err(io::Error::new(
                                    io::ErrorKind::InvalidData,
                                    "invalid proposer query phase or identity",
                                ));
                            }
                            next_query_id = query_id.checked_add(1);
                            let args = attachments
                                .into_iter()
                                .next()
                                .ok_or_else(|| io::Error::other("query arguments absent"))?;
                            let allowed = self.api.operations.contains(&name);
                            let revision = push.observation().feedback.state_revision;
                            queries.push(Box::pin(async move {
                                let result = if !allowed {
                                    AgentToolResponse::err(
                                        &name,
                                        revision,
                                        "tool_disabled",
                                        "Query was not negotiated for this endpoint.",
                                    )
                                } else if let Ok(value) =
                                    decode_strict_json(&args, Some(MAX_PACKET_BYTES))
                                {
                                    tools.call(&name, value).await
                                } else {
                                    AgentToolResponse::err(
                                        &name,
                                        revision,
                                        "invalid_arguments",
                                        "Query arguments are not strict JSON.",
                                    )
                                };
                                (query_id, result)
                            }));
                        }
                        Operation::Submit { .. } => {
                            let first = !submitted;
                            submitted = true;
                            let payload = attachments
                                .into_iter()
                                .next()
                                .ok_or_else(|| io::Error::other("proposal bytes absent"))?;
                            let reply = if !first {
                                Operation::Rejected {
                                    code: TransportRejection::DuplicateSubmission,
                                }
                            } else {
                                // The complete legal packet has arrived. The controller's
                                // reply_bytes cap is a separate admission/correction rule:
                                // preserve its bounded bytes and oversized flag unchanged.
                                let _ = response.write_chunk(&payload);
                                Operation::Submitted {}
                            };
                            let accepted = matches!(reply, Operation::Submitted {});
                            request_write(
                                connection.send(Some(id), reply, &[], &self.budget, false),
                                cancellation,
                            )
                            .await?;
                            if accepted {
                                receipt = true;
                            }
                        }
                        Operation::Complete { outcome } => {
                            if !queries.is_empty() && outcome != RequestOutcome::Failure {
                                return Err(io::Error::new(
                                    io::ErrorKind::InvalidData,
                                    "proposer completed with outstanding queries",
                                ));
                            }
                            let outcome = match outcome {
                                RequestOutcome::Response if receipt => AgentSourceOutcome::Response,
                                RequestOutcome::NoResponse if !submitted => {
                                    AgentSourceOutcome::NoResponse
                                }
                                RequestOutcome::SourceExhausted if !submitted => {
                                    AgentSourceOutcome::SourceExhausted
                                }
                                RequestOutcome::Failure => {
                                    response.discard_for_resource_failure();
                                    AgentSourceOutcome::TransportFailure
                                }
                                _ => {
                                    return Err(io::Error::new(
                                        io::ErrorKind::InvalidData,
                                        "proposer completion disagrees with submission receipt",
                                    ));
                                }
                            };
                            connection.phase.store(IDLE, Ordering::Release);
                            return Ok(outcome);
                        }
                        _ => {
                            return Err(io::Error::new(
                                io::ErrorKind::InvalidData,
                                "operation is not valid during proposer request",
                            ));
                        }
                    }
                }
            }
        }
    }

    // A failed transport can still have successful cleanup. This path never
    // turns a candidate response into success; the original source outcome and
    // resource classification remain authoritative after all owned work joins.
    async fn fallback(
        &mut self,
        original: Result<(), ProposerCleanupError>,
    ) -> Result<(), ProposerCleanupError> {
        self.terminal = true;
        if let Some(request) = &self.request {
            request.cancellation.cancel();
        }
        self.child.stop();
        let mut result = original;
        match self.child.join(self.config.fallback_timeout).await {
            Ok(exit) if exit.cleaned => {}
            Ok(_) => result = Err(ProposerCleanupError::Failed),
            Err(error) => result = Err(error),
        }
        if let Some(connection) = self.connection.as_mut()
            && let Err(error) = connection.stop_reader(self.config.fallback_timeout).await
        {
            result = Err(error);
        }
        self.connection = None;
        self.request = None;
        self.shutdown_result = Some(result);
        result
    }

    async fn quiesce(&mut self) -> Result<(), ProposerCleanupError> {
        if let Some(result) = self.shutdown_result {
            return result;
        }
        if let Some(error) = self.cleanup_error {
            return self.fallback(Err(error)).await;
        }
        let Some(request) = self.request.as_ref() else {
            return Ok(());
        };
        request.cancellation.cancel();
        if !request.joined {
            return self.fallback(Err(ProposerCleanupError::Failed)).await;
        }
        if !request.complete {
            return self.fallback(Ok(())).await;
        }
        let id = request.id;
        let Some(connection) = self.connection.as_mut() else {
            self.terminal_failure
                .get_or_insert(ProposerTerminalFailure::EndpointFailure);
            return self.fallback(Ok(())).await;
        };
        if !matches!(
            connection.incoming.try_recv(),
            Err(mpsc::error::TryRecvError::Empty)
        ) || self.child.finished()
        {
            self.terminal_failure
                .get_or_insert(ProposerTerminalFailure::ProtocolViolation);
            return self.fallback(Ok(())).await;
        }
        let result = tokio::time::timeout(
            self.config.shutdown_timeout,
            connection.send(
                Some(id),
                Operation::RequestClosed {},
                &[],
                &self.budget,
                self.budget.failure().is_some(),
            ),
        )
        .await
        .map_err(|_| ProposerCleanupError::TimedOut)
        .and_then(|result| result.map_err(|_| ProposerCleanupError::Failed));
        if result.is_err() {
            if self.budget.failure().is_none() {
                self.terminal_failure
                    .get_or_insert(ProposerTerminalFailure::EndpointFailure);
            }
            return self.fallback(Ok(())).await;
        }
        self.request = None;
        result
    }

    async fn stop(&mut self, reason: ShutdownReason) -> Result<(), ProposerCleanupError> {
        self.restart_after_cancel = false;
        if let Some(result) = self.shutdown_result {
            return result;
        }
        self.terminal = true;
        if let Some(request) = &self.request {
            request.cancellation.cancel();
        }
        let mut result = self.quiesce().await;
        if let Some(result) = self.shutdown_result {
            return result;
        }
        if self.terminal_failure.is_some() || self.budget.failure().is_some() {
            return self.fallback(result).await;
        }
        if result.is_ok() && self.connection.is_none() {
            result = Err(ProposerCleanupError::Failed);
        }
        if result.is_ok()
            && let Some(connection) = self.connection.as_mut()
        {
            connection.phase.store(SHUTDOWN, Ordering::Release);
            let exchange = tokio::time::timeout(self.config.shutdown_timeout, async {
                if connection
                    .send(
                        None,
                        Operation::Shutdown { reason },
                        &[],
                        &self.budget,
                        self.budget.failure().is_some(),
                    )
                    .await
                    .is_err()
                {
                    return if self.budget.failure().is_some() {
                        Ok(false)
                    } else {
                        Err(ProposerCleanupError::Failed)
                    };
                }
                let packet = match connection.receive().await {
                    Ok(packet) => packet,
                    Err(_) if self.budget.failure().is_some() => return Ok(false),
                    Err(_) => return Err(ProposerCleanupError::Failed),
                };
                if packet.frame.request_id.is_some()
                    || !matches!(packet.frame.operation, Operation::Closed {})
                {
                    return Err(ProposerCleanupError::Failed);
                }
                Ok(true)
            })
            .await
            .unwrap_or(Err(ProposerCleanupError::TimedOut));
            match exchange {
                Ok(true) => {}
                // A refused lifecycle packet is a latched API resource fault,
                // not a failed process join. Physical fallback still must join.
                Ok(false) => return self.fallback(Ok(())).await,
                Err(error) => result = Err(error),
            }
        }
        if result.is_ok() {
            match self.child.join(self.config.shutdown_timeout).await {
                Ok(exit) if exit.cleaned && exit.successful => {}
                Ok(_) => result = Err(ProposerCleanupError::Failed),
                Err(error) => result = Err(error),
            }
        }
        self.fallback(result).await
    }
}

impl AgentProvider for GenericProcessProposer {
    fn api_capabilities(&self) -> ApiCapabilities {
        ApiCapabilities {
            version: self.api.version.clone(),
            supported_operations: self.api.operations.clone(),
            required_operations: Vec::new(),
        }
    }
    fn terminal_failure(&self) -> Option<ProposerTerminalFailure> {
        self.terminal_failure
    }
    fn resource_failure(&self) -> Option<String> {
        self.budget.failure()
    }
    fn consult<'a>(
        &'a mut self,
        push: &'a AgentPush,
        tools: &'a dyn AgentToolSurface,
        response: &'a mut AgentResponseWriter,
        cancellation: AgentSourceCancellation,
    ) -> AgentSourceFuture<'a> {
        Box::pin(self.run_request(push, tools, response, cancellation))
    }
    fn quiesce_request(&mut self) -> ProposerCleanupFuture<'_> {
        Box::pin(self.quiesce())
    }
    fn shutdown(&mut self, reason: ShutdownReason) -> ProposerCleanupFuture<'_> {
        Box::pin(self.stop(reason))
    }
}

impl Drop for GenericProcessProposer {
    fn drop(&mut self) {
        if let Some(request) = &self.request {
            request.cancellation.cancel();
        }
        self.child.stop();
    }
}

async fn wait_for_exit(child: &EndpointChild) {
    while !child.finished() {
        tokio::time::sleep(Duration::from_millis(10)).await;
    }
}

fn fresh_token() -> io::Result<String> {
    let mut random = [0; 32];
    std::fs::File::open("/dev/urandom")?.read_exact(&mut random)?;
    Ok(random.iter().map(|byte| format!("{byte:02x}")).collect())
}

fn scratch(parent: &std::path::Path) -> io::Result<(Arc<OwnedDirectory>, String)> {
    let parent = parent.canonicalize()?;
    let token = fresh_token()?;
    let path = parent.join(format!(
        "whiel-proposer-{}-{}",
        std::process::id(),
        &token[..12]
    ));
    std::fs::DirBuilder::new().mode(0o700).create(&path)?;
    let directory = Arc::new(OwnedDirectory(path));
    if directory.0.join("api.sock").as_os_str().as_bytes().len() >= 100 {
        return Err(io::Error::other(
            "proposer socket path exceeds platform bound",
        ));
    }
    Ok((directory, token))
}

#[cfg(test)]
#[path = "generic_write_tests.rs"]
mod write_tests;
