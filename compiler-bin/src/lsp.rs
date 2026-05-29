pub mod error;
pub mod event;
pub mod extension;

use std::borrow::BorrowMut;
use std::ops::{ControlFlow, Deref};
use std::path::PathBuf;
use std::sync::Arc;
use std::time::SystemTime;
use std::{env, fs, mem, process};

use analyzer::completion::SuggestionsCache;
use analyzer::symbols::WorkspaceSymbolsCache;
use analyzer::{Files, QueryEngine, prim};
use async_lsp::client_monitor::ClientProcessMonitorLayer;
use async_lsp::concurrency::ConcurrencyLayer;
use async_lsp::lsp_types::notification::Notification;
use async_lsp::lsp_types::request::Request;
use async_lsp::lsp_types::*;
use async_lsp::panic::CatchUnwindLayer;
use async_lsp::router::Router;
use async_lsp::server::LifecycleLayer;
use async_lsp::{ClientSocket, ResponseError};
use globset::{Glob, GlobSetBuilder};
use parking_lot::RwLock;
use path_absolutize::Absolutize;
use tokio::task;
use tower::ServiceBuilder;
use walkdir::WalkDir;

use crate::cli;
use crate::lsp::error::{AnalyzerResultExt, LspError};

pub struct State {
    pub config: Arc<cli::Config>,
    pub client: ClientSocket,

    pub engine: QueryEngine,
    pub files: Arc<RwLock<Files>>,

    pub workspace_symbols_cache: Arc<RwLock<WorkspaceSymbolsCache>>,
    pub suggestions_cache: Arc<RwLock<SuggestionsCache>>,
    pub record_fields_cache: Arc<RwLock<analyzer::completion::RecordFieldsCache>>,

    pub root: Option<PathBuf>,

    /// Newest `spago.lock` mtime observed when the dependency source set was
    /// last loaded. Used to detect that dependencies changed on disk (a
    /// `spago install`/`build`, a branch switch) so the set can be reloaded
    /// mid-session — see [`reload_sources_if_stale`].
    pub loaded_lock_mtime: Option<SystemTime>,
}

impl State {
    fn new(config: Arc<cli::Config>, client: ClientSocket) -> State {
        let mut engine = QueryEngine::default();
        let mut files = Files::default();
        prim::configure(&mut engine, &mut files);

        let files = Arc::new(RwLock::new(files));

        let workspace_symbols_cache = WorkspaceSymbolsCache::default();
        let workspace_symbols_cache = Arc::new(RwLock::new(workspace_symbols_cache));

        let suggestions_cache = SuggestionsCache::default();
        let suggestions_cache = Arc::new(RwLock::new(suggestions_cache));

        let record_fields_cache = analyzer::completion::RecordFieldsCache::default();
        let record_fields_cache = Arc::new(RwLock::new(record_fields_cache));

        let root = None;

        State {
            config,
            client,
            engine,
            files,
            workspace_symbols_cache,
            suggestions_cache,
            record_fields_cache,
            root,
            loaded_lock_mtime: None,
        }
    }

    fn spawn<T>(&self, f: impl FnOnce(StateSnapshot) -> T + Send + 'static) -> task::JoinHandle<T>
    where
        T: Send + 'static,
    {
        let snapshot = StateSnapshot {
            client: self.client.clone(),
            engine: self.engine.snapshot(),
            files: Arc::clone(&self.files),
            workspace_symbols_cache: Arc::clone(&self.workspace_symbols_cache),
            suggestions_cache: Arc::clone(&self.suggestions_cache),
            record_fields_cache: Arc::clone(&self.record_fields_cache),
        };
        task::spawn_blocking(move || f(snapshot))
    }

    fn invalidate_workspace_symbols(&self) {
        let mut cache = self.workspace_symbols_cache.write();
        mem::take(&mut *cache);
    }

    fn invalidate_suggestions_cache(&self) {
        let mut cache = self.suggestions_cache.write();
        mem::take(&mut *cache);
    }
}

struct StateSnapshot {
    client: ClientSocket,
    engine: QueryEngine,
    files: Arc<RwLock<Files>>,
    workspace_symbols_cache: Arc<RwLock<WorkspaceSymbolsCache>>,
    suggestions_cache: Arc<RwLock<SuggestionsCache>>,
    record_fields_cache: Arc<RwLock<analyzer::completion::RecordFieldsCache>>,
}

impl StateSnapshot {
    fn files(&self) -> impl Deref<Target = Files> {
        self.files.read()
    }
}

fn initialize(
    state: &mut State,
    p: extension::CustomInitializeParams,
) -> impl Future<Output = Result<InitializeResult, ResponseError>> + use<> {
    state.root = p
        .initialize_params
        .workspace_folders
        .and_then(|folders| {
            let folder = folders.first()?;
            folder.uri.to_file_path().ok()
        })
        .or_else(|| env::current_dir().ok());
    async move {
        Ok(InitializeResult {
            server_info: None,
            capabilities: ServerCapabilities {
                completion_provider: Some(CompletionOptions {
                    resolve_provider: Some(true),
                    trigger_characters: Some(vec![".".to_string(), " ".to_string()]),
                    all_commit_characters: None,
                    work_done_progress_options: WorkDoneProgressOptions {
                        work_done_progress: None,
                    },
                    completion_item: Some(CompletionOptionsCompletionItem {
                        label_details_support: Some(true),
                    }),
                }),
                definition_provider: Some(OneOf::Left(true)),
                hover_provider: Some(HoverProviderCapability::Simple(true)),
                references_provider: Some(OneOf::Left(true)),
                signature_help_provider: Some(SignatureHelpOptions {
                    trigger_characters: Some(vec![" ".to_string()]),
                    retrigger_characters: None,
                    work_done_progress_options: WorkDoneProgressOptions {
                        work_done_progress: None,
                    },
                }),
                workspace_symbol_provider: Some(OneOf::Left(true)),
                code_action_provider: Some(CodeActionProviderCapability::Simple(true)),
                rename_provider: Some(OneOf::Left(true)),
                text_document_sync: Some(TextDocumentSyncCapability::Kind(
                    TextDocumentSyncKind::FULL,
                )),
                ..ServerCapabilities::default()
            },
        })
    }
}

fn initialized(state: &mut State, _: InitializedParams) -> Result<(), LspError> {
    let _span = tracing::info_span!("initialization").entered();
    let config = Arc::clone(&state.config);
    if let Some(command) = config.source_command.as_deref() {
        initialized_manual(state, command)
    } else {
        initialized_spago(state)
    }
}

fn initialized_manual(state: &mut State, command: &str) -> Result<(), LspError> {
    let root = state.root.as_ref().ok_or(LspError::MissingRoot)?;

    tracing::info!("Using '{}'", command);

    let mut parts = command.split(" ");
    let program = parts.next().ok_or(LspError::InvalidSourceCommand)?;

    let mut command = process::Command::new(program);
    command.args(parts);

    let output = command.output()?;
    let output = str::from_utf8(&output.stdout)?;

    let mut files = vec![];
    let mut globs = GlobSetBuilder::new();

    for line in output.lines() {
        let path = root.join(line);
        if let Ok(path) = path.absolutize()
            && let Some(path) = path.to_str()
            && let Ok(glob) = Glob::new(path)
        {
            globs.add(glob);
        } else {
            files.push(path);
        }
    }

    let globs = globs.build()?;

    tracing::info!("Found {} file literals", files.len());
    tracing::info!("Found {} glob patterns", globs.len());

    let files_from_glob = WalkDir::new(root).into_iter().filter_map(move |entry| {
        let entry = entry.ok()?;
        let path = entry.path();
        if globs.matches(path).is_empty() { None } else { Some(path.to_path_buf()) }
    });

    files.extend(files_from_glob);
    load_files(state, &files, false)?;

    Ok(())
}

fn initialized_spago(state: &mut State) -> Result<(), LspError> {
    let root = state.root.as_ref().ok_or(LspError::MissingRoot)?.clone();

    tracing::info!("Using 'spago.lock'");

    let lockfiles = find_spago_lockfiles(&root);
    tracing::info!("Found {} spago.lock files", lockfiles.len());

    for lockfile_dir in &lockfiles {
        let spago_action = check_spago_status(lockfile_dir);
        if let Some(action) = spago_action {
            state.client.emit(event::SpagoAction(action, lockfile_dir.clone()))?;
        }
    }

    load_spago_sources(state, &lockfiles, false)
}

/// Read every lockfile's source globs and load the resulting files into the
/// engine, then record the lockfiles' newest mtime so [`reload_sources_if_stale`]
/// can tell when the set has gone out of date. Idempotent: re-running it picks
/// up packages that have since appeared on disk. Pass `additive` to skip files
/// already loaded (a reload), leaving open editor buffers untouched.
fn load_spago_sources(
    state: &mut State,
    lockfiles: &[PathBuf],
    additive: bool,
) -> Result<(), LspError> {
    let mut all_files = vec![];
    for lockfile_dir in lockfiles {
        match spago::source_files(lockfile_dir) {
            Ok(files) => all_files.extend(files),
            Err(e) => tracing::warn!("Failed to read {}: {e}", lockfile_dir.display()),
        }
    }

    all_files.sort();
    all_files.dedup();
    load_files(state, &all_files, additive)?;

    state.loaded_lock_mtime = max_lockfile_mtime(lockfiles);

    Ok(())
}

/// Newest modification time across the given lockfile directories' `spago.lock`
/// files, or `None` when none can be stat'd.
fn max_lockfile_mtime(lockfiles: &[PathBuf]) -> Option<SystemTime> {
    lockfiles
        .iter()
        .filter_map(|dir| dir.join("spago.lock").metadata().and_then(|m| m.modified()).ok())
        .max()
}

/// Reload the source set when a `spago.lock` has changed since it was last
/// loaded. Without this the set is frozen at `initialized` for the life of the
/// session, so an install/build that rewrites the lockfile (or a session that
/// started while the lockfile was mid-write) leaves modules permanently
/// unresolvable — there is no "reload the window" in a headless client.
///
/// Checked on `did_open` and `did_save` — between them every client (editor or
/// headless MCP) hits one before reading diagnostics, even when it keeps the
/// document open across requests, so resolution heals on the next request. The
/// reload is additive (see [`load_files`]), so it never clobbers an open
/// buffer. No-op under `--source-command`, where the caller owns the set.
fn reload_sources_if_stale(state: &mut State) -> Result<(), LspError> {
    if state.config.source_command.is_some() {
        return Ok(());
    }

    let Some(root) = state.root.clone() else {
        return Ok(());
    };

    let lockfiles = find_spago_lockfiles(&root);
    let current = max_lockfile_mtime(&lockfiles);

    let stale = match (current, state.loaded_lock_mtime) {
        (Some(now), Some(loaded)) => now > loaded,
        (Some(_), None) => true,
        _ => false,
    };

    if stale {
        tracing::info!("spago.lock changed since last load; reloading sources");
        load_spago_sources(state, &lockfiles, true)?;
    }

    Ok(())
}

fn find_spago_lockfiles(root: &std::path::Path) -> Vec<PathBuf> {
    let mut result = vec![];

    if root.join("spago.lock").exists() {
        result.push(root.to_path_buf());
    }

    if let Ok(entries) = fs::read_dir(root) {
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() && path.join("spago.lock").exists() {
                result.push(path);
            }
        }
    }

    result
}

fn check_spago_status(root: &std::path::Path) -> Option<SpagoActionKind> {
    let spago_lock = root.join("spago.lock");
    let spago_packages = root.join(".spago").join("p");

    if is_lockfile_stale(root, &spago_lock) {
        return Some(SpagoActionKind::Install);
    }

    if !spago_packages.exists() {
        return Some(SpagoActionKind::Install);
    }

    None
}

#[derive(Debug, Clone)]
pub enum SpagoActionKind {
    Install,
}

fn is_lockfile_stale(root: &std::path::Path, spago_lock: &std::path::Path) -> bool {
    let lock_modified = spago_lock.metadata().and_then(|m| m.modified()).ok();

    let yamls = std::iter::once(root.join("spago.yaml")).chain(
        fs::read_dir(root)
            .into_iter()
            .flatten()
            .filter_map(|e| e.ok())
            .filter(|e| e.path().is_dir())
            .map(|e| e.path().join("spago.yaml"))
            .filter(|p| p.exists()),
    );

    for yaml in yamls {
        let yaml_modified = yaml.metadata().and_then(|m| m.modified()).ok();
        if let Some((yaml_t, lock_t)) = yaml_modified.zip(lock_modified) {
            if yaml_t > lock_t {
                tracing::info!("{} is newer than spago.lock", yaml.display());
                return true;
            }
        }
    }

    false
}

pub fn run_spago(root: &std::path::Path, command: &str) -> bool {
    let result = process::Command::new("spago").arg(command).current_dir(root).output();

    match result {
        Ok(output) if output.status.success() => {
            tracing::info!("spago {command} succeeded");
            true
        }
        Ok(output) => {
            let stderr = String::from_utf8_lossy(&output.stderr);
            tracing::warn!("spago {command} failed: {stderr}");
            false
        }
        Err(e) => {
            tracing::warn!("Failed to run spago {command}: {e}");
            false
        }
    }
}

/// Load the given files into the engine. When `additive`, files the engine
/// already knows are skipped rather than re-read — so a reload can add modules
/// that have appeared without overwriting content the editor is holding for an
/// open (possibly unsaved) document.
fn load_files(state: &mut State, files: &[PathBuf], additive: bool) -> Result<(), LspError> {
    tracing::info!("Loading {} files (additive: {additive}).", files.len());

    let mut loaded = 0;
    for file in files {
        let url = url::Url::from_file_path(file).map_err(|_| {
            let file = PathBuf::clone(file);
            LspError::PathParseFail(file)
        })?;

        let uri = url.to_string();

        if additive && state.files.read().id(uri.as_str()).is_some() {
            continue;
        }

        let text = fs::read_to_string(file)?;
        on_change(state, &uri, &text)?;
        loaded += 1;
    }

    tracing::info!("Loaded {loaded} files.");

    Ok(())
}

fn definition(
    snapshot: StateSnapshot,
    p: GotoDefinitionParams,
) -> Result<Option<GotoDefinitionResponse>, LspError> {
    let _span = tracing::info_span!("definition").entered();
    let uri = p.text_document_position_params.text_document.uri;
    let position = p.text_document_position_params.position;
    analyzer::definition::implementation(&snapshot.engine, &snapshot.files(), uri, position)
        .on_non_fatal(None)
}

fn hover(snapshot: StateSnapshot, p: HoverParams) -> Result<Option<Hover>, LspError> {
    let _span = tracing::info_span!("hover").entered();
    let uri = p.text_document_position_params.text_document.uri;
    let position = p.text_document_position_params.position;
    analyzer::hover::implementation(&snapshot.engine, &snapshot.files(), uri, position)
        .on_non_fatal(None)
}

fn completion(
    snapshot: StateSnapshot,
    p: CompletionParams,
) -> Result<Option<CompletionResponse>, LspError> {
    let _span = tracing::info_span!("completion").entered();
    let uri = p.text_document_position.text_document.uri;
    let position = p.text_document_position.position;
    let trigger_character = p.context.as_ref().and_then(|c| c.trigger_character.clone());

    let mut cache = snapshot.suggestions_cache.write();
    let mut record_cache = snapshot.record_fields_cache.write();

    analyzer::completion::implementation(
        &snapshot.engine,
        &snapshot.files(),
        &mut cache,
        &mut record_cache,
        uri,
        position,
        trigger_character.as_deref(),
    )
    .on_non_fatal(None)
}

fn resolve_completion_item(
    snapshot: StateSnapshot,
    item: CompletionItem,
) -> Result<CompletionItem, LspError> {
    let _span = tracing::info_span!("resolve_completion_item").entered();
    analyzer::completion::resolve::implementation(&snapshot.engine, item)
        .or_else(|(error, item)| Err(error).on_non_fatal(item))
}

fn references(
    snapshot: StateSnapshot,
    p: ReferenceParams,
) -> Result<Option<Vec<Location>>, LspError> {
    let _span = tracing::info_span!("references").entered();
    let uri = p.text_document_position.text_document.uri;
    let position = p.text_document_position.position;
    analyzer::references::implementation(&snapshot.engine, &snapshot.files(), uri, position)
        .on_non_fatal(None)
}

fn signature_help(
    snapshot: StateSnapshot,
    p: SignatureHelpParams,
) -> Result<Option<SignatureHelp>, LspError> {
    let _span = tracing::info_span!("signature_help").entered();
    let uri = p.text_document_position_params.text_document.uri;
    let position = p.text_document_position_params.position;
    analyzer::signature_help::implementation(&snapshot.engine, &snapshot.files(), uri, position)
        .on_non_fatal(None)
}

fn code_action(
    snapshot: StateSnapshot,
    p: CodeActionParams,
) -> Result<Option<CodeActionResponse>, LspError> {
    let _span = tracing::info_span!("code_action").entered();
    let uri = p.text_document.uri;
    let range = p.range;
    let diagnostics = &p.context.diagnostics;
    analyzer::code_action::implementation(
        &snapshot.engine,
        &snapshot.files(),
        uri,
        range,
        diagnostics,
    )
    .on_non_fatal(None)
}

fn rename(snapshot: StateSnapshot, p: RenameParams) -> Result<Option<WorkspaceEdit>, LspError> {
    let _span = tracing::info_span!("rename").entered();
    let uri = p.text_document_position.text_document.uri;
    let position = p.text_document_position.position;
    let new_name = p.new_name;
    analyzer::rename::implementation(&snapshot.engine, &snapshot.files(), uri, position, new_name)
        .on_non_fatal(None)
}

fn workspace_symbols(
    snapshot: StateSnapshot,
    p: WorkspaceSymbolParams,
) -> Result<Option<WorkspaceSymbolResponse>, LspError> {
    let _span = tracing::info_span!("workspace_symbols").entered();

    let mut cache = snapshot.workspace_symbols_cache.write();
    analyzer::symbols::workspace(&snapshot.engine, &snapshot.files(), &mut cache, &p.query)
        .on_non_fatal(None)
}

fn did_open(state: &mut State, p: DidOpenTextDocumentParams) -> Result<(), LspError> {
    reload_sources_if_stale(state)?;
    event::emit_collect_diagnostics(state, p.text_document.uri)?;
    Ok(())
}

fn did_change(state: &mut State, p: DidChangeTextDocumentParams) -> Result<(), LspError> {
    let uri = p.text_document.uri.as_str();

    for content_change in &p.content_changes {
        let text = content_change.text.as_str();
        on_change(state, uri, text)?
    }

    state.invalidate_workspace_symbols();
    event::emit_collect_diagnostics(state, p.text_document.uri)?;

    Ok(())
}

fn did_save(state: &mut State, p: DidSaveTextDocumentParams) -> Result<(), LspError> {
    state.invalidate_suggestions_cache();
    reload_sources_if_stale(state)?;
    event::emit_collect_diagnostics(state, p.text_document.uri)?;
    Ok(())
}

fn on_change(state: &mut State, uri: &str, content: &str) -> Result<(), LspError> {
    // Cancel in-flight queries so that threads holding a read lock
    // over `files` are terminated quickly, compared to having to
    // wait for expensive LSP requests to complete successfully.
    state.engine.request_cancel();

    let mut files = state.files.write();
    let id = files.insert(uri, content);

    state.engine.set_content(id, content);

    let (parsed, _) = state.engine.parsed(id)?;

    if let Some(name) = parsed.module_name() {
        state.engine.set_module_file(&name, id);
    }

    Ok(())
}

trait RequestExtension: BorrowMut<Router<State>> {
    fn request_snapshot<R: Request>(
        &mut self,
        action: impl Fn(StateSnapshot, R::Params) -> Result<R::Result, LspError> + Send + Copy + 'static,
    ) -> &mut Self {
        self.borrow_mut().request::<R, _>(move |state, parameters| {
            let task = state.spawn(move |snapshot| action(snapshot, parameters));
            async move {
                task.await.map_err(LspError::JoinError).flatten().map_err(|error| {
                    error.emit_trace();
                    let code = error.code();
                    let message = error.message();
                    ResponseError::new(code, message)
                })
            }
        });
        self
    }

    fn notification_ext<N: Notification>(
        &mut self,
        action: impl Fn(&mut State, N::Params) -> Result<(), LspError> + Send + Copy + 'static,
    ) -> &mut Self {
        let this: &mut Router<State> = self.borrow_mut();
        this.notification::<N>(move |state, parameters| {
            let _ = action(state, parameters).inspect_err(|error| error.emit_trace());
            ControlFlow::Continue(())
        });
        self
    }
    fn event_ext<E>(
        &mut self,
        action: impl Fn(&mut State, E) -> Result<(), LspError> + Send + Copy + 'static,
    ) -> &mut Self
    where
        E: Send + 'static,
    {
        let this: &mut Router<State> = self.borrow_mut();
        this.event::<E>(move |state, event| {
            let _ = action(state, event).inspect_err(|error| error.emit_trace());
            ControlFlow::Continue(())
        });
        self
    }
}

impl RequestExtension for Router<State> {}

pub async fn start(config: Arc<cli::Config>) {
    let (server, _) = async_lsp::MainLoop::new_server(move |client| {
        let mut router: Router<State, ResponseError> =
            Router::new(State::new(config, client.clone()));

        router
            .request::<extension::CustomInitialize, _>(initialize)
            .request_snapshot::<request::GotoDefinition>(definition)
            .request_snapshot::<request::HoverRequest>(hover)
            .request_snapshot::<request::Completion>(completion)
            .request_snapshot::<request::ResolveCompletionItem>(resolve_completion_item)
            .request_snapshot::<request::References>(references)
            .request_snapshot::<request::SignatureHelpRequest>(signature_help)
            .request_snapshot::<request::WorkspaceSymbolRequest>(workspace_symbols)
            .request_snapshot::<request::CodeActionRequest>(code_action)
            .request_snapshot::<request::Rename>(rename)
            .notification_ext::<notification::Initialized>(initialized)
            .notification_ext::<notification::DidOpenTextDocument>(did_open)
            .notification_ext::<notification::DidSaveTextDocument>(did_save)
            .notification_ext::<notification::DidCloseTextDocument>(|_, _| Ok(()))
            .notification_ext::<notification::DidChangeConfiguration>(|_, _| Ok(()))
            .notification_ext::<notification::DidChangeTextDocument>(did_change)
            .event_ext::<event::CollectDiagnostics>(event::collect_diagnostics)
            .event_ext::<event::SpagoAction>(event::spago_action);

        ServiceBuilder::new()
            .layer(LifecycleLayer::default())
            .layer(CatchUnwindLayer::default())
            .layer(ConcurrencyLayer::default())
            .layer(ClientProcessMonitorLayer::new(client))
            .service(router)
    });

    #[cfg(unix)]
    let (stdin, stdout) = (
        async_lsp::stdio::PipeStdin::lock_tokio().unwrap(),
        async_lsp::stdio::PipeStdout::lock_tokio().unwrap(),
    );

    #[cfg(not(unix))]
    let (stdin, stdout) = (
        tokio_util::compat::TokioAsyncReadCompatExt::compat(tokio::io::stdin()),
        tokio_util::compat::TokioAsyncWriteCompatExt::compat_write(tokio::io::stdout()),
    );

    server.run_buffered(stdin, stdout).await.unwrap();
}
