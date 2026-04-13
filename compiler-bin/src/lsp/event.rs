use std::path::PathBuf;

use analyzer::{common, locate};
use async_lsp::LanguageClient;
use async_lsp::lsp_types::*;
use checking::ExternalQueries;
use diagnostics::{DiagnosticsContext, ToDiagnostics};
use files::FileId;
use itertools::Itertools;
use rowan::TextSize;
use tokio::task;

use crate::lsp::error::LspError;
use crate::lsp::{SpagoActionKind, State, StateSnapshot, run_spago};

pub fn emit_collect_diagnostics(state: &mut State, uri: Url) -> Result<(), LspError> {
    let files = state.files.read();
    let uri = uri.as_str();

    if let Some(file_id) = files.id(uri) {
        state.client.emit(CollectDiagnostics(file_id))?;
    }

    Ok(())
}

pub struct CollectDiagnostics(FileId);

pub fn collect_diagnostics(state: &mut State, id: CollectDiagnostics) -> Result<(), LspError> {
    state.spawn(move |snapshot| {
        let _span = tracing::info_span!("collect-diagnostics-task").entered();
        collect_diagnostics_core(snapshot, id).inspect_err(|error| error.emit_trace())
    });
    Ok(())
}

fn collect_diagnostics_core(
    mut snapshot: StateSnapshot,
    CollectDiagnostics(id): CollectDiagnostics,
) -> Result<(), LspError> {
    let content = snapshot.engine.content(id);

    let (parsed, _) = snapshot.engine.parsed(id)?;
    let root = parsed.syntax_node();

    let stabilized = snapshot.engine.stabilized(id)?;
    let indexed = snapshot.engine.indexed(id)?;
    let resolved = snapshot.engine.resolved(id)?;
    let lowered = snapshot.engine.lowered(id)?;
    let checked = snapshot.engine.checked(id);

    let uri = {
        let files = snapshot.files.read();
        common::file_uri(&snapshot.engine, &files, id)?
    };

    let lookup = |id: checking::core::SmolStrId| snapshot.engine.lookup_smol_str(id);

    let context = DiagnosticsContext::new(&content, &root, &stabilized, &indexed, &lowered);
    let context = if checked.is_ok() { context.with_checking_lookup(&lookup) } else { context };

    let mut all_diagnostics = vec![];

    for error in &lowered.errors {
        all_diagnostics.extend(error.to_diagnostics(&context));
    }

    for error in &resolved.errors {
        all_diagnostics.extend(error.to_diagnostics(&context));
    }

    if let Ok(checked) = &checked {
        for error in &checked.errors {
            all_diagnostics.extend(error.to_diagnostics(&context));
        }
    }

    let to_position = |offset: u32| locate::offset_to_position(&content, TextSize::from(offset));

    let diagnostics = all_diagnostics
        .iter()
        .filter_map(|diagnostic| {
            let start = to_position(diagnostic.primary.start)?;
            let end = to_position(diagnostic.primary.end)?;
            let range = Range { start, end };

            let severity = match diagnostic.severity {
                diagnostics::Severity::Error => DiagnosticSeverity::ERROR,
                diagnostics::Severity::Warning => DiagnosticSeverity::WARNING,
            };

            let related_information = diagnostic.related.iter().filter_map(|related| {
                let start = to_position(related.span.start)?;
                let end = to_position(related.span.end)?;
                Some(DiagnosticRelatedInformation {
                    location: Location { uri: uri.clone(), range: Range { start, end } },
                    message: related.message.clone(),
                })
            });

            let related_information = related_information.collect_vec();

            Some(Diagnostic {
                range,
                severity: Some(severity),
                code: Some(NumberOrString::String(diagnostic.code.to_string())),
                code_description: None,
                source: Some(format!("analyzer/{}", diagnostic.source)),
                message: diagnostic.message.clone(),
                related_information: if related_information.is_empty() {
                    None
                } else {
                    Some(related_information)
                },
                tags: None,
                data: None,
            })
        })
        .collect();

    snapshot.client.publish_diagnostics(PublishDiagnosticsParams {
        uri,
        diagnostics,
        version: None,
    })?;

    Ok(())
}

pub struct SpagoAction(pub SpagoActionKind, pub PathBuf);

pub fn spago_action(state: &mut State, action: SpagoAction) -> Result<(), LspError> {
    let SpagoAction(kind, root) = action;
    let mut client = state.client.clone();

    let message = match &kind {
        SpagoActionKind::Install => {
            "Dependencies may be missing or out of date. Run spago install?".to_string()
        }
    };

    task::spawn(async move {
        let response = client
            .show_message_request(ShowMessageRequestParams {
                typ: MessageType::INFO,
                message,
                actions: Some(vec![MessageActionItem {
                    title: "Yes".to_string(),
                    properties: Default::default(),
                }]),
            })
            .await;

        let accepted = matches!(response, Ok(Some(ref item)) if item.title == "Yes");
        if !accepted {
            return;
        }

        task::spawn_blocking(move || {
            let ok = match kind {
                SpagoActionKind::Install => run_spago(&root, "install"),
            };

            if ok {
                let _ = client.show_message(ShowMessageParams {
                    typ: MessageType::INFO,
                    message: "spago install complete. Please reload the window to pick up new dependencies.".to_string(),
                });
            } else {
                let _ = client.show_message(ShowMessageParams {
                    typ: MessageType::ERROR,
                    message: "spago command failed. Check the output for details.".to_string(),
                });
            }
        })
        .await
        .ok();
    });

    Ok(())
}
