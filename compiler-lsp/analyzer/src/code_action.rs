use async_lsp::lsp_types::*;
use building::QueryEngine;
use files::Files;
use rowan::ast::AstNode;

use crate::import_edit::{self, ImportContext};
use crate::{AnalyzerError, locate};

pub fn implementation(
    engine: &QueryEngine,
    files: &Files,
    uri: Url,
    _range: Range,
    diagnostics: &[Diagnostic],
) -> Result<Option<Vec<CodeActionOrCommand>>, AnalyzerError> {
    let current_file = {
        let uri = uri.as_str();
        files.id(uri).ok_or(AnalyzerError::NonFatal)?
    };

    let content = engine.content(current_file);
    let (parsed, _) = engine.parsed(current_file)?;
    let stabilized = engine.stabilized(current_file)?;
    let resolved = engine.resolved(current_file)?;

    let import_ctx = ImportContext {
        content: &content,
        stabilized: &stabilized,
        parsed: &parsed,
        resolved: &resolved,
    };

    let insert_range = insert_import_range(&parsed, &content);

    let prim_id = engine.prim_id();
    let mut actions = vec![];

    for diagnostic in diagnostics {
        let is_not_in_scope = diagnostic
            .code
            .as_ref()
            .is_some_and(|code| matches!(code, NumberOrString::String(s) if s == "NotInScope"));

        if !is_not_in_scope {
            continue;
        }

        let Some(name) = parse_not_in_scope_name(&diagnostic.message) else {
            continue;
        };

        collect_imports(
            engine,
            files,
            current_file,
            prim_id,
            &import_ctx,
            insert_range,
            &uri,
            diagnostic,
            name,
            &mut actions,
        )?;
    }

    if actions.is_empty() { Ok(None) } else { Ok(Some(actions)) }
}

fn parse_not_in_scope_name(message: &str) -> Option<&str> {
    let rest = message.strip_prefix('\'')?;
    let end = rest.find('\'')?;
    Some(&rest[..end])
}

fn insert_import_range(parsed: &parsing::ParsedModule, content: &str) -> Option<Range> {
    let cst = parsed.cst();
    let range = cst.imports().map_or_else(
        || {
            let header = cst.header()?;
            Some(header.syntax().text_range())
        },
        |cst| Some(cst.syntax().text_range()),
    )?;

    let mut position = locate::offset_to_position(content, range.end())?;
    position.line += 1;
    position.character = 0;

    Some(Range::new(position, position))
}

#[allow(clippy::too_many_arguments)]
fn collect_imports(
    engine: &QueryEngine,
    files: &Files,
    current_file: files::FileId,
    prim_id: files::FileId,
    import_ctx: &ImportContext,
    insert_range: Option<Range>,
    uri: &Url,
    diagnostic: &Diagnostic,
    name: &str,
    actions: &mut Vec<CodeActionOrCommand>,
) -> Result<(), AnalyzerError> {
    for import_id in files.iter_id() {
        if import_id == current_file || import_id == prim_id {
            continue;
        }

        let candidate_resolved = engine.resolved(import_id)?;

        for (export_name, file_id, term_id) in candidate_resolved.exports.iter_terms() {
            if export_name.as_str() != name || file_id != import_id {
                continue;
            }

            let (candidate_parsed, _) = engine.parsed(import_id)?;
            let Some(module_name) = candidate_parsed.module_name() else {
                continue;
            };

            let (import_text, import_range) = import_edit::term_import_item(
                import_ctx,
                engine,
                &module_name,
                name,
                file_id,
                term_id,
            );

            if let Some(action) = make_action(
                uri,
                diagnostic,
                name,
                &module_name,
                import_text,
                import_range,
                insert_range,
            ) {
                actions.push(action);
            }
        }

        let type_exports = candidate_resolved
            .exports
            .iter_types()
            .chain(candidate_resolved.exports.iter_classes());

        for (export_name, file_id, type_id) in type_exports {
            if export_name.as_str() != name || file_id != import_id {
                continue;
            }

            let (candidate_parsed, _) = engine.parsed(import_id)?;
            let Some(module_name) = candidate_parsed.module_name() else {
                continue;
            };

            let (import_text, import_range) = import_edit::type_import_item(
                import_ctx,
                engine,
                &module_name,
                name,
                file_id,
                type_id,
            );

            if let Some(action) = make_action(
                uri,
                diagnostic,
                name,
                &module_name,
                import_text,
                import_range,
                insert_range,
            ) {
                actions.push(action);
            }
        }
    }

    Ok(())
}

fn make_action(
    uri: &Url,
    diagnostic: &Diagnostic,
    name: &str,
    module_name: &str,
    import_text: Option<String>,
    import_range: Option<Range>,
    insert_range: Option<Range>,
) -> Option<CodeActionOrCommand> {
    let import_text = import_text?;
    let range = import_range.or(insert_range)?;

    let edit = TextEdit { range, new_text: import_text };
    let mut changes = std::collections::HashMap::new();
    changes.insert(uri.clone(), vec![edit]);

    Some(CodeActionOrCommand::CodeAction(CodeAction {
        title: format!("Import '{name}' from {module_name}"),
        kind: Some(CodeActionKind::QUICKFIX),
        diagnostics: Some(vec![diagnostic.clone()]),
        edit: Some(WorkspaceEdit { changes: Some(changes), ..Default::default() }),
        is_preferred: None,
        disabled: None,
        command: None,
        data: None,
    }))
}
