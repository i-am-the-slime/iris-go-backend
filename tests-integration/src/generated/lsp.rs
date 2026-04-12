pub mod render;

use std::fmt::Write;

use analyzer::completion::SuggestionsCache;
use analyzer::{QueryEngine, prim};
use async_lsp::lsp_types::{
    CodeActionOrCommand, CompletionList, CompletionResponse, GotoDefinitionResponse, HoverContents,
    LanguageString, Location, MarkedString, Position, SignatureHelp, TextEdit, Url,
};
use files::{FileId, Files};
use itertools::Itertools;
use line_index::{LineIndex, TextSize};
use render::TabledCompletionItem;
use tabled::Table;
use tabled::settings::{Padding, Style};

#[derive(Debug, Clone, Copy)]
enum CursorKind {
    GotoDefinition,
    Hover,
    Completion,
    CompletionCached,
    CompletionSpace,
    CompletionDot,
    References,
    SignatureHelp,
    CodeAction,
    Rename,
}

impl CursorKind {
    const CHARACTERS: &[char] = &['@', '$', '^', '~', '%', '&', '!', '#', '?', '*'];

    fn parse(text: &str) -> Option<CursorKind> {
        match text {
            "@" => Some(CursorKind::GotoDefinition),
            "$" => Some(CursorKind::Hover),
            "^" => Some(CursorKind::Completion),
            "~" => Some(CursorKind::CompletionCached),
            "!" => Some(CursorKind::CompletionSpace),
            "#" => Some(CursorKind::CompletionDot),
            "%" => Some(CursorKind::References),
            "&" => Some(CursorKind::SignatureHelp),
            "?" => Some(CursorKind::CodeAction),
            "*" => Some(CursorKind::Rename),
            _ => None,
        }
    }

    fn valid(c: char) -> bool {
        CursorKind::CHARACTERS.contains(&c)
    }
}

fn extract_cursors(content: &str) -> Vec<(Position, CursorKind)> {
    let line_index = LineIndex::new(content);
    let mut cursors = vec![];

    for (index, text) in content.match_indices(CursorKind::valid) {
        let line_col = line_index.line_col(TextSize::new(index as u32));
        let line_range = line_index.line(line_col.line).unwrap();
        if !content[line_range].starts_with("--") {
            continue;
        }

        let line = line_col.line - 1;
        let character = line_col.col;
        let position = Position::new(line, character);
        let Some(kind) = CursorKind::parse(text) else { continue };

        cursors.push((position, kind));
    }

    cursors
}

pub fn report(engine: &QueryEngine, files: &Files, id: FileId) -> String {
    let uri = {
        let path = files.path(id);
        let content = files.content(id);
        let uri = Url::parse(&path).unwrap();
        prim::handle_generated(uri, &content).unwrap()
    };

    let content = engine.content(id);
    let line_index = LineIndex::new(&content);
    let cursors = extract_cursors(&content);

    let mut cache = SuggestionsCache::default();
    let mut record_fields_cache = analyzer::completion::RecordFieldsCache::default();
    let mut result = String::new();
    for (index, (position, cursor)) in cursors.iter().enumerate() {
        let uri = uri.clone();

        if index > 0 {
            writeln!(result, "\n").unwrap();
        }

        writeln!(result, "{cursor:#?} at {position:?}\n").unwrap();

        let line_0 = line_index.line(position.line);
        let line_1 = line_index.line(position.line + 1);
        if let Some((line_0, line_1)) = line_0.zip(line_1) {
            let line_0 = &content[line_0];
            let line_1 = &content[line_1];
            writeln!(result, "```").unwrap();
            write!(result, "{line_0}").unwrap();
            write!(result, "{line_1}").unwrap();
            writeln!(result, "```").unwrap();
        }
        writeln!(result).unwrap();

        if matches!(
            cursor,
            CursorKind::Completion | CursorKind::CompletionSpace | CursorKind::CompletionDot
        ) {
            cache = SuggestionsCache::default();
        }

        dispatch_cursor(
            &mut result,
            engine,
            files,
            &mut cache,
            &mut record_fields_cache,
            *position,
            *cursor,
            uri,
        );
    }

    redact_paths(result)
}

fn dispatch_cursor(
    result: &mut String,
    engine: &QueryEngine,
    files: &Files,
    cache: &mut SuggestionsCache,
    record_fields_cache: &mut analyzer::completion::RecordFieldsCache,
    position: Position,
    cursor: CursorKind,
    uri: Url,
) {
    let render_location = |location: Location| -> String {
        format!(
            "{} @ {}:{}..{}:{}",
            location.uri,
            location.range.start.line,
            location.range.start.character,
            location.range.end.line,
            location.range.end.character,
        )
    };

    match cursor {
        CursorKind::GotoDefinition => {
            if let Ok(Some(response)) =
                analyzer::definition::implementation(engine, files, uri, position)
            {
                match response {
                    GotoDefinitionResponse::Scalar(location) => {
                        let location = render_location(location);
                        writeln!(result, "{location}").unwrap();
                    }
                    GotoDefinitionResponse::Array(location) => {
                        let location = location.into_iter().map(render_location).join("\n");
                        writeln!(result, "{location}").unwrap();
                    }
                    GotoDefinitionResponse::Link(_) => (),
                }
            } else {
                writeln!(result, "<empty>").unwrap();
            }
        }
        CursorKind::Hover => {
            if let Ok(Some(response)) =
                analyzer::hover::implementation(engine, files, uri, position)
            {
                let convert = |marked: MarkedString| -> String {
                    match marked {
                        MarkedString::String(string) => string,
                        MarkedString::LanguageString(LanguageString {
                            language, value, ..
                        }) => format!("```{language}\n{value}\n```"),
                    }
                };

                match response.contents {
                    HoverContents::Scalar(marked) => {
                        let marked = convert(marked);
                        if marked.is_empty() {
                            writeln!(result, "<empty>").unwrap();
                        } else {
                            writeln!(result, "{marked}").unwrap();
                        }
                    }
                    HoverContents::Array(marked) => {
                        let marked = marked.into_iter().map(convert).join("\n");
                        if marked.is_empty() {
                            writeln!(result, "<empty>").unwrap();
                        } else {
                            writeln!(result, "{marked}").unwrap();
                        }
                    }
                    HoverContents::Markup(markup) => {
                        if markup.value.is_empty() {
                            writeln!(result, "<empty>").unwrap();
                        } else {
                            writeln!(result, "{}", markup.value).unwrap();
                        }
                    }
                }
            } else {
                writeln!(result, "<empty>").unwrap();
            }
        }
        CursorKind::Completion
        | CursorKind::CompletionCached
        | CursorKind::CompletionSpace
        | CursorKind::CompletionDot => {
            let trigger = match cursor {
                CursorKind::CompletionSpace => Some(" "),
                CursorKind::CompletionDot => Some("."),
                _ => None,
            };
            if let Ok(Some(response)) = analyzer::completion::implementation(
                engine,
                files,
                cache,
                record_fields_cache,
                uri,
                position,
                trigger,
            ) {
                match response {
                    CompletionResponse::Array(items)
                    | CompletionResponse::List(CompletionList { items, .. }) => {
                        let items = items.into_iter().filter_map(|item| {
                            analyzer::completion::resolve::implementation(engine, item).ok()
                        });

                        let items: Vec<TabledCompletionItem> =
                            items.into_iter().map(TabledCompletionItem::from).collect();

                        let mut table = Table::new(items);
                        table.with(Style::modern_rounded());
                        table.with(Padding::new(2, 2, 0, 0));

                        writeln!(result, "{table}").unwrap();
                    }
                }
            } else {
                writeln!(result, "<empty>").unwrap();
            }
        }
        CursorKind::References => {
            if let Ok(Some(location)) =
                analyzer::references::implementation(engine, files, uri, position)
            {
                let location = location.into_iter().map(render_location).join("\n");
                writeln!(result, "{location}").unwrap();
            } else {
                writeln!(result, "<empty>").unwrap();
            }
        }
        CursorKind::SignatureHelp => {
            if let Ok(Some(response)) =
                analyzer::signature_help::implementation(engine, files, uri, position)
            {
                render_signature_help(result, &response);
            } else {
                writeln!(result, "<empty>").unwrap();
            }
        }
        CursorKind::CodeAction => {
            let all_diagnostics = collect_lsp_diagnostics(engine, files, &uri);
            let diagnostics: Vec<_> = all_diagnostics
                .into_iter()
                .filter(|d| {
                    d.range.start.line <= position.line && d.range.end.line >= position.line
                })
                .collect();
            let range = async_lsp::lsp_types::Range::new(position, position);
            if let Ok(Some(actions)) =
                analyzer::code_action::implementation(engine, files, uri, range, &diagnostics)
            {
                render_code_actions(result, &actions);
            } else {
                writeln!(result, "<empty>").unwrap();
            }
        }
        CursorKind::Rename => {
            if let Ok(Some(edit)) = analyzer::rename::implementation(
                engine,
                files,
                uri,
                position,
                "renamed".to_string(),
            ) {
                render_workspace_edit(result, &edit);
            } else {
                writeln!(result, "<empty>").unwrap();
            }
        }
    }
}

fn render_signature_help(result: &mut String, response: &SignatureHelp) {
    for sig in &response.signatures {
        writeln!(result, "```purescript\n{}\n```", sig.label).unwrap();
        if let Some(active) = sig.active_parameter.or(response.active_parameter)
            && let Some(params) = &sig.parameters
        {
            for (i, param) in params.iter().enumerate() {
                let marker = if i == active as usize { "→" } else { " " };
                let label = match &param.label {
                    async_lsp::lsp_types::ParameterLabel::Simple(s) => s.clone(),
                    async_lsp::lsp_types::ParameterLabel::LabelOffsets([s, e]) => {
                        sig.label[*s as usize..*e as usize].to_string()
                    }
                };
                writeln!(result, "{marker} {i}: {label}").unwrap();
            }
        }
    }
}

fn collect_lsp_diagnostics(
    engine: &QueryEngine,
    files: &Files,
    uri: &Url,
) -> Vec<async_lsp::lsp_types::Diagnostic> {
    use analyzer::locate;
    use diagnostics::{DiagnosticsContext, ToDiagnostics};
    use rowan::TextSize;

    let uri_str = uri.as_str();
    let Some(id) = files.id(uri_str) else { return vec![] };

    let content = engine.content(id);
    let Ok((parsed, _)) = engine.parsed(id) else { return vec![] };
    let root = parsed.syntax_node();

    let Ok(stabilized) = engine.stabilized(id) else { return vec![] };
    let Ok(indexed) = engine.indexed(id) else { return vec![] };
    let Ok(lowered) = engine.lowered(id) else { return vec![] };

    let context = DiagnosticsContext::new(&content, &root, &stabilized, &indexed, &lowered);

    let mut all = vec![];
    for error in &lowered.errors {
        all.extend(error.to_diagnostics(&context));
    }

    let to_position = |offset: u32| locate::offset_to_position(&content, TextSize::from(offset));

    all.iter()
        .filter_map(|diagnostic| {
            let start = to_position(diagnostic.primary.start)?;
            let end = to_position(diagnostic.primary.end)?;
            let range = async_lsp::lsp_types::Range { start, end };
            Some(async_lsp::lsp_types::Diagnostic {
                range,
                severity: None,
                code: Some(async_lsp::lsp_types::NumberOrString::String(
                    diagnostic.code.to_string(),
                )),
                code_description: None,
                source: Some(format!("analyzer/{}", diagnostic.source)),
                message: diagnostic.message.clone(),
                related_information: None,
                tags: None,
                data: None,
            })
        })
        .collect()
}

fn render_code_actions(result: &mut String, actions: &[CodeActionOrCommand]) {
    for action in actions {
        match action {
            CodeActionOrCommand::CodeAction(action) => {
                writeln!(result, "Action: {}", action.title).unwrap();
                if let Some(edit) = &action.edit {
                    render_workspace_edit_inner(result, edit, "  ");
                }
            }
            CodeActionOrCommand::Command(cmd) => {
                writeln!(result, "Command: {}", cmd.title).unwrap();
            }
        }
    }
}

fn render_workspace_edit(result: &mut String, edit: &async_lsp::lsp_types::WorkspaceEdit) {
    render_workspace_edit_inner(result, edit, "");
}

fn render_workspace_edit_inner(
    result: &mut String,
    edit: &async_lsp::lsp_types::WorkspaceEdit,
    indent: &str,
) {
    if let Some(changes) = &edit.changes {
        let mut entries: Vec<_> = changes.iter().collect();
        entries.sort_by_key(|(uri, _)| uri.to_string());
        for (uri, edits) in entries {
            writeln!(result, "{indent}{uri}:").unwrap();
            let mut sorted_edits: Vec<&TextEdit> = edits.iter().collect();
            sorted_edits.sort_by_key(|e| (e.range.start.line, e.range.start.character));
            for edit in sorted_edits {
                let r = &edit.range;
                writeln!(
                    result,
                    "{indent}  {}:{}..{}:{} -> {:?}",
                    r.start.line, r.start.character, r.end.line, r.end.character, edit.new_text,
                )
                .unwrap();
            }
        }
    }
}

fn redact_paths(mut result: String) -> String {
    let manifest_directory = env!("CARGO_MANIFEST_DIR");
    let temporary_directory = prim::TEMPORARY_DIRECTORY.path();

    let manifest_directory_url = url::Url::from_file_path(manifest_directory).unwrap();
    let temporary_directory_url = url::Url::from_file_path(temporary_directory).unwrap();

    for (url, redacted) in [
        (manifest_directory_url, "file:///tests-integration"),
        (temporary_directory_url, "file:///temporary-directory"),
    ] {
        let uri = url.to_string();
        result = result.replace(&uri, redacted);
    }

    result
}
