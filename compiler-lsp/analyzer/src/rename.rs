use std::collections::HashMap;

use async_lsp::lsp_types::*;
use building::QueryEngine;
use files::{FileId, Files};
use indexing::{TermItemId, TermItemKind, TypeItemId};
use lowering::{ExpressionKind, TermVariableResolution, TypeKind};
use rowan::ast::AstNode;
use syntax::cst;

use crate::{AnalyzerError, common, locate, references};

pub fn implementation(
    engine: &QueryEngine,
    files: &Files,
    uri: Url,
    position: Position,
    new_name: String,
) -> Result<Option<WorkspaceEdit>, AnalyzerError> {
    let current_file = {
        let uri = uri.as_str();
        files.id(uri).ok_or(AnalyzerError::NonFatal)?
    };

    let located = locate::locate(engine, current_file, position)?;
    let definition = resolve_definition(engine, files, current_file, &located)?;
    let reference_locations = references::implementation(engine, files, uri, position)?;

    let mut all_locations: Vec<Location> = vec![];

    if let Some(def) = definition {
        all_locations.push(def);
    }

    if let Some(refs) = reference_locations {
        for loc in refs {
            let is_duplicate = all_locations
                .iter()
                .any(|existing| existing.uri == loc.uri && existing.range == loc.range);
            if !is_duplicate {
                all_locations.push(loc);
            }
        }
    }

    if all_locations.is_empty() {
        return Ok(None);
    }

    let mut changes: HashMap<Url, Vec<TextEdit>> = HashMap::new();
    for location in all_locations {
        changes
            .entry(location.uri)
            .or_default()
            .push(TextEdit { range: location.range, new_text: new_name.clone() });
    }

    Ok(Some(WorkspaceEdit { changes: Some(changes), ..Default::default() }))
}

fn term_name_location(
    engine: &QueryEngine,
    files: &Files,
    file_id: FileId,
    term_id: TermItemId,
) -> Result<Option<Location>, AnalyzerError> {
    let uri = common::file_uri(engine, files, file_id)?;
    let content = engine.content(file_id);
    let (parsed, _) = engine.parsed(file_id)?;
    let stabilized = engine.stabilized(file_id)?;
    let indexed = engine.indexed(file_id)?;

    let root = parsed.syntax_node();
    let item = &indexed.items[term_id];

    let range = match &item.kind {
        TermItemKind::Value { equations, .. } => {
            let Some(equation_id) = equations.first().copied() else { return Ok(None) };
            let Some(ptr) = stabilized.syntax_ptr(equation_id) else { return Ok(None) };
            let Some(node) = ptr.try_to_node(&root) else { return Ok(None) };
            let Some(equation) = cst::ValueEquation::cast(node) else { return Ok(None) };
            let Some(name_token) = equation.name_token() else { return Ok(None) };
            locate::text_range_to_range(&content, name_token.text_range())
        }
        _ => {
            let Some(name) = item.name.as_ref() else { return Ok(None) };
            let pointers = indexed.term_item_ptr(&stabilized, term_id);
            for ptr in pointers {
                if let Some(node) = ptr.try_to_node(&root)
                    && let Some(token) = node.descendants_with_tokens().find_map(|it| {
                        let token = it.into_token()?;
                        if token.text() == name.as_str() { Some(token) } else { None }
                    })
                {
                    return Ok(locate::text_range_to_range(&content, token.text_range())
                        .map(|range| Location { uri, range }));
                }
            }
            None
        }
    };

    Ok(range.map(|range| Location { uri, range }))
}

fn type_name_location(
    engine: &QueryEngine,
    files: &Files,
    file_id: FileId,
    type_id: TypeItemId,
) -> Result<Option<Location>, AnalyzerError> {
    let uri = common::file_uri(engine, files, file_id)?;
    let content = engine.content(file_id);
    let (parsed, _) = engine.parsed(file_id)?;
    let stabilized = engine.stabilized(file_id)?;
    let indexed = engine.indexed(file_id)?;

    let root = parsed.syntax_node();
    let item = &indexed.items[type_id];
    let Some(name) = item.name.as_ref() else { return Ok(None) };

    let pointers = indexed.type_item_ptr(&stabilized, type_id);
    for ptr in pointers {
        if let Some(node) = ptr.try_to_node(&root)
            && let Some(token) = node.descendants_with_tokens().find_map(|it| {
                let token = it.into_token()?;
                if token.text() == name.as_str() { Some(token) } else { None }
            })
        {
            return Ok(locate::text_range_to_range(&content, token.text_range())
                .map(|range| Location { uri, range }));
        }
    }

    Ok(None)
}

fn resolve_definition(
    engine: &QueryEngine,
    files: &Files,
    current_file: FileId,
    located: &locate::Located,
) -> Result<Option<Location>, AnalyzerError> {
    match located {
        locate::Located::TermItem(term_id) => {
            term_name_location(engine, files, current_file, *term_id)
        }
        locate::Located::TypeItem(type_id) => {
            type_name_location(engine, files, current_file, *type_id)
        }
        locate::Located::Expression(expression_id) => {
            let lowered = engine.lowered(current_file)?;
            let kind =
                lowered.info.get_expression_kind(*expression_id).ok_or(AnalyzerError::NonFatal)?;
            match kind {
                ExpressionKind::Variable {
                    resolution: Some(TermVariableResolution::Reference(f_id, t_id)),
                    ..
                } => term_name_location(engine, files, *f_id, *t_id),
                ExpressionKind::Constructor { resolution: Some((f_id, t_id)), .. }
                | ExpressionKind::OperatorName { resolution: Some((f_id, t_id)), .. } => {
                    term_name_location(engine, files, *f_id, *t_id)
                }
                _ => Ok(None),
            }
        }
        locate::Located::Type(type_id) => {
            let lowered = engine.lowered(current_file)?;
            let kind = lowered.info.get_type_kind(*type_id).ok_or(AnalyzerError::NonFatal)?;
            match kind {
                TypeKind::Constructor { resolution: Some((f_id, t_id)), .. } => {
                    type_name_location(engine, files, *f_id, *t_id)
                }
                _ => Ok(None),
            }
        }
        locate::Located::TermOperator(operator_id) => {
            let lowered = engine.lowered(current_file)?;
            let (f_id, t_id) =
                lowered.info.get_term_operator(*operator_id).ok_or(AnalyzerError::NonFatal)?;
            term_name_location(engine, files, f_id, t_id)
        }
        locate::Located::TypeOperator(operator_id) => {
            let lowered = engine.lowered(current_file)?;
            let (f_id, t_id) =
                lowered.info.get_type_operator(*operator_id).ok_or(AnalyzerError::NonFatal)?;
            type_name_location(engine, files, f_id, t_id)
        }
        _ => Ok(None),
    }
}
