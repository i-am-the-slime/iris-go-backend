use std::collections::HashMap;

use async_lsp::lsp_types::*;
use building::QueryEngine;
use files::{FileId, Files};
use indexing::{TermItemId, TermItemKind, TypeItemId};
use lowering::{BinderId, ExpressionKind, LetBindingNameGroupId, TermVariableResolution, TypeKind};
use parsing::ParsedModule;
use rowan::ast::AstNode;
use stabilizing::StabilizedModule;
use syntax::cst;

use indexing::ImportKind;

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

    // Try local rename first (let, where, binders, parameters)
    if let Some(edit) = try_local_rename(engine, files, current_file, &uri, &located, &new_name)? {
        return Ok(Some(edit));
    }

    // Fall back to global rename
    let definition = resolve_definition(engine, files, current_file, &located)?;
    let reference_locations = references::implementation(engine, files, uri, position)?;

    let mut all_locations: Vec<Location> = vec![];

    if let Some(def) = definition {
        all_locations.push(def);
    }

    if let Some(refs) = reference_locations {
        push_unique(&mut all_locations, refs);
    }

    // Also update import statements referencing this symbol
    if let Some((target_file, target_term, old_name)) =
        resolve_term_target(engine, current_file, &located)?
    {
        let import_locations =
            collect_import_name_locations(engine, files, target_file, target_term, &old_name)?;
        push_unique(&mut all_locations, import_locations);
    }

    if all_locations.is_empty() {
        return Ok(None);
    }

    build_workspace_edit(all_locations, &new_name)
}

fn push_unique(all: &mut Vec<Location>, new: impl IntoIterator<Item = Location>) {
    for loc in new {
        let is_duplicate =
            all.iter().any(|existing| existing.uri == loc.uri && existing.range == loc.range);
        if !is_duplicate {
            all.push(loc);
        }
    }
}

fn resolve_term_target(
    engine: &QueryEngine,
    current_file: FileId,
    located: &locate::Located,
) -> Result<Option<(FileId, TermItemId, String)>, AnalyzerError> {
    let lowered = engine.lowered(current_file)?;
    let indexed = engine.indexed(current_file)?;

    match located {
        locate::Located::TermItem(term_id) => {
            let name = indexed.items[*term_id].name.as_ref().ok_or(AnalyzerError::NonFatal)?;
            Ok(Some((current_file, *term_id, name.to_string())))
        }
        locate::Located::Expression(expression_id) => {
            let kind =
                lowered.info.get_expression_kind(*expression_id).ok_or(AnalyzerError::NonFatal)?;
            match kind {
                ExpressionKind::Variable {
                    resolution: Some(TermVariableResolution::Reference(f_id, t_id)),
                    ..
                } => {
                    let target_indexed = engine.indexed(*f_id)?;
                    let name =
                        target_indexed.items[*t_id].name.as_ref().ok_or(AnalyzerError::NonFatal)?;
                    Ok(Some((*f_id, *t_id, name.to_string())))
                }
                ExpressionKind::Constructor { resolution: Some((f_id, t_id)), .. }
                | ExpressionKind::OperatorName { resolution: Some((f_id, t_id)), .. } => {
                    let target_indexed = engine.indexed(*f_id)?;
                    let name =
                        target_indexed.items[*t_id].name.as_ref().ok_or(AnalyzerError::NonFatal)?;
                    Ok(Some((*f_id, *t_id, name.to_string())))
                }
                _ => Ok(None),
            }
        }
        _ => Ok(None),
    }
}

fn build_workspace_edit(
    locations: Vec<Location>,
    new_name: &str,
) -> Result<Option<WorkspaceEdit>, AnalyzerError> {
    let mut changes: HashMap<Url, Vec<TextEdit>> = HashMap::new();
    for location in locations {
        changes
            .entry(location.uri)
            .or_default()
            .push(TextEdit { range: location.range, new_text: new_name.to_string() });
    }
    Ok(Some(WorkspaceEdit { changes: Some(changes), ..Default::default() }))
}

// ── Local rename (let, where, binders, parameters) ──

fn try_local_rename(
    engine: &QueryEngine,
    files: &Files,
    current_file: FileId,
    uri: &Url,
    located: &locate::Located,
    new_name: &str,
) -> Result<Option<WorkspaceEdit>, AnalyzerError> {
    let lowered = engine.lowered(current_file)?;

    // Determine if the cursor is on a local variable
    let local_target = match located {
        locate::Located::Expression(expression_id) => {
            let kind =
                lowered.info.get_expression_kind(*expression_id).ok_or(AnalyzerError::NonFatal)?;
            match kind {
                ExpressionKind::Variable {
                    resolution: Some(TermVariableResolution::Binder(binder_id)),
                    ..
                } => Some(LocalTarget::Binder(*binder_id)),
                ExpressionKind::Variable {
                    resolution: Some(TermVariableResolution::Let(let_id)),
                    ..
                } => Some(LocalTarget::Let(*let_id)),
                _ => None,
            }
        }
        locate::Located::Binder(binder_id) => {
            let kind = lowered.info.get_binder_kind(*binder_id).ok_or(AnalyzerError::NonFatal)?;
            match kind {
                lowering::BinderKind::Variable { .. } | lowering::BinderKind::Named { .. } => {
                    Some(LocalTarget::Binder(*binder_id))
                }
                _ => None,
            }
        }
        _ => None,
    };

    let Some(target) = local_target else {
        return Ok(None);
    };

    let file_uri = common::file_uri(engine, files, current_file)?;
    let content = engine.content(current_file);
    let (parsed, _) = engine.parsed(current_file)?;
    let stabilized = engine.stabilized(current_file)?;

    let mut locations = vec![];

    match target {
        LocalTarget::Binder(target_binder_id) => {
            // Add the binder definition site
            if let Some(range) = id_range(&content, &parsed, &stabilized, target_binder_id) {
                locations.push(Location { uri: file_uri.clone(), range });
            }

            // Find all expressions referencing this binder
            for (expr_id, expr_kind) in lowered.info.iter_expression() {
                if let ExpressionKind::Variable {
                    resolution: Some(TermVariableResolution::Binder(b_id)),
                    ..
                } = expr_kind
                    && *b_id == target_binder_id
                {
                    if let Some(range) = id_range(&content, &parsed, &stabilized, expr_id) {
                        locations.push(Location { uri: file_uri.clone(), range });
                    }
                }
            }
        }
        LocalTarget::Let(target_let_id) => {
            // Add the let equation name(s) as definition sites
            let group = lowered.info.get_let_binding_group(target_let_id);
            for &equation_id in group.equations.iter() {
                let root = parsed.syntax_node();
                let ptr = stabilized.syntax_ptr(equation_id);
                if let Some(ptr) = ptr
                    && let Some(node) = ptr.try_to_node(&root)
                    && let Some(equation) = cst::LetBindingEquation::cast(node)
                    && let Some(name_token) = equation.name_token()
                {
                    if let Some(range) =
                        locate::text_range_to_range(&content, name_token.text_range())
                    {
                        locations.push(Location { uri: file_uri.clone(), range });
                    }
                }
            }

            // Find all expressions referencing this let binding
            for (expr_id, expr_kind) in lowered.info.iter_expression() {
                if let ExpressionKind::Variable {
                    resolution: Some(TermVariableResolution::Let(l_id)),
                    ..
                } = expr_kind
                    && *l_id == target_let_id
                {
                    if let Some(range) = id_range(&content, &parsed, &stabilized, expr_id) {
                        locations.push(Location { uri: uri.clone(), range });
                    }
                }
            }
        }
    }

    if locations.is_empty() {
        return Ok(None);
    }

    build_workspace_edit(locations, new_name)
}

enum LocalTarget {
    Binder(BinderId),
    Let(LetBindingNameGroupId),
}

fn id_range<T>(
    content: &str,
    parsed: &ParsedModule,
    stabilized: &StabilizedModule,
    item_id: stabilizing::AstId<T>,
) -> Option<Range>
where
    T: AstNode<Language = syntax::PureScript>,
{
    let root = parsed.syntax_node();
    let ptr = stabilized.syntax_ptr(item_id)?;
    locate::syntax_range(content, &root, &ptr)
}

// ── Import statement updates ──

fn collect_import_name_locations(
    engine: &QueryEngine,
    files: &Files,
    target_file: FileId,
    target_term: TermItemId,
    name: &str,
) -> Result<Vec<Location>, AnalyzerError> {
    let mut locations = vec![];

    for workspace_file_id in files.iter_id() {
        let resolved = engine.resolved(workspace_file_id)?;

        let all_imports =
            resolved.unqualified.values().flatten().chain(resolved.qualified.values().flatten());

        for import in all_imports {
            if !matches!(import.kind, ImportKind::Explicit) {
                continue;
            }

            let has_term = import
                .lookup_term(name)
                .is_some_and(|(f, t, _)| f == target_file && t == target_term);

            if !has_term {
                continue;
            }

            // Find the import item name token within the import statement
            let content = engine.content(workspace_file_id);
            let (parsed, _) = engine.parsed(workspace_file_id)?;
            let stabilized = engine.stabilized(workspace_file_id)?;
            let root = parsed.syntax_node();

            let Some(ptr) = stabilized.syntax_ptr(import.id) else { continue };
            let Some(statement) = ptr.try_to_node(&root) else { continue };
            let Some(statement) = cst::ImportStatement::cast(statement) else { continue };
            let Some(import_list) = statement.import_list() else { continue };

            for item in import_list.children() {
                let token = match &item {
                    cst::ImportItem::ImportValue(v) => v.name_token(),
                    cst::ImportItem::ImportOperator(v) => v.name_token(),
                    _ => continue,
                };
                let Some(token) = token else { continue };
                if token.text() != name {
                    continue;
                }

                let Some(range) = locate::text_range_to_range(&content, token.text_range()) else {
                    continue;
                };
                let uri = common::file_uri(engine, files, workspace_file_id)?;
                locations.push(Location { uri, range });
            }
        }
    }

    Ok(locations)
}

// ── Global rename (top-level definitions) ──

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
