mod edit;
mod filter;
mod item;
mod prelude;
mod sources;

pub mod resolve;

use std::sync::Arc;

use async_lsp::lsp_types::*;
use building::QueryEngine;
use checking::ExternalQueries;
use checking::core::TypeId;
use checking::core::pretty::Pretty;
use files::Files;
use lowering::scope::GraphNode;
use radix_trie::Trie;
use rowan::TokenAtOffset;
use rowan::ast::{AstNode, AstPtr};
use smol_str::SmolStr;
use syntax::{SyntaxKind, cst};

use filter::{FuzzyMatch, NoFilter, StartsWith};
use item::CompletionItemSpec;
use prelude::{CompletionSource, Context, CursorSemantics, CursorText, Filter};
use resolve::CompletionResolveData;
use sources::{
    ExpressionLocals, ImportedTerms, ImportedTypes, LocalTerms, LocalTypes, PrimTerms, PrimTypes,
    QualifiedModules, QualifiedTerms, QualifiedTermsSuggestions, QualifiedTypes,
    QualifiedTypesSuggestions, RecordFields, SuggestedTerms, SuggestedTypes, WorkspaceModules,
};

use crate::{AnalyzerError, locate, signature_help};

#[derive(Clone, Default)]
pub struct SuggestionsCacheEntry {
    pub terms: Vec<CompletionItem>,
    pub types: Vec<CompletionItem>,
    pub qualified_terms: Vec<CompletionItem>,
    pub qualified_types: Vec<CompletionItem>,
}

pub type SuggestionsCache = Trie<String, Arc<SuggestionsCacheEntry>>;

/// Cache for record binder fields, keyed by (file URI, line).
/// Stores the best-known fields so incremental typing doesn't lose fields
/// that were found on the initial (uncorrupted) completion request.
pub type RecordFieldsCache = std::collections::HashMap<(String, u32), Vec<(SmolStr, TypeId)>>;

pub fn implementation(
    engine: &QueryEngine,
    files: &Files,
    cache: &mut SuggestionsCache,
    record_fields_cache: &mut RecordFieldsCache,
    uri: Url,
    position: Position,
    trigger_character: Option<&str>,
) -> Result<Option<CompletionResponse>, AnalyzerError> {
    let current_file = {
        let uri = uri.as_str();
        files.id(uri).ok_or(AnalyzerError::NonFatal)?
    };

    let prim_id = engine.prim_id();
    let content = engine.content(current_file);
    let (parsed, _) = engine.parsed(current_file)?;

    let offset = locate::position_to_offset(&content, position).ok_or(AnalyzerError::NonFatal)?;

    let node = parsed.syntax_node();
    let token = node.token_at_offset(offset);

    let token = match token {
        TokenAtOffset::None => return Ok(None),
        TokenAtOffset::Single(token) => token,
        TokenAtOffset::Between(left, right) => {
            let left_annotation = left.parent_ancestors().any(|node| {
                let kind = node.kind();
                matches!(kind, SyntaxKind::Annotation)
            });
            if left_annotation { right } else { left }
        }
    };

    let semantics = CursorSemantics::new(&content, position);
    let (text, range) = CursorText::new(&content, &token);

    let stabilized = engine.stabilized(current_file)?;
    let resolved = engine.resolved(current_file)?;
    let prim_resolved = engine.resolved(prim_id)?;

    let expected_type = signature_help::expected_type_at(engine, current_file, offset);

    let context = Context {
        engine,
        files,
        current_file,
        content: &content,
        stabilized: &stabilized,
        parsed: &parsed,
        resolved: &resolved,
        prim_id,
        prim_resolved: &prim_resolved,
        semantics,
        text,
        range,
        expected_type,
        token: token.clone(),
        space_triggered: trigger_character == Some(" "),
        dot_triggered: trigger_character == Some(".")
            || (trigger_character.is_none() && token.text() == "."),
    };

    let items = collect(&context, cache, record_fields_cache, &uri, position)?;
    // Always re-request for record field completions (small lists that need
    // re-querying on backspace), otherwise use heuristic.
    let is_incomplete = items.len() > 5
        || items.iter().any(|i| i.kind == Some(CompletionItemKind::FIELD));

    Ok(Some(CompletionResponse::List(CompletionList { is_incomplete, items })))
}

fn collect(
    context: &Context,
    cache: &mut SuggestionsCache,
    record_fields_cache: &mut RecordFieldsCache,
    uri: &Url,
    position: Position,
) -> Result<Vec<CompletionItem>, AnalyzerError> {
    let mut items = vec![];
    let into = &mut items;

    // Record binder/expression completion takes priority — check before
    // space/dot triggers since it applies in all trigger contexts.
    if let Some(source) = find_record_binder_type(context) {
        // Compute the text edit range for the token under the cursor.
        // Without this, VS Code can't filter completions as the user types.
        let range = context.range.or_else(|| {
            // Find the identifier span at the cursor by scanning the source text.
            // The parser may not tokenize partial text inside `{}` as a LOWER token.
            let cursor_byte: usize = context.token.text_range().end().into();
            let after = &context.content[cursor_byte..];
            let before = &context.content[..cursor_byte];
            let ident_end = after
                .find(|c: char| !c.is_alphanumeric() && c != '_' && c != '\'')
                .unwrap_or(after.len());
            let ident_start = before
                .rfind(|c: char| !c.is_alphanumeric() && c != '_' && c != '\'')
                .map_or(0, |i| i + 1);
            let ident_len = (cursor_byte - ident_start) + ident_end;
            if ident_len > 0 {
                let start = rowan::TextSize::from(ident_start as u32);
                let end = rowan::TextSize::from((ident_start + ident_len) as u32);
                locate::text_range_to_range(
                    context.content,
                    rowan::TextRange::new(start, end),
                )
            } else {
                // Zero-width insertion at cursor.
                let pos = locate::text_range_to_range(
                    context.content,
                    rowan::TextRange::empty(context.token.text_range().start()),
                )?;
                Some(Range { start: pos.start, end: pos.start })
            }
        });
        // Extract fields from the source.
        let mut fields = match source {
            RecordTypeSource::TypeId(type_id) => {
                sources::extract_record_fields(context.engine, type_id).unwrap_or_default()
            }
            RecordTypeSource::Fields(f) => f,
        };

        // Merge with cached fields from previous requests. This ensures
        // fields found on the initial (uncorrupted) request survive when
        // incremental typing corrupts the binder type.
        let cache_key = (uri.to_string(), position.line);
        if let Some(cached) = record_fields_cache.get(&cache_key) {
            for (label, tid) in cached {
                if !fields.iter().any(|(l, _)| l == label) {
                    fields.push((label.clone(), *tid));
                }
            }
        }
        // Update cache if we found more fields than before.
        let cached_count = record_fields_cache.get(&cache_key).map_or(0, |c| c.len());
        if fields.len() >= cached_count {
            record_fields_cache.insert(cache_key, fields.clone());
        }

        emit_record_fields_from_list_with_range(context, &fields, range, into)?;
        return Ok(items);
    }

    if context.space_triggered {
        if context.collect_terms() && context.expected_type.is_some() {
            let mut candidates = vec![];
            let _ = ExpressionLocals.collect_into(context, NoFilter, &mut candidates);
            LocalTerms.collect_into(context, NoFilter, &mut candidates)?;
            ImportedTerms.collect_into(context, NoFilter, &mut candidates)?;
            items.extend(
                candidates
                    .into_iter()
                    .filter(|item| item.sort_text.as_deref().is_some_and(|s| s.starts_with("0!"))),
            );
        }
        return Ok(items);
    }

    if context.dot_triggered {
        let dot_type = find_record_type_at_dot(context);
        let dot_count = dot_type
            .and_then(|tid| sources::extract_record_fields(context.engine, tid))
            .map_or(0, |f| f.len());
        let offset = context.token.text_range().start();
        let annot_fields = annotation_record_fields(context, offset);

        // For `_.` sections: try extracting record type from the expected
        // function argument type (e.g. `asks` expects `(r -> a)`).
        let section_fields = context.expected_type.and_then(|expected| {
            let mut current = expected;
            let arg = loop {
                match context.engine.lookup_type(current) {
                    checking::core::Type::Forall(_, inner)
                    | checking::core::Type::Constrained(_, inner) => current = inner,
                    checking::core::Type::Function(arg, _) => break arg,
                    _ => return None,
                }
            };
            let expanded = expand_synonym_type(context, arg).unwrap_or(arg);
            let fields = sources::extract_record_fields(context.engine, expanded)
                .or_else(|| {
                    let collected = collect_row_fields(context, arg);
                    if collected.is_empty() { None } else { Some(collected) }
                })?;
            Some(fields)
        });
        let section_count = section_fields.as_ref().map_or(0, |f| f.len());

        if section_count > dot_count && section_count >= annot_fields.as_ref().map_or(0, |f| f.len()) {
            emit_record_fields_from_list(context, section_fields.as_ref().unwrap(), into)?;
        } else if annot_fields.as_ref().is_some_and(|f| f.len() > dot_count) {
            emit_record_fields_from_list(context, annot_fields.as_ref().unwrap(), into)?;
        } else if let Some(type_id) = dot_type {
            emit_record_fields(context, type_id, into)?;
        } else if let Some(fields) = &section_fields {
            emit_record_fields_from_list(context, fields, into)?;
        } else {
            emit_record_fields_from_cst(context, into);
        }
        return Ok(items);
    }

    match &context.text {
        CursorText::None => {
            if context.collect_modules() {
                WorkspaceModules.collect_into(context, NoFilter, into)?;
            } else {
                QualifiedModules.collect_into(context, NoFilter, into)?;
            }
            if context.collect_terms() {
                LocalTerms.collect_into(context, NoFilter, into)?;
                let _ = ExpressionLocals.collect_into(context, NoFilter, into);
                ImportedTerms.collect_into(context, NoFilter, into)?;
            }
            if context.collect_types() {
                LocalTypes.collect_into(context, NoFilter, into)?;
                ImportedTypes.collect_into(context, NoFilter, into)?;
            }
        }
        CursorText::Prefix(p) => {
            let p = p.trim_end_matches('.');

            if context.collect_modules() {
                WorkspaceModules.collect_into(context, StartsWith(p), into)?;
            } else {
                QualifiedModules.collect_into(context, StartsWith(p), into)?;
            }
            if context.collect_terms() {
                QualifiedTerms(p).collect_into(context, NoFilter, into)?;
            }
            if context.collect_types() {
                QualifiedTypes(p).collect_into(context, NoFilter, into)?;
            }

            let query = format!("prefix:{p}");
            let suggestions =
                get_or_populate_suggestions(cache, &query, context, Some(p), NoFilter)?;

            if context.collect_terms() && !context.has_qualified_import(p) {
                items.extend(suggestions.qualified_terms.iter().cloned());
            }
            if context.collect_types() && !context.has_qualified_import(p) {
                items.extend(suggestions.qualified_types.iter().cloned());
            }
        }
        CursorText::Name(n) => {
            if context.collect_modules() {
                WorkspaceModules.collect_into(context, StartsWith(n), into)?;
            } else {
                QualifiedModules.collect_into(context, StartsWith(n), into)?;
            }
            if context.collect_terms() {
                LocalTerms.collect_into(context, FuzzyMatch(n), into)?;
                let _ = ExpressionLocals.collect_into(context, FuzzyMatch(n), into);
                ImportedTerms.collect_into(context, FuzzyMatch(n), into)?;
                if context.collect_implicit_prim() {
                    PrimTerms.collect_into(context, FuzzyMatch(n), into)?;
                }
            }
            if context.collect_types() {
                LocalTypes.collect_into(context, FuzzyMatch(n), into)?;
                ImportedTypes.collect_into(context, FuzzyMatch(n), into)?;
                if context.collect_implicit_prim() {
                    PrimTypes.collect_into(context, FuzzyMatch(n), into)?;
                }
            }

            let query = format!("name:{n}");
            let suggestions =
                get_or_populate_suggestions(cache, &query, context, None, StartsWith(n))?;

            if context.collect_terms() {
                items.extend(suggestions.terms.iter().cloned());
            }

            if context.collect_types() {
                items.extend(suggestions.types.iter().cloned());
            }
        }
        CursorText::Both(p, n) => {
            let t: SmolStr = p.chars().chain(n.chars()).collect();
            let p = p.trim_end_matches('.');

            if context.collect_modules() {
                WorkspaceModules.collect_into(context, StartsWith(&t), into)?;
            } else {
                QualifiedModules.collect_into(context, StartsWith(&t), into)?;
            }
            if context.collect_terms() {
                QualifiedTerms(p).collect_into(context, FuzzyMatch(n), into)?;
            }
            if context.collect_types() {
                QualifiedTypes(p).collect_into(context, FuzzyMatch(n), into)?;
            }

            let query = format!("both:{t}");
            let suggestions =
                get_or_populate_suggestions(cache, &query, context, Some(p), FuzzyMatch(n))?;

            if context.collect_terms() && !context.has_qualified_import(p) {
                items.extend(suggestions.qualified_terms.iter().cloned());
            }

            if context.collect_types() && !context.has_qualified_import(p) {
                items.extend(suggestions.qualified_types.iter().cloned());
            }
        }
        CursorText::RecordAccess(expr_ptr, completed, partial) => {
            let source = RecordFields { expr_ptr, completed_labels: completed };
            match partial {
                Some(p) => source.collect_into(context, FuzzyMatch(p), into)?,
                None => source.collect_into(context, NoFilter, into)?,
            };
        }
    }

    Ok(items)
}

/// The record type source, either a TypeId or pre-computed fields from the annotation.
enum RecordTypeSource {
    TypeId(TypeId),
    Fields(Vec<(SmolStr, TypeId)>),
}

/// Detect when cursor is inside a record binder `{ }` or record expression `{ }`.
/// Returns the record type source if known, for field/pun completion.
fn find_record_binder_type(context: &Context) -> Option<RecordTypeSource> {
    let offset = context.token.text_range().start();
    let root = context.parsed.syntax_node();

    let mut node = root;
    loop {
        let child = node.children().find(|c| c.text_range().contains_inclusive(offset));
        match child {
            Some(c) => node = c,
            None => break,
        }
    }

    // Check for BinderRecord ancestor (pattern destructuring).
    let in_binder_record = node.ancestors().any(|n| cst::BinderRecord::cast(n).is_some());

    // Check for ExpressionRecord ancestor (record literal in expression).
    let in_expr_record = node.ancestors().any(|n| cst::ExpressionRecord::cast(n).is_some());

    if !in_binder_record && !in_expr_record {
        return None;
    }

    if in_binder_record {
        // The parser may corrupt binder types by combining record access across
        // line boundaries (e.g. `ctx@{ } <- ask` followed by `ctx.path`), so we
        // collect ALL candidates and pick the one with the MOST fields.
        let mut best_tid: Option<(TypeId, usize)> = None;
        let mut consider = |tid: TypeId| {
            let expanded = expand_synonym_type(context, tid).unwrap_or(tid);
            if let Some(fields) = sources::extract_record_fields(context.engine, expanded) {
                let count = fields.len();
                if best_tid.is_none() || count > best_tid.unwrap().1 {
                    best_tid = Some((expanded, count));
                }
            }
        };

        // From BinderNamed (@): shared resolution (annotation, scoped binder, global search).
        let binder_record_node =
            node.ancestors().find(|n| cst::BinderRecord::cast(n.clone()).is_some());
        if let Some(ref br_node) = binder_record_node {
            let name = br_node.ancestors().find_map(|n| {
                let named = cst::BinderNamed::cast(n)?;
                Some(named.name_token()?.text().to_string())
            });
            if let Some(name) = name {
                if let Some(tid) = resolve_name_record_type(context, br_node, &name) {
                    consider(tid);
                }
            }
        }

        // From DoStatementBind: binder type and RHS expression type.
        let checked = context.engine.checked(context.current_file).ok()?;
        for ancestor in node.ancestors() {
            let Some(bind_cst) = cst::DoStatementBind::cast(ancestor) else { continue };
            if let Some(b) = bind_cst.binder() {
                if let Some(id) = context.stabilized.lookup_ptr(&AstPtr::new(&b)) {
                    if let Some(tid) = checked.nodes.lookup_binder(id) {
                        consider(tid);
                    }
                }
            }
            if let Some(expr) = bind_cst.expression() {
                if let Some(expr_id) = context.stabilized.lookup_ptr(&AstPtr::new(&expr)) {
                    let tid = checked
                        .nodes
                        .lookup_expression(expr_id)
                        .or_else(|| resolve_rhs_type(context, &checked, expr_id));
                    if let Some(tid) = tid {
                        consider(tid);
                    }
                }
            }
            break;
        }

        // From annotation: walk the function's type tree to find row types.
        // This bypasses all binder corruption since annotations are pristine.
        let annot_fields = annotation_record_fields(context, offset);

        // From RHS expression type: walk the do-bind RHS (e.g. `ask`) type tree.
        // Framework types like Om may include extra fields (e.g. route params)
        // that aren't in the annotation but are in the expression type's row.
        let rhs_fields: Option<Vec<(SmolStr, TypeId)>> = (|| {
            let checked = context.engine.checked(context.current_file).ok()?;
            for ancestor in node.ancestors() {
                let Some(bind_cst) = cst::DoStatementBind::cast(ancestor) else { continue };
                let expr = bind_cst.expression()?;
                let expr_id = context.stabilized.lookup_ptr(&AstPtr::new(&expr))?;
                let tid = checked
                    .nodes
                    .lookup_expression(expr_id)
                    .or_else(|| resolve_rhs_type(context, &checked, expr_id))?;
                let fields = collect_row_fields(context, tid);
                return if fields.is_empty() { None } else { Some(fields) };
            }
            None
        })();

        // Merge all sources: annotation fields, binder fields, and RHS fields.
        // The binder may have extra fields (e.g. route params) not in the annotation.
        // Collect all field sources and merge them (union, most fields wins ties).
        let binder_fields = best_tid
            .and_then(|(tid, _)| sources::extract_record_fields(context.engine, tid));
        let all_sources: Vec<&Vec<(SmolStr, TypeId)>> = [
            annot_fields.as_ref(),
            binder_fields.as_ref(),
            rhs_fields.as_ref(),
        ]
        .into_iter()
        .flatten()
        .collect();

        if !all_sources.is_empty() {
            // Start with the source that has the most fields.
            let mut merged = all_sources
                .iter()
                .max_by_key(|f| f.len())
                .unwrap()
                .to_vec();
            // Add missing fields from other sources.
            for source in &all_sources {
                for (label, tid) in source.iter() {
                    if !merged.iter().any(|(l, _)| l == label) {
                        let is_bogus = matches!(
                            context.engine.lookup_type(*tid),
                            checking::core::Type::Unknown(_) | checking::core::Type::Unification(_)
                        );
                        if !is_bogus {
                            merged.push((label.clone(), *tid));
                        }
                    }
                }
            }
            return Some(RecordTypeSource::Fields(merged));
        }
        if let Some((tid, _)) = best_tid {
            return Some(RecordTypeSource::TypeId(tid));
        }
    }

    if in_expr_record {
        // For expression records, check the expected type at this position.
        if let Some(expected) = context.expected_type {
            let expanded = expand_synonym_type(context, expected).unwrap_or(expected);
            if sources::extract_record_fields(context.engine, expanded).is_some() {
                return Some(RecordTypeSource::TypeId(expanded));
            }
        }
    }

    None
}

fn find_record_type_at_dot(context: &Context) -> Option<TypeId> {
    let dot_start = context.token.text_range().start();

    // Find ExpressionRecordAccess at the dot position and extract completed labels.
    let root = context.parsed.syntax_node();
    let access_and_completed = {
        let mut node = root.clone();
        loop {
            let child = node.children().find(|c| c.text_range().contains_inclusive(dot_start));
            match child {
                Some(c) => node = c,
                None => break,
            }
        }
        node.ancestors().find_map(|ancestor| {
            let access = cst::ExpressionRecordAccess::cast(ancestor)?;
            let completed: Vec<SmolStr> = access
                .children()
                .filter(|label| label.syntax().text_range().end() <= dot_start)
                .filter_map(|label| label.text().map(|t| SmolStr::new(t.text())))
                .collect();
            Some((access, completed))
        })
    };

    // If no ExpressionRecordAccess exists, extract the name from source text
    // and look it up via the shared resolution logic (handles let-bound records).
    let Some((access, completed)) = access_and_completed else {
        let dot_byte: usize = dot_start.into();
        let before = context.content[..dot_byte].trim_end_matches('.');
        let name: String = before
            .chars()
            .rev()
            .take_while(|c| c.is_alphanumeric() || *c == '_' || *c == '\'')
            .collect();
        let name: String = name.chars().rev().collect();
        if name.is_empty() {
            return None;
        }
        return resolve_name_record_type(context, &context.token.parent()?, &name);
    };

    let expression = access.expression()?;
    let base_name = expression.syntax().text().to_string();
    let base_name = base_name.trim().to_string();

    // For record accessor sections (`_.field`), the record type comes from
    // the expected function argument type, not from a named variable.
    if cst::ExpressionSection::cast(expression.syntax().clone()).is_some() {
        if let Some(expected) = context.expected_type {
            // expected_type is the type of the whole section: `r -> a`.
            // Extract `r` (the function argument type).
            let record_type = match context.engine.lookup_type(expected) {
                checking::core::Type::Function(arg, _) => Some(arg),
                _ => {
                    // Try peeling the expected type to find a function.
                    let mut current = expected;
                    loop {
                        match context.engine.lookup_type(current) {
                            checking::core::Type::Forall(_, inner)
                            | checking::core::Type::Constrained(_, inner) => current = inner,
                            checking::core::Type::Function(arg, _) => break Some(arg),
                            _ => break None,
                        }
                    }
                }
            };
            if let Some(tid) = record_type {
                let expanded = expand_synonym_type(context, tid).unwrap_or(tid);
                if sources::extract_record_fields(context.engine, expanded).is_some() {
                    return Some(expanded);
                }
                // Also try collect_row_fields for parameterized row aliases.
                let fields = collect_row_fields(context, tid);
                if !fields.is_empty() {
                    // We can't return fields directly from here (returns TypeId),
                    // but the caller's annotation fallback will pick them up.
                    // For now, try the expanded type.
                    if sources::extract_record_fields(context.engine, tid).is_some() {
                        return Some(tid);
                    }
                }
            }
        }
        return None;
    }

    // Use the shared resolution logic (annotation, scoped binder, global search).
    // Additionally try the expression type from the checked module (strategy 3),
    // which only applies when we have an ExpressionRecordAccess with a base expression.
    let base_type = resolve_name_record_type(context, access.syntax(), &base_name)
        .or_else(|| {
            let checked = context.engine.checked(context.current_file).ok()?;
            let expr_ptr = AstPtr::new(&expression);
            let expr_id = context.stabilized.lookup_ptr(&expr_ptr)?;
            let t = checked.nodes.lookup_expression(expr_id)?;
            sources::extract_record_fields(context.engine, t).is_some().then_some(t)
        })?;

    let mut type_id = base_type;
    for label in &completed {
        let fields = sources::extract_record_fields(context.engine, type_id)?;
        type_id = fields.into_iter().find(|(l, _)| l == label).map(|(_, t)| t)?;
    }
    Some(type_id)
}

fn annotation_parameter_type(
    context: &Context,
    cursor_offset: rowan::TextSize,
    param_name: &str,
) -> Option<TypeId> {
    let checked = context.engine.checked(context.current_file).ok()?;
    let lowered = context.engine.lowered(context.current_file).ok()?;

    // Find the ValueEquation at cursor position by scanning all equations.
    let root = context.parsed.syntax_node();
    let mut equation = None;
    for child in root.descendants() {
        if let Some(eq) = cst::ValueEquation::cast(child) {
            let name_range = eq.name_token().map(|t| t.text_range());
            if let Some(r) = name_range
                && r.start() <= cursor_offset
            {
                equation = Some(eq);
            }
        }
    }
    let equation = equation?;

    let fn_name = equation.name_token()?.text().to_string();
    let (_, term_id) = context.resolved.locals.lookup_term(&fn_name)?;
    let term_ir = lowered.info.get_term_item(term_id);
    let term_ir = term_ir?;
    let lowering::TermItemIr::ValueGroup { signature, .. } = term_ir else {
        return None;
    };
    let Some(sig_type_id) = signature else {
        return None;
    };

    let fn_type = checked.nodes.lookup_type(*sig_type_id);
    let fn_type = fn_type?;

    let mut current = fn_type;
    loop {
        match context.engine.lookup_type(current) {
            checking::core::Type::Forall(_, inner) => current = inner,
            checking::core::Type::Constrained(_, inner) => current = inner,
            _ => break,
        }
    }

    let binders = equation.function_binders()?;
    let binder_index =
        binders.children().position(|b| b.syntax().text().to_string().trim() == param_name)?;

    for _ in 0..binder_index {
        let checking::core::Type::Function(_, ret) = context.engine.lookup_type(current) else {
            return None;
        };
        current = ret;
    }
    let checking::core::Type::Function(arg, _) = context.engine.lookup_type(current) else {
        return None;
    };
    Some(arg)
}

/// Walk the enclosing function's annotation type tree to find row types.
/// Returns flattened fields from the row with the most fields.
/// This bypasses type corruption from parser issues since annotations are
/// stored before type checking the body.
fn annotation_record_fields(
    context: &Context,
    cursor_offset: rowan::TextSize,
) -> Option<Vec<(SmolStr, TypeId)>> {
    let checked = context.engine.checked(context.current_file).ok()?;
    let lowered = context.engine.lowered(context.current_file).ok()?;

    let root = context.parsed.syntax_node();
    let mut equation = None;
    for child in root.descendants() {
        if let Some(eq) = cst::ValueEquation::cast(child) {
            let name_range = eq.name_token().map(|t| t.text_range());
            if let Some(r) = name_range
                && r.start() <= cursor_offset
            {
                equation = Some(eq);
            }
        }
    }
    let equation = equation?;

    let fn_name = equation.name_token()?.text().to_string();
    let (_, term_id) = context.resolved.locals.lookup_term(&fn_name)?;
    let term_ir = lowered.info.get_term_item(term_id)?;
    let lowering::TermItemIr::ValueGroup { signature, .. } = term_ir else {
        return None;
    };
    let fn_type = (*signature)
        .and_then(|sid| checked.nodes.lookup_type(sid))
        .or_else(|| checked.terms.get(&term_id).copied())?;

    // Walk the type tree to find row types, expanding synonym applications
    // (e.g. `AuthCtx + BaseCtx + ()` → `AuthCtx (BaseCtx ())` → all fields).
    let mut best: Option<Vec<(SmolStr, TypeId)>> = None;
    let mut stack = vec![fn_type];
    let mut visited = std::collections::HashSet::new();
    while let Some(tid) = stack.pop() {
        if !visited.insert(tid) {
            continue;
        }
        // Try extracting fields via synonym application expansion.
        let fields = collect_row_fields(context, tid);
        if !fields.is_empty() && best.as_ref().is_none_or(|b| fields.len() > b.len()) {
            best = Some(fields);
        }
        // Also check for Application(Record, Row).
        if let Some(fields) = sources::extract_record_fields(context.engine, tid) {
            if best.as_ref().is_none_or(|b| fields.len() > b.len()) {
                best = Some(fields);
            }
        }
        // Recurse into type structure.
        match context.engine.lookup_type(tid) {
            checking::core::Type::Application(a, b)
            | checking::core::Type::KindApplication(a, b)
            | checking::core::Type::Function(a, b)
            | checking::core::Type::Constrained(a, b)
            | checking::core::Type::Kinded(a, b) => {
                stack.push(a);
                stack.push(b);
            }
            checking::core::Type::Forall(_, inner) => stack.push(inner),
            _ => {}
        }
    }
    best
}

type NameSubstitutions = std::collections::HashMap<checking::core::Name, TypeId>;

/// Collect all record fields from a type, expanding synonym applications.
/// This handles `AuthCtx (BaseCtx ())` style parameterized row aliases
/// by applying synonyms and substituting type variables in row tails.
fn collect_row_fields(context: &Context, type_id: TypeId) -> Vec<(SmolStr, TypeId)> {
    let mut fields = vec![];
    let mut subs = NameSubstitutions::new();
    collect_row_fields_inner(context, type_id, &mut subs, &mut fields, 0);
    fields
}

fn collect_row_fields_inner(
    context: &Context,
    type_id: TypeId,
    subs: &mut NameSubstitutions,
    fields: &mut Vec<(SmolStr, TypeId)>,
    depth: usize,
) {
    if depth > 20 {
        return;
    }
    // First resolve Rigid substitutions.
    let type_id = match context.engine.lookup_type(type_id) {
        checking::core::Type::Rigid(name, _, _) => {
            if let Some(&replacement) = subs.get(&name) {
                return collect_row_fields_inner(context, replacement, subs, fields, depth + 1);
            }
            type_id
        }
        _ => type_id,
    };
    match context.engine.lookup_type(type_id) {
        checking::core::Type::Row(row_id) => {
            let row = context.engine.lookup_row_type(row_id);
            fields.extend(row.fields.iter().map(|f| (f.label.clone(), f.id)));
            if let Some(tail) = row.tail {
                collect_row_fields_inner(context, tail, subs, fields, depth + 1);
            }
        }
        checking::core::Type::Application(func, arg) => {
            // Resolve Rigid in function position before trying synonym expansion.
            let func = resolve_rigid(context, func, subs);
            let arg = resolve_rigid(context, arg, subs);
            if let Some((body, new_subs)) = expand_synonym_application(context, func, arg) {
                let old_subs = subs.clone();
                subs.extend(new_subs);
                collect_row_fields_inner(context, body, subs, fields, depth + 1);
                *subs = old_subs;
            } else {
                // Not a synonym — recurse into both func and arg to find nested rows.
                collect_row_fields_inner(context, func, subs, fields, depth + 1);
                collect_row_fields_inner(context, arg, subs, fields, depth + 1);
            }
        }
        checking::core::Type::Constructor(file_id, type_item_id) => {
            // Nullary synonym expansion.
            if let Ok(checked) = context.engine.checked(file_id) {
                if let Some(synonym) = checked.lookup_synonym(type_item_id) {
                    if synonym.parameters.is_empty() {
                        collect_row_fields_inner(
                            context,
                            synonym.synonym,
                            subs,
                            fields,
                            depth + 1,
                        );
                    }
                }
            }
        }
        _ => {}
    }
}

/// Resolve a type through Rigid substitutions.
fn resolve_rigid(context: &Context, type_id: TypeId, subs: &NameSubstitutions) -> TypeId {
    match context.engine.lookup_type(type_id) {
        checking::core::Type::Rigid(name, _, _) => subs.get(&name).copied().unwrap_or(type_id),
        _ => type_id,
    }
}

/// Try to expand `Application(func, arg)` where func resolves to a type
/// synonym constructor. Returns the synonym body and parameter substitutions.
fn expand_synonym_application(
    context: &Context,
    func: TypeId,
    arg: TypeId,
) -> Option<(TypeId, NameSubstitutions)> {
    let mut args = vec![arg];
    let mut current = func;
    loop {
        match context.engine.lookup_type(current) {
            checking::core::Type::Application(f, a) => {
                args.push(a);
                current = f;
            }
            checking::core::Type::KindApplication(f, _) => {
                current = f;
            }
            _ => break,
        }
    }
    args.reverse();

    let checking::core::Type::Constructor(file_id, type_item_id) =
        context.engine.lookup_type(current)
    else {
        return None;
    };
    let checked = context.engine.checked(file_id).ok()?;
    let synonym = checked.lookup_synonym(type_item_id)?;

    if synonym.parameters.is_empty() || args.is_empty() {
        return None;
    }

    let mut substitutions = NameSubstitutions::new();
    for (param, arg) in synonym.parameters.iter().zip(args.iter()) {
        substitutions.insert(param.name, *arg);
    }

    Some((synonym.synonym, substitutions))
}

fn emit_record_fields_from_list_with_range(
    context: &Context,
    fields: &[(SmolStr, TypeId)],
    range: Option<Range>,
    items: &mut Vec<CompletionItem>,
) -> Result<(), AnalyzerError> {
    let checked = context.engine.checked(context.current_file)?;
    for (label, field_type) in fields {
        let type_str = Pretty::new(context.engine, &checked).render(*field_type);
        let mut item = CompletionItemSpec::new(
            label.to_string(),
            range,
            CompletionItemKind::FIELD,
            CompletionResolveData::RecordField,
        );
        item.label_detail(format!(" :: {type_str}"));
        item.label_description("Record".to_string());
        items.push(item.build());
    }
    Ok(())
}

fn emit_record_fields_from_list(
    context: &Context,
    fields: &[(SmolStr, TypeId)],
    items: &mut Vec<CompletionItem>,
) -> Result<(), AnalyzerError> {
    emit_record_fields_from_list_with_range(context, fields, context.range, items)
}

fn emit_record_fields_with_range(
    context: &Context,
    type_id: TypeId,
    range: Option<Range>,
    items: &mut Vec<CompletionItem>,
) -> Result<(), AnalyzerError> {
    let checked = context.engine.checked(context.current_file)?;
    let fields =
        sources::extract_record_fields(context.engine, type_id).ok_or(AnalyzerError::NonFatal)?;
    emit_record_fields_from_list_with_range(context, &fields, range, items)
}

fn emit_record_fields(
    context: &Context,
    type_id: TypeId,
    items: &mut Vec<CompletionItem>,
) -> Result<(), AnalyzerError> {
    emit_record_fields_with_range(context, type_id, context.range, items)
}

/// Fallback: extract record field completions when type info is unavailable.
/// Handles let-bound variables where the type checker didn't solve the binding's type.
/// Supports chained access like `rec.something.` where `rec` is a let-bound record literal.
fn emit_record_fields_from_cst(context: &Context, items: &mut Vec<CompletionItem>) -> bool {
    let dot_start = context.token.text_range().start();
    let dot_byte: usize = dot_start.into();
    let before = context.content[..dot_byte].trim_end_matches('.');

    // Parse the chain: "rec.something" → ["rec", "something"]
    let chain: Vec<&str> = before
        .rsplit(|c: char| c.is_whitespace() || "()#$@!,;[]{}".contains(c))
        .next()
        .unwrap_or("")
        .split('.')
        .filter(|s| !s.is_empty())
        .collect();
    if chain.is_empty() {
        return false;
    }

    let base_name = chain[0];
    let field_path = &chain[1..];

    let lowered = match context.engine.lowered(context.current_file) {
        Ok(l) => l,
        Err(_) => return false,
    };
    let checked = context.engine.checked(context.current_file).ok();

    // Find the RHS expression ID from a let binding or do-bind statement.
    let rhs_expr_id = find_let_rhs_expr(&lowered, base_name)
        .or_else(|| find_do_bind_rhs_expr(&lowered, base_name));
    let Some(rhs_expr_id) = rhs_expr_id else { return false };

    // Strategy A: try type-based resolution.
    if let Some(checked) = &checked {
        let rhs_type = checked
            .nodes
            .lookup_expression(rhs_expr_id)
            .or_else(|| resolve_rhs_type(context, checked, rhs_expr_id));
        if let Some(mut tid) = rhs_type {
            // Drill through field_path.
            let drilled = field_path.iter().all(|label| {
                if let Some(fields) = sources::extract_record_fields(context.engine, tid)
                    && let Some((_, t)) = fields.into_iter().find(|(l, _)| l.as_str() == *label)
                {
                    tid = t;
                    return true;
                }
                false
            });
            if drilled && let Some(fields) = sources::extract_record_fields(context.engine, tid) {
                for (label, field_type) in &fields {
                    let type_str = Pretty::new(context.engine, checked).render(*field_type);
                    let mut item = CompletionItemSpec::new(
                        label.to_string(),
                        context.range,
                        CompletionItemKind::FIELD,
                        CompletionResolveData::RecordField,
                    );
                    item.label_detail(format!(" :: {type_str}"));
                    item.label_description("Record".to_string());
                    items.push(item.build());
                }
                return !items.is_empty();
            }
        }
    }

    // Strategy B: walk the CST record literal and drill through fields.
    let rhs_node = context
        .stabilized
        .ast_ptr(rhs_expr_id)
        .and_then(|ptr| ptr.try_to_node(&context.parsed.syntax_node()));
    let Some(rhs_node) = rhs_node else { return false };

    // Drill through field_path in the CST.
    let target_record = drill_record_cst(&rhs_node, field_path);
    let Some(record) = target_record else { return false };

    for record_item in record.children() {
        let label_text = match &record_item {
            cst::RecordItem::RecordField(f) => {
                f.name().and_then(|n| n.text()).map(|t| t.text().to_string())
            }
            cst::RecordItem::RecordPun(p) => {
                p.name().and_then(|n| n.text()).map(|t| t.text().to_string())
            }
        };
        let Some(label_text) = label_text else { continue };

        let mut item = CompletionItemSpec::new(
            label_text,
            context.range,
            CompletionItemKind::FIELD,
            CompletionResolveData::RecordField,
        );
        item.label_description("Record".to_string());
        items.push(item.build());
    }

    !items.is_empty()
}

/// Expand a type synonym constructor to its underlying type.
fn expand_synonym_type(context: &Context, type_id: TypeId) -> Option<TypeId> {
    let checking::core::Type::Constructor(file_id, type_item_id) =
        context.engine.lookup_type(type_id)
    else {
        return None;
    };
    let checked = context.engine.checked(file_id).ok()?;
    let synonym = checked.lookup_synonym(type_item_id)?;
    Some(synonym.synonym)
}

fn find_do_bind_rhs_expr(
    lowered: &lowering::LoweredModule,
    name: &str,
) -> Option<lowering::ExpressionId> {
    // Find the binder ID for the name from the scope graph.
    let binder_id = lowered.graph.iter().find_map(|(_, graph_node)| {
        let GraphNode::Binder { binders, .. } = graph_node else { return None };
        let (_, id) = binders.iter().find(|(n, _)| **n == name)?;
        Some(*id)
    })?;

    // Find the DoStatement::Bind that uses this binder.
    lowered.info.iter_do_statement().find_map(|(_, stmt)| {
        let lowering::DoStatement::Bind { binder, expression } = stmt else { return None };
        if *binder == Some(binder_id) { *expression } else { None }
    })
}

fn find_let_rhs_expr(
    lowered: &lowering::LoweredModule,
    name: &str,
) -> Option<lowering::ExpressionId> {
    lowered.graph.iter().find_map(|(_, graph_node)| {
        let GraphNode::Let { bindings, .. } = graph_node else { return None };
        let (_, let_id) = bindings.iter().find(|(n, _)| **n == name)?;
        let binding = lowered.info.get_let_binding(*let_id)?;
        let eq = binding.equations.first()?;
        let guarded = eq.guarded.as_ref()?;
        let lowering::GuardedExpression::Unconditional { where_expression } = guarded else {
            return None;
        };
        where_expression.as_ref()?.expression
    })
}

/// Walk a CST record literal, drilling through field names.
/// Given `{ something: { nested: "value" } }` and path `["something"]`,
/// returns the inner record `{ nested: "value" }`.
fn drill_record_cst(node: &cst::Expression, path: &[&str]) -> Option<cst::ExpressionRecord> {
    let mut current = cst::ExpressionRecord::cast(node.syntax().clone())?;

    for field_name in path {
        let field_expr = current.children().find_map(|item| {
            let cst::RecordItem::RecordField(f) = item else { return None };
            let name = f.name()?.text()?.text().to_string();
            if name == *field_name { f.expression() } else { None }
        })?;
        current = cst::ExpressionRecord::cast(field_expr.syntax().clone())?;
    }

    Some(current)
}

/// Resolve the type of a let binding's RHS by walking its CST structure.
/// Handles cases like `let callback = rec.something` where the type checker
/// didn't store the expression type due to errors in the surrounding code.
fn resolve_rhs_type(
    context: &Context,
    checked: &checking::CheckedModule,
    rhs_expr_id: lowering::ExpressionId,
) -> Option<TypeId> {
    let rhs_node = context
        .stabilized
        .ast_ptr(rhs_expr_id)
        .and_then(|ptr| ptr.try_to_node(&context.parsed.syntax_node()))?;

    let rhs_name = rhs_node.syntax().text().to_string();
    let rhs_name = rhs_name.trim();
    let lowered = context.engine.lowered(context.current_file).ok()?;

    // Try to resolve the expression as a name reference (simple variable or function).
    let name_type = context
        .resolved
        .lookup_term(context.prim_resolved, None, rhs_name)
        .and_then(|(_, term_id)| checked.terms.get(&term_id).copied())
        .or_else(|| resolve_let_binding_type(context, checked, &lowered, rhs_name));
    if let Some(tid) = name_type {
        let expanded = expand_synonym_type(context, tid).unwrap_or(tid);
        if sources::extract_record_fields(context.engine, expanded).is_some() {
            return Some(expanded);
        }
    }

    // If the RHS is a record access like `rec.field`, resolve the base and drill.
    let access = cst::ExpressionRecordAccess::cast(rhs_node.syntax().clone())?;
    let base = access.expression()?;
    let labels: Vec<_> =
        access.children().filter_map(|l| l.text().map(|t| SmolStr::new(t.text()))).collect();

    let base_ptr = AstPtr::new(&base);
    let base_name = base.syntax().text().to_string();
    let base_name = base_name.trim();
    let mut type_id = context
        .stabilized
        .lookup_ptr(&base_ptr)
        .and_then(|id| checked.nodes.lookup_expression(id))
        .or_else(|| {
            let (_, term_id) =
                context.resolved.lookup_term(context.prim_resolved, None, base_name)?;
            checked.terms.get(&term_id).copied()
        })
        .or_else(|| resolve_let_binding_type(context, checked, &lowered, base_name))?;

    for label in &labels {
        let fields = sources::extract_record_fields(context.engine, type_id)?;
        type_id = fields.into_iter().find(|(l, _)| l == label).map(|(_, t)| t)?;
    }

    Some(type_id)
}

/// Resolve a let-bound variable's type by examining its RHS expression.
fn resolve_let_binding_type(
    context: &Context,
    checked: &checking::CheckedModule,
    lowered: &lowering::LoweredModule,
    name: &str,
) -> Option<TypeId> {
    // Find the let binding in the scope graph.
    let (let_id, rhs_expr_id) = lowered.graph.iter().find_map(|(_, graph_node)| {
        let GraphNode::Let { bindings, .. } = graph_node else { return None };
        let (_, let_id) = bindings.iter().find(|(n, _)| **n == name)?;
        let binding = lowered.info.get_let_binding(*let_id)?;
        let eq = binding.equations.first()?;
        let guarded = eq.guarded.as_ref()?;
        let lowering::GuardedExpression::Unconditional { where_expression } = guarded else {
            return None;
        };
        let expr_id = where_expression.as_ref()?.expression?;
        Some((*let_id, expr_id))
    })?;

    // Try the let binding's checked type first.
    let let_type = checked.nodes.lookup_let(let_id);
    if let_type.is_some_and(|t| sources::extract_record_fields(context.engine, t).is_some()) {
        return let_type;
    }

    // Try the RHS expression type.
    let rhs_type = checked.nodes.lookup_expression(rhs_expr_id);
    if rhs_type.is_some_and(|t| sources::extract_record_fields(context.engine, t).is_some()) {
        return rhs_type;
    }

    // Recurse: if the RHS is itself a record access or record literal, resolve it.
    resolve_rhs_type(context, checked, rhs_expr_id)
        .filter(|t| sources::extract_record_fields(context.engine, *t).is_some())
}

/// Resolve the record type for a named variable using multiple strategies.
/// Used by both dot-trigger (`ctx.`) and binder-record (`ctx@{ }`) paths.
fn resolve_name_record_type(
    context: &Context,
    start_node: &syntax::SyntaxNode,
    name: &str,
) -> Option<TypeId> {
    let checked = context.engine.checked(context.current_file).ok()?;
    let lowered = context.engine.lowered(context.current_file).ok()?;
    let cursor_offset = start_node.text_range().start();

    // The parser may corrupt types by combining record access across line
    // boundaries, so we collect ALL candidates and pick the one with the
    // MOST fields.
    let mut best: Option<(TypeId, usize)> = None;
    let mut consider = |tid: TypeId| {
        let expanded = expand_synonym_type(context, tid).unwrap_or(tid);
        if let Some(fields) = sources::extract_record_fields(context.engine, expanded) {
            let count = fields.len();
            if best.is_none() || count > best.unwrap().1 {
                best = Some((expanded, count));
            }
        }
    };

    // Strategy 1a: annotation parameter type (direct function parameter).
    if let Some(t) = annotation_parameter_type(context, cursor_offset, name) {
        consider(t);
    }

    // Strategy 1b: record type from annotation type tree (for do-bind binders
    // where the variable isn't a direct parameter but appears in the function's
    // annotated type as a record row).
    // annotation_record_fields is called at a higher level (find_record_binder_type)
    // since it returns fields directly, not a TypeId.

    // Strategy 2: binder type (from do-bind, function param, etc.)
    if let Some(t) = lookup_binder_type_scoped(&checked, &lowered, context, start_node, name) {
        consider(t);
    }

    // Strategy 3: global binder/let search (finds matching name from any scope).
    for (_, graph_node) in lowered.graph.iter() {
        let candidate = match graph_node {
            GraphNode::Binder { binders, .. } => binders
                .iter()
                .find(|(n, _)| **n == name)
                .and_then(|(_, id)| checked.nodes.lookup_binder(*id)),
            GraphNode::Let { bindings, .. } => bindings
                .iter()
                .find(|(n, _)| **n == name)
                .and_then(|(_, id)| {
                    checked.nodes.lookup_let(*id).or_else(|| {
                        let binding = lowered.info.get_let_binding(*id)?;
                        let eq = binding.equations.first()?;
                        let guarded = eq.guarded.as_ref()?;
                        let lowering::GuardedExpression::Unconditional { where_expression } =
                            guarded
                        else {
                            return None;
                        };
                        let expr_id = where_expression.as_ref()?.expression?;
                        checked.nodes.lookup_expression(expr_id)
                    })
                }),
            _ => None,
        };
        if let Some(tid) = candidate {
            consider(tid);
        }
    }

    best.map(|(tid, _)| tid)
}

fn lookup_binder_type_scoped(
    checked: &checking::CheckedModule,
    lowered: &lowering::LoweredModule,
    context: &Context,
    start_node: &syntax::SyntaxNode,
    name: &str,
) -> Option<TypeId> {
    let mut best: Option<(TypeId, usize)> = None;
    for ancestor in start_node.ancestors() {
        let Some(expr) = cst::Expression::cast(ancestor.clone()) else { continue };
        let ptr = AstPtr::new(&expr);
        let Some(expr_id) = context.stabilized.lookup_ptr(&ptr) else { continue };
        let Some(scope_id) = lowered.nodes.lookup_expression(expr_id) else { continue };

        for (_, graph_node) in lowered.graph.traverse(scope_id) {
            let candidate = match graph_node {
                GraphNode::Binder { binders, puns, .. } => {
                    let from_binder = binders
                        .iter()
                        .find(|(n, _)| *n == name)
                        .and_then(|(_, id)| checked.nodes.lookup_binder(*id));
                    let from_pun = puns
                        .iter()
                        .find(|(n, _)| *n == name)
                        .and_then(|(_, id)| checked.nodes.puns.get(id).copied());
                    from_binder.or(from_pun)
                }
                GraphNode::Let { bindings, .. } => bindings
                    .iter()
                    .find(|(n, _)| *n == name)
                    .and_then(|(_, id)| checked.nodes.lookup_let(*id)),
                _ => None,
            };
            if let Some(tid) = candidate {
                let expanded = expand_synonym_type(context, tid).unwrap_or(tid);
                if let Some(fields) = sources::extract_record_fields(context.engine, expanded) {
                    let count = fields.len();
                    if best.is_none() || count > best.unwrap().1 {
                        best = Some((expanded, count));
                    }
                }
            }
        }
    }
    best.map(|(tid, _)| tid)
}

fn get_or_populate_suggestions<F: Filter>(
    cache: &mut SuggestionsCache,
    query: &str,
    context: &Context,
    prefix: Option<&str>,
    filter: F,
) -> Result<Arc<SuggestionsCacheEntry>, AnalyzerError> {
    let query = query.to_lowercase();

    if let Some(cached) = cache.get(&query) {
        tracing::debug!("Found exact match for '{query}'");
        let filtered = filter_suggestions(cached, prefix, &filter, context);
        return Ok(Arc::new(filtered));
    }

    if let Some(cached) = cache.get_ancestor_value(&query) {
        tracing::debug!("Found prefix match for '{query}'");
        let filtered = filter_suggestions(cached, prefix, &filter, context);

        let key = query.to_string();
        let value = Arc::new(filtered);
        cache.insert(key, Arc::clone(&value));

        return Ok(value);
    }

    tracing::debug!("Initialising cache for '{query}'");

    let mut suggestions = SuggestionsCacheEntry::default();

    if let Some(prefix) = prefix {
        QualifiedTermsSuggestions(prefix).collect_into(
            context,
            filter,
            &mut suggestions.qualified_terms,
        )?;
        QualifiedTypesSuggestions(prefix).collect_into(
            context,
            filter,
            &mut suggestions.qualified_types,
        )?;
    } else {
        SuggestedTerms.collect_into(context, filter, &mut suggestions.terms)?;
        SuggestedTypes.collect_into(context, filter, &mut suggestions.types)?;
    }

    let key = query.to_string();
    let value = Arc::new(suggestions);
    cache.insert(key, Arc::clone(&value));

    Ok(value)
}

fn filter_suggestions<F>(
    cached: &SuggestionsCacheEntry,
    prefix: Option<&str>,
    filter: &F,
    context: &Context,
) -> SuggestionsCacheEntry
where
    F: Filter,
{
    SuggestionsCacheEntry {
        terms: collect_entries(&cached.terms, filter, prefix, context),
        types: collect_entries(&cached.types, filter, prefix, context),
        qualified_terms: collect_entries(&cached.qualified_terms, filter, prefix, context),
        qualified_types: collect_entries(&cached.qualified_types, filter, prefix, context),
    }
}

fn collect_entries<F>(
    items: &[CompletionItem],
    filter: &F,
    prefix: Option<&str>,
    context: &Context,
) -> Vec<CompletionItem>
where
    F: Filter,
{
    let entries = items.iter().filter(|item| {
        if !filter.matches(&item.label) {
            return false;
        }
        if item.additional_text_edits.is_some() {
            let has_import = match item.kind {
                Some(CompletionItemKind::VALUE) => context.has_term_import(prefix, &item.label),
                Some(CompletionItemKind::STRUCT) => context.has_type_import(prefix, &item.label),
                _ => false,
            };
            if has_import {
                return false;
            }
        }
        true
    });

    let entries = entries.cloned().map(|mut item| {
        let Some(range) = context.range else {
            return item;
        };
        if let Some(CompletionTextEdit::Edit(text_edit)) = &mut item.text_edit {
            text_edit.range = range;
        }
        item
    });

    entries.collect()
}
