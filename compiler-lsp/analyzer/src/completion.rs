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

pub fn implementation(
    engine: &QueryEngine,
    files: &Files,
    cache: &mut SuggestionsCache,
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
        dot_triggered: trigger_character == Some("."),
    };

    let items = collect(&context, cache)?;
    let is_incomplete = items.len() > 5;

    Ok(Some(CompletionResponse::List(CompletionList { is_incomplete, items })))
}

fn collect(
    context: &Context,
    cache: &mut SuggestionsCache,
) -> Result<Vec<CompletionItem>, AnalyzerError> {
    let mut items = vec![];
    let into = &mut items;

    if context.space_triggered {
        if context.collect_terms() && context.expected_type.is_some() {
            // Always include expression-local bindings.
            let _ = ExpressionLocals.collect_into(context, NoFilter, into);

            // Include module-local and imported terms only if they type-match.
            let mut candidates = vec![];
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

    if context.dot_triggered
        && let Some(type_id) = find_record_type_at_dot(context)
    {
        emit_record_fields(context, type_id, into)?;
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

fn find_record_type_at_dot(context: &Context) -> Option<TypeId> {
    let dot_start = context.token.text_range().start();

    // First: check if ExpressionRecordAccess already exists at the dot position.
    let root = context.parsed.syntax_node();
    {
        let mut node = root.clone();
        loop {
            let child = node.children().find(|c| c.text_range().contains_inclusive(dot_start));
            match child {
                Some(c) => node = c,
                None => break,
            }
        }
        for ancestor in node.ancestors() {
            if let Some(access) = cst::ExpressionRecordAccess::cast(ancestor) {
                let expression = access.expression()?;
                let expr_ptr = AstPtr::new(&expression);
                let completed: Vec<SmolStr> = access
                    .children()
                    .filter(|label| label.syntax().text_range().end() <= dot_start)
                    .filter_map(|label| label.text().map(|t| SmolStr::new(t.text())))
                    .collect();
                let expr_id = context.stabilized.lookup_ptr(&expr_ptr)?;
                let checked = context.engine.checked(context.current_file).ok()?;
                let lowered = context.engine.lowered(context.current_file).ok()?;

                let mut type_id = checked.nodes.lookup_expression(expr_id)?;

                // If the expression type isn't a record (e.g. Rigid from incomplete parse),
                // try looking up the base expression name as a binder in the enclosing scope.
                if sources::extract_record_fields(context.engine, type_id).is_none()
                    && completed.is_empty()
                {
                    let base_name = expression.syntax().text().to_string();
                    let base_name = base_name.trim();
                    if let Some(binder_type) =
                        lookup_binder_type(&checked, &lowered, context, &access, base_name)
                    {
                        type_id = binder_type;
                    }
                }

                for label in &completed {
                    let fields = sources::extract_record_fields(context.engine, type_id)?;
                    type_id = fields.into_iter().find(|(l, _)| l == label).map(|(_, t)| t)?;
                }
                return Some(type_id);
            }
        }
    }

    // Fallback: find the name before the dot via scope lookup.
    // When `rec.` has nothing after the dot, the parser doesn't create
    // ExpressionRecordAccess, so we extract the name and look it up.
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

    let name_end_byte = before.len();
    let name_offset = rowan::TextSize::new(name_end_byte.saturating_sub(1) as u32);
    lookup_name_type(context, &name, name_offset)
}

fn lookup_name_type(context: &Context, name: &str, offset: rowan::TextSize) -> Option<TypeId> {
    let checked = context.engine.checked(context.current_file).ok()?;
    let lowered = context.engine.lowered(context.current_file).ok()?;

    let root = context.parsed.syntax_node();
    let mut node = root;
    loop {
        let child = node.children().find(|c| c.text_range().contains_inclusive(offset));
        match child {
            Some(c) => node = c,
            None => break,
        }
    }

    let scope_id = node.ancestors().find_map(|ancestor| {
        let expr = cst::Expression::cast(ancestor)?;
        let ptr = AstPtr::new(&expr);
        let expr_id = context.stabilized.lookup_ptr(&ptr)?;
        lowered.nodes.lookup_expression(expr_id)
    })?;

    for (_, graph_node) in lowered.graph.traverse(scope_id) {
        match graph_node {
            GraphNode::Binder { binders, puns, .. } => {
                for (binder_name, binder_id) in binders {
                    if binder_name == name {
                        return checked.nodes.lookup_binder(*binder_id);
                    }
                }
                for (pun_name, pun_id) in puns {
                    if pun_name == name {
                        return checked.nodes.puns.get(pun_id).copied();
                    }
                }
            }
            GraphNode::Let { bindings, .. } => {
                for (let_name, let_id) in bindings {
                    if let_name == name {
                        return checked.nodes.lookup_let(*let_id);
                    }
                }
            }
            _ => {}
        }
    }

    // Try top-level terms
    let resolved = context.resolved.lookup_term(context.prim_resolved, None, name)?;
    let type_id = checked.terms.get(&resolved.1)?;
    Some(*type_id)
}

fn emit_record_fields(
    context: &Context,
    type_id: TypeId,
    items: &mut Vec<CompletionItem>,
) -> Result<(), AnalyzerError> {
    let checked = context.engine.checked(context.current_file)?;
    let fields =
        sources::extract_record_fields(context.engine, type_id).ok_or(AnalyzerError::NonFatal)?;

    for (label, field_type) in &fields {
        let type_str = Pretty::new(context.engine, &checked).render(*field_type);
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

    Ok(())
}

fn lookup_binder_type(
    checked: &checking::CheckedModule,
    lowered: &lowering::LoweredModule,
    context: &Context,
    access: &cst::ExpressionRecordAccess,
    name: &str,
) -> Option<TypeId> {
    // Search all scope graph nodes for a binder matching the name with a record type.
    for (_, graph_node) in lowered.graph.iter() {
        match graph_node {
            GraphNode::Binder { binders, puns, .. } => {
                for (binder_name, binder_id) in binders {
                    if binder_name == name {
                        let t = checked.nodes.lookup_binder(*binder_id);
                        if t.is_some_and(|tid| {
                            sources::extract_record_fields(context.engine, tid).is_some()
                        }) {
                            return t;
                        }
                    }
                }
                for (pun_name, pun_id) in puns {
                    if pun_name == name {
                        let t = checked.nodes.puns.get(pun_id).copied();
                        if t.is_some_and(|tid| {
                            sources::extract_record_fields(context.engine, tid).is_some()
                        }) {
                            return t;
                        }
                    }
                }
            }
            GraphNode::Let { bindings, .. } => {
                for (let_name, let_id) in bindings {
                    if let_name == name {
                        let t = checked.nodes.lookup_let(*let_id);
                        if t.is_some_and(|tid| {
                            sources::extract_record_fields(context.engine, tid).is_some()
                        }) {
                            return t;
                        }
                    }
                }
            }
            _ => {}
        }
    }

    // Fallback: decompose the enclosing function's declared type.
    for ancestor in access.syntax().ancestors() {
        let Some(equation) = cst::ValueEquation::cast(ancestor) else { continue };
        let fn_name = equation.name_token()?.text().to_string();
        let (_, term_id) = context.resolved.locals.lookup_term(&fn_name)?;
        let fn_type = checked.terms.get(&term_id).copied()?;

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
            binders.children().position(|b| b.syntax().text().to_string().trim() == name)?;

        for _ in 0..binder_index {
            let checking::core::Type::Function(_, ret) = context.engine.lookup_type(current) else {
                return None;
            };
            current = ret;
        }
        let checking::core::Type::Function(arg, _) = context.engine.lookup_type(current) else {
            return None;
        };
        return Some(arg);
    }

    None
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
