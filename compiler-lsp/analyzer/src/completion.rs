mod edit;
mod filter;
mod item;
mod prelude;
mod sources;

pub mod resolve;

use std::sync::Arc;

use async_lsp::lsp_types::*;
use building::QueryEngine;
use files::Files;
use radix_trie::Trie;
use rowan::TokenAtOffset;
use smol_str::SmolStr;

use filter::{FuzzyMatch, NoFilter, StartsWith};
use prelude::{CompletionSource, Context, CursorSemantics, CursorText, Filter};
use sources::{
    ExpressionLocals, ImportedTerms, ImportedTypes, LocalTerms, LocalTypes, PrimTerms, PrimTypes,
    QualifiedModules, QualifiedTerms, QualifiedTermsSuggestions, QualifiedTypes,
    QualifiedTypesSuggestions, RecordFields, SuggestedTerms, SuggestedTypes, WorkspaceModules,
};
use syntax::SyntaxKind;

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
            items.extend(candidates.into_iter().filter(|item| {
                item.sort_text.as_deref().is_some_and(|s| s.starts_with("0!"))
            }));
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
