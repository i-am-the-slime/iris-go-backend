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
        dot_triggered: trigger_character == Some(".")
            || (trigger_character.is_none() && token.text() == "."),
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
            // Only include candidates that type-match the expected argument.
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

    if let Some(type_id) = find_record_binder_type(context) {
        emit_record_fields(context, type_id, into)?;
        return Ok(items);
    }

    if context.dot_triggered {
        if let Some(type_id) = find_record_type_at_dot(context) {
            emit_record_fields(context, type_id, into)?;
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

/// Detect when cursor is inside a record binder `{ }` or record expression `{ }`.
/// Returns the record type if known, for field/pun completion.
fn find_record_binder_type(context: &Context) -> Option<TypeId> {
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

    let checked = context.engine.checked(context.current_file).ok()?;
    let lowered = context.engine.lowered(context.current_file).ok()?;

    // Check for BinderRecord ancestor (pattern destructuring).
    let in_binder_record = node.ancestors().any(|n| cst::BinderRecord::cast(n).is_some());

    // Check for ExpressionRecord ancestor (record literal in expression).
    let in_expr_record = node.ancestors().any(|n| cst::ExpressionRecord::cast(n).is_some());

    if !in_binder_record && !in_expr_record {
        return None;
    }

    if in_binder_record {
        // Try 1: Walk up to DoStatementBind and resolve the record type.
        let type_from_do_bind = node.ancestors().find_map(|n| {
            let bind_cst = cst::DoStatementBind::cast(n)?;

            // Try binder type first (works for ctx@{ } with solved named binder).
            let from_binder = bind_cst.binder().and_then(|b| {
                let ptr = AstPtr::new(&b);
                let id = context.stabilized.lookup_ptr(&ptr)?;
                let tid = checked.nodes.lookup_binder(id)?;
                let expanded = expand_synonym_type(context, tid).unwrap_or(tid);
                sources::extract_record_fields(context.engine, expanded)
                    .is_some()
                    .then_some(expanded)
            });
            if from_binder.is_some() {
                return from_binder;
            }

            // Try RHS expression type (works for { } <- ask).
            let expr = bind_cst.expression()?;
            let expr_ptr = AstPtr::new(&expr);
            let expr_id = context.stabilized.lookup_ptr(&expr_ptr)?;
            let tid = checked
                .nodes
                .lookup_expression(expr_id)
                .or_else(|| resolve_rhs_type(context, &checked, expr_id))?;
            let expanded = expand_synonym_type(context, tid).unwrap_or(tid);
            sources::extract_record_fields(context.engine, expanded).is_some().then_some(expanded)
        });
        if type_from_do_bind.is_some() {
            return type_from_do_bind;
        }

        // Try 2: Walk up to find a BinderNamed (@) and use its scope binder type.
        let type_from_named = node.ancestors().find_map(|n| {
            let named = cst::BinderNamed::cast(n)?;
            let name = named.name_token()?.text().to_string();
            // Search scope graph for this name's binder type.
            lowered.graph.iter().find_map(|(_, gn)| {
                let GraphNode::Binder { binders, .. } = gn else { return None };
                let (_, bid) = binders.iter().find(|(n, _)| **n == name)?;
                let tid = checked.nodes.lookup_binder(*bid)?;
                let expanded = expand_synonym_type(context, tid).unwrap_or(tid);
                sources::extract_record_fields(context.engine, expanded)
                    .is_some()
                    .then_some(expanded)
            })
        });
        if type_from_named.is_some() {
            return type_from_named;
        }

        // Try 3: Walk up to function equation binders and match by position.
        let type_from_equation = node.ancestors().find_map(|n| {
            let equation = cst::ValueEquation::cast(n)?;
            let fn_name = equation.name_token()?.text().to_string();
            let (_, term_id) = context.resolved.locals.lookup_term(&fn_name)?;
            let fn_type = checked.terms.get(&term_id).copied()?;
            // For a function `f { field } = ...`, the first param type is the record.
            let mut current = fn_type;
            loop {
                match context.engine.lookup_type(current) {
                    checking::core::Type::Forall(_, inner) => current = inner,
                    checking::core::Type::Constrained(_, inner) => current = inner,
                    _ => break,
                }
            }
            let checking::core::Type::Function(arg, _) = context.engine.lookup_type(current) else {
                return None;
            };
            let expanded = expand_synonym_type(context, arg).unwrap_or(arg);
            sources::extract_record_fields(context.engine, expanded).is_some().then_some(expanded)
        });
        if type_from_equation.is_some() {
            return type_from_equation;
        }
    }

    if in_expr_record {
        // For expression records, check the expected type at this position.
        if let Some(expected) = context.expected_type {
            let expanded = expand_synonym_type(context, expected).unwrap_or(expected);
            if sources::extract_record_fields(context.engine, expanded).is_some() {
                return Some(expanded);
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
    // and look it up via the scope graph (handles let-bound records).
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
        let checked = context.engine.checked(context.current_file).ok()?;
        let lowered = context.engine.lowered(context.current_file).ok()?;
        for (_, graph_node) in lowered.graph.iter() {
            let candidate = match graph_node {
                GraphNode::Let { bindings, .. } => {
                    let Some((_, let_id)) = bindings.iter().find(|(n, _)| **n == name) else {
                        continue;
                    };
                    // Try the let binding type first.
                    let let_type = checked.nodes.lookup_let(*let_id);
                    if let_type.is_some_and(|t| {
                        sources::extract_record_fields(context.engine, t).is_some()
                    }) {
                        return let_type;
                    }
                    // If unsolved, try the RHS expression type.

                    lowered
                        .info
                        .get_let_binding(*let_id)
                        .and_then(|b| b.equations.first())
                        .and_then(|eq| eq.guarded.as_ref())
                        .and_then(|g| match g {
                            lowering::GuardedExpression::Unconditional { where_expression } => {
                                where_expression.as_ref()
                            }
                            _ => None,
                        })
                        .and_then(|w| w.expression)
                        .and_then(|expr_id| checked.nodes.lookup_expression(expr_id))
                }
                GraphNode::Binder { binders, .. } => binders
                    .iter()
                    .find(|(n, _)| **n == name)
                    .and_then(|(_, id)| checked.nodes.lookup_binder(*id)),
                _ => None,
            };
            if let Some(tid) = candidate
                && sources::extract_record_fields(context.engine, tid).is_some()
            {
                return Some(tid);
            }
        }
        return None;
    };

    let expression = access.expression()?;
    let base_name = expression.syntax().text().to_string();
    let base_name = base_name.trim().to_string();

    let checked = context.engine.checked(context.current_file).ok()?;
    let lowered = context.engine.lowered(context.current_file).ok()?;

    // Try multiple strategies to find the base expression's record type.
    // The type checker may corrupt types when the parser combines record accesses
    // across declaration boundaries, so we try several approaches.
    // Binder/annotation types are preferred over expression types because the
    // parser may combine `ctx.todoId` across lines, corrupting the expression type.
    let base_type = None
        // Strategy 1: annotation type from the enclosing function's signature.
        .or_else(|| {
            let t = annotation_parameter_type(context, dot_start, &base_name)?;
            sources::extract_record_fields(context.engine, t).is_some().then_some(t)
        })
        // Strategy 2: binder type (from do-bind, function param, etc.)
        .or_else(|| lookup_binder_type_scoped(&checked, &lowered, context, &access, &base_name))
        // Strategy 3: expression type from the checked module.
        .or_else(|| {
            let expr_ptr = AstPtr::new(&expression);
            let expr_id = context.stabilized.lookup_ptr(&expr_ptr)?;
            let t = checked.nodes.lookup_expression(expr_id)?;
            sources::extract_record_fields(context.engine, t).is_some().then_some(t)
        })
        // Strategy 4: global binder search (finds matching name from any scope).
        // If there are completed labels, prefer binders whose record type contains those labels.
        .or_else(|| {
            let mut fallback = None;
            for (_, graph_node) in lowered.graph.iter() {
                let candidate = match graph_node {
                    GraphNode::Binder { binders, .. } => binders
                        .iter()
                        .find(|(n, _)| **n == base_name)
                        .and_then(|(_, id)| checked.nodes.lookup_binder(*id)),
                    GraphNode::Let { bindings, .. } => bindings
                        .iter()
                        .find(|(n, _)| **n == base_name)
                        .and_then(|(_, id)| checked.nodes.lookup_let(*id)),
                    _ => None,
                };
                let Some(tid) = candidate else { continue };
                if sources::extract_record_fields(context.engine, tid).is_none() {
                    continue;
                }
                if completed.is_empty() {
                    fallback = fallback.or(Some(tid));
                    continue;
                }
                // Validate that the record contains all completed labels.
                let valid = completed.iter().all(|label| {
                    let current = tid;
                    // drill to the label
                    sources::extract_record_fields(context.engine, current)
                        .and_then(|fields| fields.into_iter().find(|(l, _)| l == label))
                        .is_some()
                });
                if valid {
                    return Some(tid);
                }
                fallback = fallback.or(Some(tid));
            }
            fallback
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
    eprintln!("CST: base_name={base_name} chain={chain:?} rhs_expr_id={rhs_expr_id:?}");
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

fn lookup_binder_type_scoped(
    checked: &checking::CheckedModule,
    lowered: &lowering::LoweredModule,
    context: &Context,
    access: &cst::ExpressionRecordAccess,
    name: &str,
) -> Option<TypeId> {
    for ancestor in access.syntax().ancestors() {
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
            if let Some(tid) = candidate
                && sources::extract_record_fields(context.engine, tid).is_some()
            {
                return Some(tid);
            }
        }
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
