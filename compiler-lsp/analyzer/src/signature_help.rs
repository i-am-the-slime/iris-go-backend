use async_lsp::lsp_types::*;
use building::QueryEngine;
use checking::ExternalQueries;
use checking::core::{Name, Type, TypeId};
use files::{FileId, Files};
use lowering::{ExpressionId, ExpressionKind, TermVariableResolution};
use rowan::ast::AstNode;
use rowan::TextSize;
use rustc_hash::FxHashMap;
use syntax::cst;
use syntax::SyntaxToken;

use crate::AnalyzerError;
use crate::locate;

struct Resolved {
    def_file: FileId,
    term_id: indexing::TermItemId,
    /// ExpressionIds of applied term arguments (for type inference).
    applied_args: Vec<ExpressionId>,
    active_parameter: u32,
}

pub fn implementation(
    engine: &QueryEngine,
    files: &Files,
    uri: Url,
    position: Position,
) -> Result<Option<SignatureHelp>, AnalyzerError> {
    let current_file = {
        let uri = uri.as_str();
        files.id(uri).ok_or(AnalyzerError::NonFatal)?
    };

    let content = engine.content(current_file);
    let (parsed, _) = engine.parsed(current_file)?;
    let stabilized = engine.stabilized(current_file)?;

    let offset =
        locate::position_to_offset(&content, position).ok_or(AnalyzerError::NonFatal)?;

    let node = parsed.syntax_node();
    let tokens: Vec<SyntaxToken> = match node.token_at_offset(offset) {
        rowan::TokenAtOffset::None => return Ok(None),
        rowan::TokenAtOffset::Single(t) => vec![t],
        rowan::TokenAtOffset::Between(left, right) => vec![left, right],
    };

    let preceding_tokens: Vec<SyntaxToken> = tokens.iter()
        .filter_map(|t| prev_meaningful_token(t))
        .collect();

    let all_tokens: Vec<&SyntaxToken> = tokens.iter()
        .chain(preceding_tokens.iter())
        .collect();

    let resolved = all_tokens.iter()
        .find_map(|token| find_application(token, &stabilized, engine, current_file, offset))
        .or_else(|| all_tokens.iter()
            .find_map(|token| find_standalone_function(token, &stabilized, engine, current_file)));

    let resolved = resolved.ok_or(AnalyzerError::NonFatal)?;

    let current_checked = engine.checked(current_file)?;
    let def_checked = engine.checked(resolved.def_file)?;

    let declared_type_id = def_checked.terms.get(&resolved.term_id)
        .copied()
        .ok_or(AnalyzerError::NonFatal)?;

    let (declared_params, _) = collect_function_params(engine, declared_type_id);
    if declared_params.is_empty() {
        return Ok(None);
    }

    // Try to specialize by matching declared param types against inferred arg types.
    let specialized = specialize_from_args(
        engine, &current_checked, &resolved.applied_args, declared_type_id,
    );

    let type_id = specialized.unwrap_or(declared_type_id);

    // Choose the right checked module for rendering.
    let render_checked = if specialized.is_some() { &current_checked } else { &def_checked };

    let (params, _) = collect_function_params(engine, type_id);

    let indexed = engine.indexed(resolved.def_file)?;
    let name = indexed.items[resolved.term_id]
        .name
        .as_ref()
        .ok_or(AnalyzerError::NonFatal)?
        .to_string();

    let label = checking::core::pretty::Pretty::new(engine, render_checked)
        .signature(&name)
        .render(type_id)
        .to_string();

    let parameters: Vec<ParameterInformation> = find_param_offsets(&label, params.len())
        .into_iter()
        .map(|(start, end)| ParameterInformation {
            label: ParameterLabel::LabelOffsets([start as u32, end as u32]),
            documentation: None,
        })
        .collect();

    let active_parameter = resolved.active_parameter.min(
        parameters.len().saturating_sub(1) as u32,
    );

    let signature = SignatureInformation {
        label,
        documentation: None,
        parameters: Some(parameters),
        active_parameter: Some(active_parameter),
    };

    Ok(Some(SignatureHelp {
        signatures: vec![signature],
        active_signature: Some(0),
        active_parameter: Some(active_parameter),
    }))
}

/// Build a substitution from Rigid type variables to concrete types
/// by matching declared parameter types against inferred argument types.
/// Then apply the substitution to the declared type.
fn specialize_from_args(
    engine: &QueryEngine,
    checked: &checking::CheckedModule,
    applied_args: &[ExpressionId],
    declared_type_id: TypeId,
) -> Option<TypeId> {
    if applied_args.is_empty() {
        return None;
    }

    let (declared_params, _) = collect_function_params(engine, declared_type_id);

    let mut subst: FxHashMap<Name, TypeId> = FxHashMap::default();

    for (i, arg_id) in applied_args.iter().enumerate() {
        let arg_type = checked.nodes.expressions.get(arg_id).copied()?;
        if has_unification_vars(engine, arg_type) {
            return None;
        }
        if let Some(declared_param) = declared_params.get(i) {
            collect_substitution(engine, *declared_param, arg_type, &mut subst);
        }
    }

    if subst.is_empty() {
        return None;
    }

    Some(apply_substitution(engine, declared_type_id, &subst))
}

/// Match a declared parameter type against a concrete argument type
/// to discover what Rigid type variables map to.
fn collect_substitution(
    engine: &QueryEngine,
    declared: TypeId,
    concrete: TypeId,
    subst: &mut FxHashMap<Name, TypeId>,
) {
    match engine.lookup_type(declared) {
        Type::Rigid(name, _, _) => {
            subst.entry(name).or_insert(concrete);
        }
        Type::Application(df, da) => {
            if let Type::Application(cf, ca) = engine.lookup_type(concrete) {
                collect_substitution(engine, df, cf, subst);
                collect_substitution(engine, da, ca, subst);
            }
        }
        Type::Function(da, dr) => {
            if let Type::Function(ca, cr) = engine.lookup_type(concrete) {
                collect_substitution(engine, da, ca, subst);
                collect_substitution(engine, dr, cr, subst);
            }
        }
        _ => {}
    }
}

/// Replace Rigid type variables with their substituted types.
fn apply_substitution(
    engine: &QueryEngine,
    type_id: TypeId,
    subst: &FxHashMap<Name, TypeId>,
) -> TypeId {
    match engine.lookup_type(type_id) {
        Type::Rigid(name, _, _) => {
            if let Some(&replacement) = subst.get(&name) {
                replacement
            } else {
                type_id
            }
        }
        Type::Forall(binder_id, inner) => {
            let inner = apply_substitution(engine, inner, subst);
            // Check if this forall variable is fully substituted
            let binder = engine.lookup_forall_binder(binder_id);
            let name = checking::core::Name { file: binder.name.file, unique: binder.name.unique };
            if subst.contains_key(&name) {
                // Skip the forall — the variable is now concrete
                inner
            } else {
                engine.intern_type(Type::Forall(binder_id, inner))
            }
        }
        Type::Function(arg, result) => {
            let arg = apply_substitution(engine, arg, subst);
            let result = apply_substitution(engine, result, subst);
            engine.intern_type(Type::Function(arg, result))
        }
        Type::Application(f, a) => {
            let f = apply_substitution(engine, f, subst);
            let a = apply_substitution(engine, a, subst);
            engine.intern_type(Type::Application(f, a))
        }
        Type::Constrained(c, inner) => {
            let c = apply_substitution(engine, c, subst);
            let inner = apply_substitution(engine, inner, subst);
            engine.intern_type(Type::Constrained(c, inner))
        }
        _ => type_id,
    }
}

fn find_application(
    token: &SyntaxToken,
    stabilized: &stabilizing::StabilizedModule,
    engine: &QueryEngine,
    current_file: FileId,
    cursor_offset: TextSize,
) -> Option<Resolved> {
    let app_chain = token
        .parent_ancestors()
        .find_map(cst::ExpressionApplicationChain::cast)?;

    let app_expr = token
        .parent_ancestors()
        .find_map(|node| {
            cst::ExpressionApplicationChain::cast(node.clone())?;
            cst::Expression::cast(node)
        })?;

    let ptr = rowan::ast::AstPtr::new(&app_expr);
    let expression_id = stabilized.lookup_ptr(&ptr)?;

    let lowered = engine.lowered(current_file).ok()?;
    let kind = lowered.info.get_expression_kind(expression_id)?;

    let ExpressionKind::Application { function, arguments } = kind else {
        return None;
    };

    let function_id = (*function)?;
    let (def_file, term_id) = resolve_function(engine, current_file, function_id).ok()?;
    let active_parameter = active_param_from_cst(&app_chain, cursor_offset);

    let applied_args: Vec<ExpressionId> = arguments.iter()
        .filter_map(|arg| match arg {
            lowering::ExpressionArgument::Term(id) => *id,
            lowering::ExpressionArgument::Type(_) => None,
        })
        .collect();

    Some(Resolved { def_file, term_id, applied_args, active_parameter })
}

fn active_param_from_cst(
    app_chain: &cst::ExpressionApplicationChain,
    cursor_offset: TextSize,
) -> u32 {
    let mut active = 0u32;

    for arg in app_chain.children() {
        if let cst::ExpressionArgument::ExpressionTermArgument(ref term_arg) = arg {
            let arg_end = term_arg.syntax().text_range().end();
            if cursor_offset > arg_end {
                active += 1;
            }
        }
    }

    active
}

fn find_standalone_function(
    token: &SyntaxToken,
    stabilized: &stabilizing::StabilizedModule,
    engine: &QueryEngine,
    current_file: FileId,
) -> Option<Resolved> {
    let expression = token.parent_ancestors().find_map(|node| {
        let expr = cst::Expression::cast(node)?;
        match &expr {
            cst::Expression::ExpressionVariable(_) | cst::Expression::ExpressionConstructor(_) => {
                Some(expr)
            }
            _ => None,
        }
    })?;

    let ptr = rowan::ast::AstPtr::new(&expression);
    let expression_id = stabilized.lookup_ptr(&ptr)?;

    let lowered = engine.lowered(current_file).ok()?;
    let kind = lowered.info.get_expression_kind(expression_id)?;

    let (def_file, term_id) = match kind {
        ExpressionKind::Variable { resolution, .. } => {
            let resolution = resolution.as_ref()?;
            match resolution {
                TermVariableResolution::Reference(f_id, t_id) => Some((*f_id, *t_id)),
                _ => None,
            }
        }
        ExpressionKind::Constructor { resolution, .. } => {
            let (f_id, t_id) = resolution.as_ref()?;
            Some((*f_id, *t_id))
        }
        _ => None,
    }?;

    Some(Resolved { def_file, term_id, applied_args: vec![], active_parameter: 0 })
}

fn resolve_function(
    engine: &QueryEngine,
    current_file: FileId,
    function_id: ExpressionId,
) -> Result<(FileId, indexing::TermItemId), AnalyzerError> {
    let lowered = engine.lowered(current_file)?;
    let kind = lowered
        .info
        .get_expression_kind(function_id)
        .ok_or(AnalyzerError::NonFatal)?;

    match kind {
        ExpressionKind::Variable { resolution, .. } => {
            let resolution = resolution.as_ref().ok_or(AnalyzerError::NonFatal)?;
            match resolution {
                TermVariableResolution::Reference(f_id, t_id) => Ok((*f_id, *t_id)),
                _ => Err(AnalyzerError::NonFatal),
            }
        }
        ExpressionKind::Constructor { resolution, .. } => {
            let (f_id, t_id) = resolution.as_ref().ok_or(AnalyzerError::NonFatal)?;
            Ok((*f_id, *t_id))
        }
        _ => Err(AnalyzerError::NonFatal),
    }
}

fn find_param_offsets(label: &str, param_count: usize) -> Vec<(usize, usize)> {
    let type_start = label.find(":: ").map(|i| i + 3).unwrap_or(0);
    let after_forall = skip_forall_prefix(label, type_start);
    let after_constraints = skip_constraints(label, after_forall);

    let mut offsets = vec![];
    let mut pos = after_constraints;
    let bytes = label.as_bytes();

    for _ in 0..param_count {
        while pos < bytes.len() && (bytes[pos] == b' ' || bytes[pos] == b'\n') {
            pos += 1;
        }
        let param_start = pos;

        let mut depth = 0usize;
        while pos < bytes.len() {
            match bytes[pos] {
                b'(' | b'{' => depth += 1,
                b')' | b'}' => depth = depth.saturating_sub(1),
                b'-' if depth == 0
                    && pos + 2 < bytes.len()
                    && bytes[pos + 1] == b'>'
                    && (pos == 0 || bytes[pos - 1] == b' ')
                    && (pos + 2 >= bytes.len() || bytes[pos + 2] == b' ' || bytes[pos + 2] == b'\n') =>
                {
                    let param_end = pos - 1;
                    offsets.push((param_start, param_end));
                    pos += 3;
                    break;
                }
                _ => {}
            }
            pos += 1;
        }

        if offsets.len() < offsets.capacity() && pos >= bytes.len() {
            break;
        }
    }

    offsets
}

fn skip_forall_prefix(label: &str, start: usize) -> usize {
    let rest = &label[start..];
    if let Some(stripped) = rest.strip_prefix("forall ") {
        let offset_in_rest = label.len() - stripped.len();
        if let Some(dot_pos) = label[offset_in_rest..].find(". ") {
            return offset_in_rest + dot_pos + 2;
        }
    }
    start
}

fn skip_constraints(label: &str, start: usize) -> usize {
    let mut pos = start;
    loop {
        let rest = &label[pos..];
        if let Some(arrow_pos) = rest.find(" => ") {
            pos = pos + arrow_pos + 4;
        } else {
            break;
        }
    }
    pos
}

fn prev_meaningful_token(token: &SyntaxToken) -> Option<SyntaxToken> {
    let mut current = token.prev_token()?;
    while current.kind().is_layout_token() {
        current = current.prev_token()?;
    }
    Some(current)
}

fn has_unification_vars(engine: &QueryEngine, type_id: TypeId) -> bool {
    match engine.lookup_type(type_id) {
        Type::Unification(_) => true,
        Type::Function(a, b) | Type::Application(a, b) | Type::KindApplication(a, b) => {
            has_unification_vars(engine, a) || has_unification_vars(engine, b)
        }
        Type::Forall(_, inner) | Type::Constrained(_, inner) | Type::Kinded(inner, _) => {
            has_unification_vars(engine, inner)
        }
        _ => false,
    }
}

fn collect_function_params(engine: &QueryEngine, mut type_id: TypeId) -> (Vec<TypeId>, TypeId) {
    let mut params = vec![];
    loop {
        match engine.lookup_type(type_id) {
            Type::Forall(_, inner) => type_id = inner,
            Type::Constrained(_, inner) => type_id = inner,
            Type::Function(arg, result) => {
                params.push(arg);
                type_id = result;
            }
            _ => break,
        }
    }
    (params, type_id)
}
