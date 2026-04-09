use async_lsp::lsp_types::*;
use building::QueryEngine;
use checking::ExternalQueries;
use checking::core::{Name, Type, TypeId};
use files::{FileId, Files};
use lowering::{ExpressionId, ExpressionKind, TermVariableResolution};
use rowan::TextSize;
use rowan::ast::AstNode;
use rustc_hash::FxHashMap;
use syntax::SyntaxToken;
use syntax::cst;

use crate::AnalyzerError;
use crate::locate;

struct Resolved {
    def_file: FileId,
    term_id: indexing::TermItemId,
    /// ExpressionIds of term arguments applied before the piped position.
    applied_args: Vec<ExpressionId>,
    /// ExpressionIds of term arguments applied after the piped position.
    outer_args: Vec<ExpressionId>,
    active_parameter: u32,
    /// Type of the piped-in argument from an operator chain (e.g. `a # f`).
    piped_type: Option<TypeId>,
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

    let offset = locate::position_to_offset(&content, position).ok_or(AnalyzerError::NonFatal)?;

    let node = parsed.syntax_node();
    let tokens: Vec<SyntaxToken> = match node.token_at_offset(offset) {
        rowan::TokenAtOffset::None => return Ok(None),
        rowan::TokenAtOffset::Single(t) => vec![t],
        rowan::TokenAtOffset::Between(left, right) => vec![left, right],
    };

    let preceding_tokens: Vec<SyntaxToken> =
        tokens.iter().filter_map(prev_meaningful_token).collect();

    let all_tokens: Vec<&SyntaxToken> = tokens.iter().chain(preceding_tokens.iter()).collect();

    let resolved = all_tokens
        .iter()
        .find_map(|token| find_in_operator_chain(token, &stabilized, engine, current_file, offset))
        .or_else(|| {
            all_tokens.iter().find_map(|token| {
                find_application(token, &stabilized, engine, current_file, offset)
            })
        })
        .or_else(|| {
            all_tokens.iter().find_map(|token| {
                find_standalone_function(token, &stabilized, engine, current_file)
            })
        });

    let resolved = resolved.ok_or(AnalyzerError::NonFatal)?;

    let current_checked = engine.checked(current_file)?;
    let def_checked = engine.checked(resolved.def_file)?;

    let declared_type_id =
        def_checked.terms.get(&resolved.term_id).copied().ok_or(AnalyzerError::NonFatal)?;

    let (declared_params, _) = collect_function_params(engine, declared_type_id);
    if declared_params.is_empty() {
        return Ok(None);
    }

    // Try to specialize by matching declared param types against inferred arg types.
    let specialized = specialize_from_args(
        engine,
        &current_checked,
        &resolved.applied_args,
        resolved.piped_type,
        &resolved.outer_args,
        declared_type_id,
    );

    let type_id = specialized.unwrap_or(declared_type_id);

    // Choose the right checked module for rendering.
    let render_checked = if specialized.is_some() { &current_checked } else { &def_checked };

    let (params, _) = collect_function_params(engine, type_id);

    let indexed = engine.indexed(resolved.def_file)?;
    let name =
        indexed.items[resolved.term_id].name.as_ref().ok_or(AnalyzerError::NonFatal)?.to_string();

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

    let piped_args = u32::from(resolved.piped_type.is_some());
    let active_parameter = resolved.active_parameter + piped_args;
    if active_parameter as usize >= parameters.len() {
        return Ok(None);
    }

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

/// Parameter layout: applied_args[0..n], piped at n, outer_args[n+1..]
fn specialize_from_args(
    engine: &QueryEngine,
    checked: &checking::CheckedModule,
    applied_args: &[ExpressionId],
    piped_type: Option<TypeId>,
    outer_args: &[ExpressionId],
    declared_type_id: TypeId,
) -> Option<TypeId> {
    if applied_args.is_empty() && piped_type.is_none() && outer_args.is_empty() {
        return None;
    }

    let (declared_params, _) = collect_function_params(engine, declared_type_id);
    let mut subst: FxHashMap<Name, TypeId> = FxHashMap::default();

    for (i, arg_id) in applied_args.iter().enumerate() {
        if let Some(arg_type) = checked.nodes.expressions.get(arg_id).copied()
            && !has_unification_vars(engine, arg_type)
            && let Some(dp) = declared_params.get(i)
        {
            collect_substitution(engine, *dp, arg_type, &mut subst);
        }
    }

    // Piped arg fills the LAST declared param (pipeline convention).
    if let Some(piped) = piped_type
        && !has_unification_vars(engine, piped)
        && let Some(dp) = declared_params.last()
    {
        collect_substitution(engine, *dp, piped, &mut subst);
    }

    let outer_offset = applied_args.len();
    for (i, arg_id) in outer_args.iter().enumerate() {
        if let Some(arg_type) = checked.nodes.expressions.get(arg_id).copied()
            && !has_unification_vars(engine, arg_type)
            && let Some(dp) = declared_params.get(outer_offset + i)
        {
            collect_substitution(engine, *dp, arg_type, &mut subst);
        }
    }

    if subst.is_empty() {
        return None;
    }

    Some(apply_substitution(engine, declared_type_id, &subst))
}

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
            let binder = engine.lookup_forall_binder(binder_id);
            let name = checking::core::Name { file: binder.name.file, unique: binder.name.unique };
            if subst.contains_key(&name) {
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
    let app_chain = token.parent_ancestors().find_map(cst::ExpressionApplicationChain::cast)?;

    let app_expr = token.parent_ancestors().find_map(|node| {
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

    let term_args: Vec<ExpressionId> = arguments
        .iter()
        .filter_map(|arg| match arg {
            lowering::ExpressionArgument::Term(id) => *id,
            lowering::ExpressionArgument::Type(_) => None,
        })
        .collect();

    // Try direct resolution (simple function call).
    if let Ok((def_file, term_id)) = resolve_function(engine, current_file, function_id) {
        let active_parameter = active_param_from_cst(&app_chain, cursor_offset);
        return Some(Resolved {
            def_file,
            term_id,
            applied_args: term_args,
            active_parameter,
            piped_type: None,
            outer_args: vec![],
        });
    }

    // If function is an operator chain (possibly parenthesized), dig into it.
    let mut func_id = function_id;
    loop {
        let fk = lowered.info.get_expression_kind(func_id)?;
        match fk {
            ExpressionKind::Parenthesized { parenthesized } => {
                func_id = (*parenthesized)?;
            }
            _ => break,
        }
    }
    let func_kind = lowered.info.get_expression_kind(func_id)?;
    let ExpressionKind::OperatorChain { head, tail } = func_kind else {
        return None;
    };

    let last_pair = tail.last()?;
    let pair_element_id = last_pair.element?;
    let pair_kind = lowered.info.get_expression_kind(pair_element_id)?;

    let (def_file, term_id, inner_args, inner_count) =
        resolve_pair_function(engine, current_file, pair_kind, &lowered)?;

    let checked = engine.checked(current_file).ok()?;
    let piped_type = head
        .and_then(|h| checked.nodes.expressions.get(&h).copied())
        .filter(|t| !has_unification_vars(engine, *t));

    let outer_count = active_param_from_cst(&app_chain, cursor_offset);
    let active_parameter = inner_count + outer_count;

    Some(Resolved {
        def_file,
        term_id,
        applied_args: inner_args,
        outer_args: term_args,
        active_parameter,
        piped_type,
    })
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

fn find_in_operator_chain(
    token: &SyntaxToken,
    stabilized: &stabilizing::StabilizedModule,
    engine: &QueryEngine,
    current_file: FileId,
    cursor_offset: TextSize,
) -> Option<Resolved> {
    let pair = token.parent_ancestors().find_map(cst::ExpressionOperatorPair::cast)?;

    let chain_expr = token.parent_ancestors().find_map(|node| {
        cst::ExpressionOperatorChain::cast(node.clone())?;
        cst::Expression::cast(node)
    })?;
    let chain = token.parent_ancestors().find_map(cst::ExpressionOperatorChain::cast)?;

    let chain_ptr = rowan::ast::AstPtr::new(&chain_expr);
    let chain_id = stabilized.lookup_ptr(&chain_ptr)?;

    let lowered = engine.lowered(current_file).ok()?;
    let kind = lowered.info.get_expression_kind(chain_id)?;
    let ExpressionKind::OperatorChain { head, tail } = kind else {
        return None;
    };

    let pair_index =
        chain.children().position(|p| p.syntax().text_range() == pair.syntax().text_range())?;

    let op_pair = tail.get(pair_index)?;
    let _op_id = op_pair.id?;
    let pair_element_id = op_pair.element?;

    let pair_kind = lowered.info.get_expression_kind(pair_element_id)?;

    let (def_file, term_id, inner_args, inner_count) =
        resolve_pair_function(engine, current_file, pair_kind, &lowered)?;

    // Check if the operator chain is wrapped in a parent application chain.
    // e.g. `(Just 12 # fromMaybe) 0` where `0` is an outer arg.
    let (outer_args, outer_count) = find_outer_args(&chain, stabilized, &lowered, cursor_offset);

    let checked = engine.checked(current_file).ok()?;
    let piped_type = if pair_index == 0 {
        let head_id = (*head)?;
        let direct = checked.nodes.expressions.get(&head_id).copied();
        match direct {
            Some(t) if !has_unification_vars(engine, t) => Some(t),
            _ => infer_result_type(engine, &checked, current_file, &lowered, head_id),
        }
    } else {
        let prev_op_id = tail.get(pair_index - 1)?.id?;
        checked
            .nodes
            .lookup_term_operator(prev_op_id)
            .map(|b| b.result)
            .filter(|t| !has_unification_vars(engine, *t))
    };

    let active_parameter = inner_count + outer_count;

    Some(Resolved {
        def_file,
        term_id,
        applied_args: inner_args,
        outer_args,
        active_parameter,
        piped_type,
    })
}

/// Resolve the function from a pair element (variable, constructor, or application).
fn resolve_pair_function(
    engine: &QueryEngine,
    current_file: FileId,
    pair_kind: &ExpressionKind,
    _lowered: &lowering::LoweredModule,
) -> Option<(FileId, indexing::TermItemId, Vec<ExpressionId>, u32)> {
    match pair_kind {
        ExpressionKind::Application { function, arguments } => {
            let function_id = (*function)?;
            let (df, ti) = resolve_function(engine, current_file, function_id).ok()?;
            let args: Vec<ExpressionId> = arguments
                .iter()
                .filter_map(|arg| match arg {
                    lowering::ExpressionArgument::Term(id) => *id,
                    lowering::ExpressionArgument::Type(_) => None,
                })
                .collect();
            let count = args.len() as u32;
            Some((df, ti, args, count))
        }
        ExpressionKind::Variable { resolution, .. } => {
            let resolution = resolution.as_ref()?;
            match resolution {
                TermVariableResolution::Reference(f_id, t_id) => Some((*f_id, *t_id, vec![], 0u32)),
                _ => None,
            }
        }
        ExpressionKind::Constructor { resolution, .. } => {
            let (f_id, t_id) = resolution.as_ref()?;
            Some((*f_id, *t_id, vec![], 0u32))
        }
        _ => None,
    }
}

/// When an operator chain is the function in a parent application,
/// collect those outer arguments and cursor-based active count.
fn find_outer_args(
    chain: &cst::ExpressionOperatorChain,
    stabilized: &stabilizing::StabilizedModule,
    lowered: &lowering::LoweredModule,
    cursor_offset: TextSize,
) -> (Vec<ExpressionId>, u32) {
    let result = (|| {
        // Walk up past possible wrapper nodes (Expression, Parenthesized).
        let mut node = chain.syntax().parent()?;
        while cst::ExpressionParenthesized::cast(node.clone()).is_some() {
            node = node.parent()?;
        }
        let outer_app = cst::ExpressionApplicationChain::cast(node.clone())?;
        let outer_expr = cst::Expression::cast(node)?;
        let ptr = rowan::ast::AstPtr::new(&outer_expr);
        let outer_id = stabilized.lookup_ptr(&ptr)?;
        let kind = lowered.info.get_expression_kind(outer_id)?;
        let ExpressionKind::Application { arguments, .. } = kind else {
            return None;
        };
        let args: Vec<ExpressionId> = arguments
            .iter()
            .filter_map(|arg| match arg {
                lowering::ExpressionArgument::Term(id) => *id,
                lowering::ExpressionArgument::Type(_) => None,
            })
            .collect();
        let cst_active = active_param_from_cst(&outer_app, cursor_offset);
        Some((args, cst_active))
    })();
    result.unwrap_or((vec![], 0))
}

/// Infer the result type of an expression by looking at its declared type
/// and concrete argument types. Used when checked.nodes.expressions has
/// unresolved unification variables.
fn infer_result_type(
    engine: &QueryEngine,
    checked: &checking::CheckedModule,
    current_file: FileId,
    lowered: &lowering::LoweredModule,
    expr_id: ExpressionId,
) -> Option<TypeId> {
    let kind = lowered.info.get_expression_kind(expr_id)?;
    let (func_id, arguments) = match kind {
        ExpressionKind::Application { function, arguments } => ((*function)?, arguments),
        ExpressionKind::Constructor { resolution, .. } => {
            let (f_id, t_id) = resolution.as_ref()?;
            let def_checked = engine.checked(*f_id).ok()?;
            return def_checked.terms.get(t_id).copied();
        }
        _ => return None,
    };

    let (def_file, term_id) = resolve_function(engine, current_file, func_id).ok()?;
    let def_checked = engine.checked(def_file).ok()?;
    let declared_type = def_checked.terms.get(&term_id).copied()?;

    let term_args: Vec<ExpressionId> = arguments
        .iter()
        .filter_map(|arg| match arg {
            lowering::ExpressionArgument::Term(id) => *id,
            lowering::ExpressionArgument::Type(_) => None,
        })
        .collect();

    if term_args.is_empty() {
        return Some(declared_type);
    }

    let (params, _) = collect_function_params(engine, declared_type);
    let mut subst: FxHashMap<Name, TypeId> = FxHashMap::default();

    for (i, arg_id) in term_args.iter().enumerate() {
        let arg_type = checked.nodes.expressions.get(arg_id).copied()?;
        if has_unification_vars(engine, arg_type) {
            return None;
        }
        if let Some(dp) = params.get(i) {
            collect_substitution(engine, *dp, arg_type, &mut subst);
        }
    }

    let specialized = if subst.is_empty() {
        declared_type
    } else {
        apply_substitution(engine, declared_type, &subst)
    };

    // Skip consumed params to get the result type.
    let mut result = specialized;
    let mut remaining = term_args.len();
    loop {
        match engine.lookup_type(result) {
            Type::Forall(_, inner) | Type::Constrained(_, inner) => result = inner,
            Type::Function(_, ret) if remaining > 0 => {
                remaining -= 1;
                result = ret;
            }
            _ => break,
        }
    }

    Some(result)
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

    Some(Resolved {
        def_file,
        term_id,
        applied_args: vec![],
        outer_args: vec![],
        active_parameter: 0,
        piped_type: None,
    })
}

fn resolve_function(
    engine: &QueryEngine,
    current_file: FileId,
    function_id: ExpressionId,
) -> Result<(FileId, indexing::TermItemId), AnalyzerError> {
    let lowered = engine.lowered(current_file)?;
    let kind = lowered.info.get_expression_kind(function_id).ok_or(AnalyzerError::NonFatal)?;

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
                    && (pos + 2 >= bytes.len()
                        || bytes[pos + 2] == b' '
                        || bytes[pos + 2] == b'\n') =>
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

/// Returns the expected parameter type at the given cursor offset, if the cursor
/// is in an argument position of a function application. Returns `None` if the
/// expected type contains rigid variables (fully generic — no sorting signal).
pub fn expected_type_at(
    engine: &QueryEngine,
    current_file: FileId,
    offset: TextSize,
) -> Option<TypeId> {
    let (parsed, _) = engine.parsed(current_file).ok()?;
    let stabilized = engine.stabilized(current_file).ok()?;

    let node = parsed.syntax_node();
    let tokens: Vec<SyntaxToken> = match node.token_at_offset(offset) {
        rowan::TokenAtOffset::None => return None,
        rowan::TokenAtOffset::Single(t) => vec![t],
        rowan::TokenAtOffset::Between(left, right) => vec![left, right],
    };

    let preceding_tokens: Vec<SyntaxToken> =
        tokens.iter().filter_map(prev_meaningful_token).collect();

    let all_tokens: Vec<&SyntaxToken> = tokens.iter().chain(preceding_tokens.iter()).collect();

    let resolved = all_tokens
        .iter()
        .find_map(|token| find_in_operator_chain(token, &stabilized, engine, current_file, offset))
        .or_else(|| {
            all_tokens.iter().find_map(|token| {
                find_application(token, &stabilized, engine, current_file, offset)
            })
        })
        .or_else(|| {
            all_tokens.iter().find_map(|token| {
                find_standalone_function(token, &stabilized, engine, current_file)
            })
        })?;

    let current_checked = engine.checked(current_file).ok()?;
    let def_checked = engine.checked(resolved.def_file).ok()?;

    let declared_type_id = def_checked.terms.get(&resolved.term_id).copied()?;

    let specialized = specialize_from_args(
        engine,
        &current_checked,
        &resolved.applied_args,
        resolved.piped_type,
        &resolved.outer_args,
        declared_type_id,
    );

    let type_id = specialized.unwrap_or(declared_type_id);

    let (params, _) = collect_function_params(engine, type_id);
    let param_type = params.get(resolved.active_parameter as usize).copied()?;

    if has_rigid_vars(engine, param_type) {
        return None;
    }

    Some(param_type)
}

/// Checks whether a candidate type could fill a position expecting `expected`.
/// Strips Forall, Constrained, and Function arrows from the candidate to get
/// its result type, then checks structural equality.
pub fn type_matches(engine: &QueryEngine, expected: TypeId, candidate_type: TypeId) -> bool {
    let result = result_type(engine, candidate_type);

    if has_unification_vars(engine, result) {
        return false;
    }

    types_equal(engine, expected, result)
}

fn result_type(engine: &QueryEngine, mut type_id: TypeId) -> TypeId {
    loop {
        match engine.lookup_type(type_id) {
            Type::Forall(_, inner) | Type::Constrained(_, inner) => type_id = inner,
            Type::Function(_, ret) => type_id = ret,
            _ => return type_id,
        }
    }
}

fn types_equal(engine: &QueryEngine, a: TypeId, b: TypeId) -> bool {
    if a == b {
        return true;
    }
    match (engine.lookup_type(a), engine.lookup_type(b)) {
        (Type::Application(af, aa), Type::Application(bf, ba)) => {
            types_equal(engine, af, bf) && types_equal(engine, aa, ba)
        }
        (Type::Constructor(af, ai), Type::Constructor(bf, bi)) => af == bf && ai == bi,
        (Type::Function(aa, ar), Type::Function(ba, br)) => {
            types_equal(engine, aa, ba) && types_equal(engine, ar, br)
        }
        _ => false,
    }
}

fn has_rigid_vars(engine: &QueryEngine, type_id: TypeId) -> bool {
    match engine.lookup_type(type_id) {
        Type::Rigid(..) => true,
        Type::Function(a, b) | Type::Application(a, b) | Type::KindApplication(a, b) => {
            has_rigid_vars(engine, a) || has_rigid_vars(engine, b)
        }
        Type::Forall(_, inner) | Type::Constrained(_, inner) | Type::Kinded(inner, _) => {
            has_rigid_vars(engine, inner)
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
