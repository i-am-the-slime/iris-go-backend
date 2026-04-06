use async_lsp::lsp_types::*;
use building::QueryEngine;
use checking::ExternalQueries;
use checking::core::{Type, TypeId};
use files::{FileId, Files};
use lowering::{ExpressionId, ExpressionKind, TermVariableResolution};
use rowan::ast::AstNode;
use rowan::TextSize;
use syntax::cst;
use syntax::SyntaxToken;

use crate::AnalyzerError;
use crate::extract::{self, AnnotationSyntaxRange};
use crate::locate;

struct Resolved {
    def_file: FileId,
    term_id: indexing::TermItemId,
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

    // Get the source syntax for the type signature (clean, human-written).
    let (def_root, range) =
        AnnotationSyntaxRange::of_file_term(engine, resolved.def_file, resolved.term_id)?;

    let label = range
        .syntax
        .map(|r| extract::extract_syntax(&def_root, r))
        .ok_or(AnalyzerError::NonFatal)?;

    // Count parameters from the checked type to know how many `->` to look for.
    let def_checked = engine.checked(resolved.def_file)?;
    let type_id = def_checked.terms.get(&resolved.term_id)
        .copied()
        .ok_or(AnalyzerError::NonFatal)?;

    let (params, _) = collect_function_params(engine, type_id);
    if params.is_empty() {
        return Ok(None);
    }

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

    let ExpressionKind::Application { function, .. } = kind else {
        return None;
    };

    let function_id = (*function)?;
    let (def_file, term_id) = resolve_function(engine, current_file, function_id).ok()?;
    let active_parameter = active_param_from_cst(&app_chain, cursor_offset);

    Some(Resolved { def_file, term_id, active_parameter })
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

    Some(Resolved { def_file, term_id, active_parameter: 0 })
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
