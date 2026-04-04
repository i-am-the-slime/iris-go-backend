use async_lsp::lsp_types::*;
use building::QueryEngine;
use checking::ExternalQueries;
use checking::core::{Type, TypeId};
use files::{FileId, Files};
use lowering::{ExpressionKind, TermVariableResolution};
use rowan::ast::AstNode;
use rowan::TextSize;
use syntax::cst;
use syntax::SyntaxToken;

use crate::AnalyzerError;
use crate::locate;

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

    let resolved = tokens.iter()
        .find_map(|token| find_application(token, &stabilized, engine, current_file, offset))
        .or_else(|| tokens.iter()
            .find_map(|token| find_standalone_function(token, &stabilized, engine, current_file)));

    let (file_id, term_id, active_parameter) =
        resolved.ok_or(AnalyzerError::NonFatal)?;

    let checked = engine.checked(file_id)?;
    let type_id = checked.terms.get(&term_id).copied().ok_or(AnalyzerError::NonFatal)?;

    let (params, _) = collect_function_params(engine, type_id);
    if params.is_empty() {
        return Ok(None);
    }

    let indexed = engine.indexed(file_id)?;
    let name = indexed.items[term_id]
        .name
        .as_ref()
        .ok_or(AnalyzerError::NonFatal)?
        .to_string();

    let label = checking::core::pretty::Pretty::new(engine, &checked)
        .signature(&name)
        .render(type_id)
        .to_string();

    let parameters: Vec<ParameterInformation> = params
        .iter()
        .map(|&param_id| {
            let rendered = checking::core::pretty::Pretty::new(engine, &checked)
                .render(param_id)
                .to_string();
            ParameterInformation {
                label: ParameterLabel::Simple(rendered),
                documentation: None,
            }
        })
        .collect();

    let active_parameter = active_parameter.min(parameters.len() as u32 - 1);

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

/// Find signature help when cursor is inside an ExpressionApplicationChain.
fn find_application(
    token: &SyntaxToken,
    stabilized: &stabilizing::StabilizedModule,
    engine: &QueryEngine,
    current_file: FileId,
    cursor_offset: TextSize,
) -> Option<(FileId, indexing::TermItemId, u32)> {
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
    let (file_id, term_id) = resolve_function(engine, current_file, function_id).ok()?;

    let active = active_param_from_cst(&app_chain, cursor_offset);

    Some((file_id, term_id, active))
}

/// Determine active parameter from the cursor position relative to
/// the term arguments in the CST. Cursor past an argument's end
/// means we've moved on to the next parameter.
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

/// Find signature help when cursor is on or after a standalone variable/constructor
/// that has a function type (e.g. `fromMaybe ` with no args yet).
fn find_standalone_function(
    token: &SyntaxToken,
    stabilized: &stabilizing::StabilizedModule,
    engine: &QueryEngine,
    current_file: FileId,
) -> Option<(FileId, indexing::TermItemId, u32)> {
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

    let (file_id, term_id) = match kind {
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

    Some((file_id, term_id, 0))
}

fn resolve_function(
    engine: &QueryEngine,
    current_file: FileId,
    function_id: lowering::ExpressionId,
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
