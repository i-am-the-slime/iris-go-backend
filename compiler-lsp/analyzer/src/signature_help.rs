use async_lsp::lsp_types::*;
use building::QueryEngine;
use checking::ExternalQueries;
use checking::core::{Type, TypeId};
use files::{FileId, Files};
use lowering::{ExpressionArgument, ExpressionKind, TermVariableResolution};
use rowan::ast::AstNode;

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
    let token = match node.token_at_offset(offset) {
        rowan::TokenAtOffset::None => return Ok(None),
        rowan::TokenAtOffset::Single(t) => t,
        rowan::TokenAtOffset::Between(_, right) => right,
    };

    let expression = token
        .parent_ancestors()
        .find_map(|node| {
            syntax::cst::ExpressionApplicationChain::cast(node.clone())?;
            syntax::cst::Expression::cast(node)
        })
        .ok_or(AnalyzerError::NonFatal)?;

    let application_ptr = rowan::ast::AstPtr::new(&expression);
    let expression_id = stabilized
        .lookup_ptr(&application_ptr)
        .ok_or(AnalyzerError::NonFatal)?;

    let lowered = engine.lowered(current_file)?;
    let kind = lowered
        .info
        .get_expression_kind(expression_id)
        .ok_or(AnalyzerError::NonFatal)?;

    let ExpressionKind::Application { function, arguments } = kind else {
        return Ok(None);
    };

    let function_id = function.ok_or(AnalyzerError::NonFatal)?;
    let (file_id, term_id) =
        resolve_function(engine, current_file, function_id)?;

    let checked = engine.checked(file_id)?;
    let type_id = checked.terms.get(&term_id).copied().ok_or(AnalyzerError::NonFatal)?;

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

    let (params, _) = collect_function_params(engine, type_id);

    let param_labels: Vec<ParameterLabel> = params
        .iter()
        .map(|&param_id| {
            let rendered = checking::core::pretty::Pretty::new(engine, &checked)
                .render(param_id)
                .to_string();
            ParameterLabel::Simple(rendered)
        })
        .collect();

    let parameters: Vec<ParameterInformation> = param_labels
        .into_iter()
        .map(|label| ParameterInformation { label, documentation: None })
        .collect();

    let active_parameter = count_applied_term_args(arguments);

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

fn count_applied_term_args(arguments: &[ExpressionArgument]) -> u32 {
    arguments
        .iter()
        .filter(|arg| matches!(arg, ExpressionArgument::Term(_)))
        .count() as u32
}
