use super::packages::Spelling;
use super::{DataKind, Emitter, call, field, identifier_expression};
use crate::error::GoResult;
use crate::monotype::{DataType, MonotypeId};
use crate::syntax::{GoCase, GoDeclaration, GoDefault, GoExpression, GoStatement};

impl<'q, Q> Emitter<'_, '_, 'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn erase_existential(
        &mut self,
        value: GoExpression,
        from: MonotypeId,
        data: &DataType,
        to: MonotypeId,
    ) -> GoResult<GoExpression> {
        if let Some(name) = self.converters.get(&(from, to)) {
            return Ok(call(identifier_expression(name), vec![value]));
        }
        let name = self.global_name(Spelling::Base("convert".into()));
        self.converters.insert((from, to), name.clone());
        let parameter_type = self.go_type(from)?;
        let result_type = self.go_type(to)?;
        let layout = self.data_layout(data)?;
        let parameter = identifier_expression("value");
        let mut cases = vec![];
        for constructor in &layout.constructors {
            let mut statements = vec![];
            for (slot, payload) in &constructor.fields {
                let hidden = field(parameter.clone(), slot);
                let erased = self.coerce(hidden, *payload, to, &mut statements)?;
                statements.push(GoStatement::Return(Some(erased)));
            }
            cases.push(GoCase {
                values: vec![identifier_expression(&constructor.tag)],
                body: statements,
                line: None,
            });
        }
        let body = match (layout.kind, cases.as_mut_slice()) {
            (_, []) => vec![GoStatement::Return(Some(identifier_expression("nil")))],
            (DataKind::Product, [case]) => std::mem::take(&mut case.body),
            (DataKind::Sentinel, _) => {
                let last = cases.len() - 1;
                let mut body = vec![];
                for (index, case) in cases.iter_mut().enumerate() {
                    let then = std::mem::take(&mut case.body);
                    match self.constructor_test(&layout, index, parameter.clone()) {
                        Some(condition) if index < last => {
                            body.push(GoStatement::If { condition, then, otherwise: vec![] })
                        }
                        _ => body.extend(then),
                    }
                }
                body
            }
            _ => {
                let default = GoDefault::covering(&mut cases);
                let tag = field(parameter, "Tag");
                vec![GoStatement::Switch { value: Some(tag), cases, default: Some(default) }]
            }
        };
        self.type_declarations.push(GoDeclaration::Function {
            name: name.clone(),
            parameters: vec![("value".into(), parameter_type)],
            result: Some(result_type),
            body,
        });
        Ok(call(identifier_expression(&name), vec![value]))
    }
}
