//! Data constructors used as values.
//!
//! `k More Done` passes the constructors themselves. Each constructor passed
//! as a value becomes one Go function beside its type,
//!
//! ```go
//! func More(more func(struct{}) StepInt) StepInt { return StepInt{Tag: StepIntMore, More: more} }
//! ```
//!
//! passed by name, instead of a function literal that builds the struct at
//! every use. A constructor applied to all its fields is still a struct
//! literal where it is applied.

use super::packages::Spelling;
use super::{Emitter, identifier_expression, lines};
use crate::error::GoResult;
use crate::monomorphic::{Expression, ExpressionKind, Local};
use crate::monotype::{DataType, MonotypeId};
use crate::naming::{RESERVED, identifier, lower_first};
use crate::syntax::{GoDeclaration, GoExpression, GoStatement};

impl<Q> Emitter<'_, '_, '_, Q>
where
    Q: checking::ExternalQueries,
{
    /// The Go function a lambda is, when it only applies a constructor to its
    /// parameters in order and Go calls it with all of them at once.
    pub(super) fn constructor_as_value(
        &mut self,
        monotype: MonotypeId,
        parameters: &[Local],
        body: &Expression,
    ) -> GoResult<Option<GoExpression>> {
        let (parameters, body) = self.merged_lambda(monotype, parameters, body);
        let ExpressionKind::Construct { data, constructor, arguments } = &body.kind else {
            return Ok(None);
        };
        let applies_parameters = arguments.len() == parameters.len()
            && arguments.iter().zip(&parameters).all(|(argument, parameter)| {
                matches!(argument.kind, ExpressionKind::Local(id) if id == parameter.id)
            });
        if parameters.is_empty() || !applies_parameters || self.arity(monotype) != parameters.len()
        {
            return Ok(None);
        }
        let key = (data.clone(), *constructor, monotype);
        if let Some(name) = self.constructor_functions.get(&key) {
            return Ok(Some(identifier_expression(name)));
        }
        let layout = self.data_layout(data)?;
        if let Some(maybe) = &layout.maybe {
            let name = self.maybe_just_function(&layout, maybe)?;
            self.constructor_functions.insert(key, name.clone());
            return Ok(Some(identifier_expression(&name)));
        }
        let Some(name) =
            self.declare_constructor_function(data, *constructor, &parameters, body)?
        else {
            return Ok(None);
        };
        self.constructor_functions.insert(key, name.clone());
        Ok(Some(identifier_expression(&name)))
    }

    /// The parameters of a lambda and of the lambdas it returns, as far as Go
    /// takes them in one call, and the body they share.
    pub(super) fn merged_lambda<'e>(
        &self,
        monotype: MonotypeId,
        parameters: &[Local],
        mut body: &'e Expression,
    ) -> (Vec<Local>, &'e Expression) {
        let arity = self.arity(monotype);
        let mut merged = parameters.to_vec();
        while merged.len() < arity
            && let ExpressionKind::Lambda { parameters: inner, body: inner_body } = &body.kind
        {
            merged.extend(inner.iter().cloned());
            body = inner_body;
        }
        (merged, body)
    }

    /// Declares `func More(more …) StepInt { return StepInt{…} }` beside the
    /// type: called after the constructor, or after the constructor and its
    /// type where another global has that name.
    fn declare_constructor_function(
        &mut self,
        data: &DataType,
        constructor: usize,
        parameters: &[Local],
        body: &Expression,
    ) -> GoResult<Option<String>> {
        let layout = self.data_layout(data)?;
        let fields = layout.constructors[constructor].fields.clone();
        if fields.len() != parameters.len() {
            return Ok(None);
        }
        let constructors = self
            .monotypes
            .constructors(&mut self.context, data)
            .map_err(|failure| failure.at(&layout.name))?;
        let constructor_name = crate::naming::go_field(&constructors[constructor].name);
        let qualified = format!("{constructor_name}{}", layout.name);
        let name = self.global_name(Spelling::Ladder(vec![constructor_name, qualified]));
        self.homes.insert(name.clone(), data.file_id);
        // The function's locals are its own, apart from the function being emitted.
        let enclosing = std::mem::take(&mut self.local_names);
        let names: Vec<String> = fields
            .iter()
            .enumerate()
            .map(|(position, (field, _))| self.local_name(parameter_name(field, position)))
            .collect();
        self.local_names = enclosing;
        let mut go_parameters = Vec::with_capacity(parameters.len());
        for (name, parameter) in names.iter().zip(parameters) {
            go_parameters.push((name.clone(), self.go_type(parameter.monotype)?));
        }
        let values = names.iter().map(|name| identifier_expression(name)).collect();
        let constructed = self.construct(data, constructor, values)?;
        let result = self.go_result(body.monotype)?;
        let line = self.constructor_line(data, &constructors[constructor])?;
        let mut statements = vec![];
        lines::push_at(line, GoStatement::Return(Some(constructed)), &mut statements);
        self.type_declarations.push(GoDeclaration::Function {
            name: name.clone(),
            parameters: go_parameters,
            result,
            body: statements,
        });
        Ok(Some(name))
    }
}

/// A constructor function's parameter: its field's name, unexported.
fn parameter_name(field: &str, position: usize) -> String {
    let lowered = lower_first(field);
    let lowered = if lowered.is_empty() { format!("value{position}") } else { lowered };
    let mut name = identifier(&lowered);
    if RESERVED.contains(&name.as_str()) {
        name = format!("{name}Value");
    }
    name
}
