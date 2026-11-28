//! Constructor functions.
//!
//! `k More Done` passes the constructors themselves. Each constructor passed
//! as a value becomes one Go function beside its type,
//!
//! ```go
//! func More(more func(struct{}) StepInt) StepInt { return StepInt{Tag: StepIntMore, More: more} }
//! ```
//!
//! passed by name, instead of a function literal that builds the struct at
//! every use. A sum type's constructor applied to all its fields calls the
//! same function, `More(next)`, once the passes that read the fields of
//! composite literals are done with it.

use super::packages::Spelling;
use super::{DataKind, DataLayout, Emitter, call, composite, identifier_expression, lines};
use crate::error::GoResult;
use crate::go_traversal;
use crate::monomorphic::{Expression, ExpressionKind, Local};
use crate::monotype::{DataType, MonotypeId};
use crate::naming::{RESERVED, identifier, lower_first};
use crate::syntax::{GoDeclaration, GoExpression, GoStatement, GoType};

/// A constructor's composite literals: the Go struct, and the tag of a tagged one.
pub(super) type ConstructionKey = (String, Option<String>);

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
        let constructor = *constructor;
        let applies_parameters = arguments.len() == parameters.len()
            && arguments.iter().zip(&parameters).all(|(argument, parameter)| {
                matches!(argument.kind, ExpressionKind::Local(id) if id == parameter.id)
            });
        if parameters.is_empty() || !applies_parameters || self.arity(monotype) != parameters.len()
        {
            return Ok(None);
        }
        let key = (data.clone(), constructor, monotype);
        if let Some(name) = self.constructor_functions.get(&key) {
            return Ok(Some(identifier_expression(name)));
        }
        let layout = self.data_layout(data)?;
        if let Some(maybe) = &layout.maybe {
            let name = self.maybe_just_function(&layout, maybe)?;
            self.constructor_functions.insert(key, name.clone());
            return Ok(Some(identifier_expression(&name)));
        }
        let construction = self.construction_key(&layout, constructor)?;
        let shared = construction.as_ref().and_then(|key| self.construction_functions.get(key));
        if let Some(name) = shared.cloned() {
            self.constructor_functions.insert(key, name.clone());
            return Ok(Some(identifier_expression(&name)));
        }
        if layout.constructors[constructor].fields.len() != parameters.len() {
            return Ok(None);
        }
        let mut parameter_types = Vec::with_capacity(parameters.len());
        for parameter in &parameters {
            parameter_types.push(self.go_type(parameter.monotype)?);
        }
        let result = self.go_result(body.monotype)?;
        let name = self.declare_constructor_function(data, constructor, parameter_types, result)?;
        self.constructor_functions.insert(key, name.clone());
        if let Some(construction) = construction {
            self.construction_functions.insert(construction, name.clone());
        }
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

    /// How a construction's composite literals are told apart, when a constructor function
    /// may build it: a constructor with fields of a sum type. A product's literal already
    /// reads as its fields, and a field typed with `any` would add one more to the function.
    pub(super) fn construction_key(
        &mut self,
        layout: &DataLayout,
        constructor: usize,
    ) -> GoResult<Option<ConstructionKey>> {
        let constructor_layout = &layout.constructors[constructor];
        let sum = matches!(layout.kind, DataKind::Tagged | DataKind::Sentinel);
        if !sum
            || layout.maybe.is_some()
            || layout.erases_arguments
            || constructor_layout.fields.is_empty()
        {
            return Ok(None);
        }
        for &(_, field) in &constructor_layout.fields {
            if mentions_any(&self.go_type(field)?) {
                return Ok(None);
            }
        }
        let tag = (layout.kind == DataKind::Tagged).then(|| constructor_layout.tag.clone());
        Ok(Some((layout.name.clone(), tag)))
    }

    /// Calls the constructor function of every construction still built by a composite
    /// literal of its own fields, and nothing else, such as a `Unique` mask.
    pub(super) fn call_constructor_functions(
        &mut self,
        declarations: &mut [GoDeclaration],
    ) -> GoResult<()> {
        if self.named_constructions.is_empty() {
            return Ok(());
        }
        let mut failure = None;
        for declaration in declarations.iter_mut() {
            go_traversal::each_expression_in_declaration(declaration, |expression| {
                if failure.is_none()
                    && let Err(error) = self.call_constructor_function(expression)
                {
                    failure = Some(error);
                }
            });
        }
        failure.map_or(Ok(()), Err)
    }

    fn call_constructor_function(&mut self, expression: &mut GoExpression) -> GoResult<()> {
        let (composite, addressed) = match &mut *expression {
            GoExpression::Address(composite) => (composite.as_mut(), true),
            composite => (composite, false),
        };
        let GoExpression::Composite { type_: GoType::Named(type_name), fields } = composite else {
            return Ok(());
        };
        let tag = match fields.first() {
            Some((Some(label), GoExpression::Identifier(tag))) if label == "Tag" => {
                Some(tag.clone())
            }
            _ => None,
        };
        let key = (type_name.clone(), tag);
        let Some((data, constructor)) = self.named_constructions.get(&key).cloned() else {
            return Ok(());
        };
        let layout = self.data_layout(&data)?;
        // A boxed type's bare literal is written into a cell that already exists.
        if layout.boxed != addressed {
            return Ok(());
        }
        let values = &fields[usize::from(key.1.is_some())..];
        let expected = &layout.constructors[constructor].fields;
        let own_fields = values.len() == expected.len()
            && values
                .iter()
                .zip(expected)
                .all(|((label, _), (field, _))| label.as_deref() == Some(field.as_str()));
        if !own_fields {
            return Ok(());
        }
        let name = self.construction_function(key, &data, constructor, &layout)?;
        let values = fields.drain(..).skip(usize::from(layout.kind == DataKind::Tagged));
        let arguments = values.map(|(_, value)| value).collect();
        *expression = call(identifier_expression(&name), arguments);
        Ok(())
    }

    fn construction_function(
        &mut self,
        key: ConstructionKey,
        data: &DataType,
        constructor: usize,
        layout: &DataLayout,
    ) -> GoResult<String> {
        if let Some(name) = self.construction_functions.get(&key) {
            return Ok(name.clone());
        }
        let mut parameter_types = vec![];
        for &(_, field) in &layout.constructors[constructor].fields {
            parameter_types.push(self.go_type(field)?);
        }
        let result = Some(layout.go_type());
        let name = self.declare_constructor_function(data, constructor, parameter_types, result)?;
        self.construction_functions.insert(key, name.clone());
        Ok(name)
    }

    /// Declares `func More(more …) StepInt { return StepInt{…} }` beside the
    /// type: called after the constructor, or after the constructor and its
    /// type where another global has that name.
    fn declare_constructor_function(
        &mut self,
        data: &DataType,
        constructor: usize,
        parameter_types: Vec<GoType>,
        result: Option<GoType>,
    ) -> GoResult<String> {
        let layout = self.data_layout(data)?;
        let fields = layout.constructors[constructor].fields.clone();
        let constructors = self
            .monotypes
            .constructors(&mut self.context, data)
            .map_err(|failure| failure.at(&layout.name))?;
        let name = self.global_name(Spelling::Constructor {
            constructor: crate::naming::go_field(&constructors[constructor].name),
            data_type: layout.name.clone(),
        });
        self.homes.insert(name.clone(), data.file_id);
        // The function's locals are its own, apart from the function being emitted.
        let enclosing = std::mem::take(&mut self.local_names);
        let names: Vec<String> = fields
            .iter()
            .enumerate()
            .map(|(position, (field, _))| self.local_name(parameter_name(field, position)))
            .collect();
        self.local_names = enclosing;
        let parameters = names.iter().cloned().zip(parameter_types).collect();
        let values = names.iter().map(|name| identifier_expression(name)).collect();
        let composite = composite(&layout, constructor, values);
        let constructed = match layout.boxed {
            true => GoExpression::Address(Box::new(composite)),
            false => composite,
        };
        let line = self.constructor_line(data, &constructors[constructor])?;
        let mut statements = vec![];
        lines::push_at(line, GoStatement::Return(Some(constructed)), &mut statements);
        self.type_declarations.push(GoDeclaration::Function {
            name: name.clone(),
            parameters,
            result,
            body: statements,
        });
        Ok(name)
    }
}

/// Whether a type spells `any` itself; a named type's own declaration counts its `any`s once.
fn mentions_any(type_: &GoType) -> bool {
    match type_ {
        GoType::Any | GoType::Erased(_) => true,
        GoType::Slice(element) | GoType::Pointer(element) => mentions_any(element),
        GoType::Map(key, value) => mentions_any(key) || mentions_any(value),
        GoType::Function { parameters, result } => {
            parameters.iter().any(mentions_any) || result.as_deref().is_some_and(mentions_any)
        }
        GoType::Struct(fields) => fields.iter().any(|field| mentions_any(&field.type_)),
        GoType::Generic { arguments, .. } | GoType::Results(arguments) => {
            arguments.iter().any(mentions_any)
        }
        GoType::Named(_)
        | GoType::Int
        | GoType::Float64
        | GoType::Bool
        | GoType::Rune
        | GoType::String
        | GoType::EmptyStruct => false,
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
