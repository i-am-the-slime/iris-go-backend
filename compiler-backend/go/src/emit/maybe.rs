use rustc_hash::FxHashSet;

use super::names::{NamePart, PendingSpelling};
use super::packages::Spelling;
use super::{
    ConstructorLayout, DataKind, DataLayout, Emitter, binary, call, field, identifier_expression,
};
use crate::error::GoResult;
use crate::mono::{Literal, Pattern, PatternKind};
use crate::monotype::{DataConstructor, DataType, Failure, Monotype, MonotypeId};
use crate::naming::identifier;
use crate::primitives::{KnownType, known_type};
use crate::syntax::{GoDeclaration, GoExpression, GoStatement, GoType};
use files::FileId;

#[derive(Clone, Debug)]
pub(super) enum MaybeLayout {
    Int { just: String, nothing: String },
    Char { just: String, nothing: String },
    Boolean { just: String, true_: String, false_: String, nothing: String },
    Pointer { just: String, payload: MonotypeId },
    Struct { just: String, nothing: String, literal: bool },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Representation {
    Int,
    Char,
    Boolean,
    Pointer,
    Struct,
}

impl MaybeLayout {
    pub(super) fn is_struct(&self) -> bool {
        matches!(self, MaybeLayout::Struct { .. })
    }

    fn is_nothing(&self, value: &GoExpression) -> bool {
        let GoExpression::Identifier(name) = value else { return false };
        match self {
            MaybeLayout::Int { nothing, .. }
            | MaybeLayout::Char { nothing, .. }
            | MaybeLayout::Boolean { nothing, .. }
            | MaybeLayout::Struct { nothing, .. } => name == nothing,
            MaybeLayout::Pointer { .. } => name == "nil",
        }
    }

    fn just(&self) -> &str {
        match self {
            MaybeLayout::Int { just, .. }
            | MaybeLayout::Char { just, .. }
            | MaybeLayout::Boolean { just, .. }
            | MaybeLayout::Pointer { just, .. }
            | MaybeLayout::Struct { just, .. } => just,
        }
    }
}

pub(super) struct MaybeHelpers {
    tags: Option<(String, String)>,
    declared: FxHashSet<String>,
}

impl MaybeHelpers {
    pub(super) fn new() -> MaybeHelpers {
        MaybeHelpers { tags: None, declared: FxHashSet::default() }
    }
}

impl<Q> Emitter<'_, '_, '_, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn maybe_payload(&mut self, data: &DataType) -> GoResult<Option<MonotypeId>> {
        if data.arguments.len() != 1 {
            return Ok(None);
        }
        let module = self.context.module(data.file_id)?.name.clone();
        let name = self.context.type_name(data.file_id, data.item)?;
        if known_type(&module, &name) != Some(KnownType::Maybe) {
            return Ok(None);
        }
        let constructors = self
            .monotypes
            .constructors(&mut self.context, data)
            .map_err(Failure::in_code_generation)?;
        Ok(constructors.iter().find_map(|constructor| match constructor.fields[..] {
            [payload] => Some(payload),
            _ => None,
        }))
    }

    pub(super) fn maybe_representation(
        &mut self,
        payload: MonotypeId,
    ) -> GoResult<Representation> {
        Ok(match self.monotypes.get(payload).clone() {
            Monotype::Int => Representation::Int,
            Monotype::Char => Representation::Char,
            Monotype::Boolean => Representation::Boolean,
            Monotype::Data(data) if self.is_boxed(&data)? => Representation::Pointer,
            Monotype::Function(..)
            | Monotype::Effect(_)
            | Monotype::Reference(_)
            | Monotype::Lazy(_) => Representation::Pointer,
            Monotype::Recursive(data) => {
                let unfolded = self.unfold(&data)?;
                let unfolds_to_maybe = match self.monotypes.get(unfolded).clone() {
                    Monotype::Recursive(_) => true,
                    Monotype::Data(inner) => self.maybe_payload(&inner)?.is_some(),
                    _ => false,
                };
                let pointer = !unfolds_to_maybe
                    && self.maybe_representation(unfolded)? == Representation::Pointer;
                if pointer { Representation::Pointer } else { Representation::Struct }
            }
            _ => Representation::Struct,
        })
    }

    pub(super) fn maybe_pointer_payload(
        &mut self,
        data: &DataType,
    ) -> GoResult<Option<MonotypeId>> {
        let Some(payload) = self.maybe_payload(data)? else { return Ok(None) };
        Ok((self.maybe_representation(payload)? == Representation::Pointer).then_some(payload))
    }

    pub(super) fn maybe_boolean_test(
        &self,
        layout: &DataLayout,
        arguments: &[Pattern],
        path: GoExpression,
    ) -> Option<GoExpression> {
        let Some(MaybeLayout::Boolean { true_, false_, .. }) = &layout.maybe else { return None };
        let [Pattern { kind: PatternKind::Literal(Literal::Boolean(value)), .. }] = arguments
        else {
            return None;
        };
        let constant = if *value { true_ } else { false_ };
        Some(binary("==", path, identifier_expression(constant)))
    }

    pub(super) fn maybe_layout(
        &mut self,
        data: &DataType,
        payload: MonotypeId,
        constructors: &[DataConstructor],
    ) -> GoResult<DataLayout> {
        let representation = self.maybe_representation(payload)?;
        let just = self.maybe_global(data, "Just")?;
        let fields_of = |constructor: &DataConstructor| -> Vec<(String, MonotypeId)> {
            constructor.fields.iter().map(|&field| ("Just".to_string(), field)).collect()
        };
        let scalar = |emitter: &mut Self,
                      name: String,
                      maybe: MaybeLayout|
         -> DataLayout {
            let constructors = constructors
                .iter()
                .map(|constructor| ConstructorLayout {
                    tag: String::new(),
                    fields: fields_of(constructor),
                })
                .collect();
            let layout = DataLayout {
                name,
                kind: DataKind::Tagged,
                constructors,
                erases_arguments: false,
                boxed: false,
                declaration: None,
                origin_position: 0,
                maybe: Some(maybe),
            };
            emitter.data_layouts.insert(data.clone(), layout.clone());
            layout
        };
        match representation {
            Representation::Int | Representation::Char => {
                let name = self.maybe_global(data, "")?;
                let nothing = self.maybe_global(data, "No")?;
                self.type_declarations.push(GoDeclaration::Type {
                    name: name.clone(),
                    type_: GoType::Named("int64".into()),
                });
                let outside_int32 =
                    binary("<<", GoExpression::Integer(1), GoExpression::Integer(32));
                self.type_declarations.push(GoDeclaration::Constant {
                    name: nothing.clone(),
                    type_: Some(GoType::Named(name.clone())),
                    value: outside_int32,
                });
                let maybe = match representation {
                    Representation::Int => MaybeLayout::Int { just, nothing },
                    _ => MaybeLayout::Char { just, nothing },
                };
                Ok(scalar(self, name, maybe))
            }
            Representation::Boolean => {
                let name = self.maybe_global(data, "")?;
                let nothing = self.maybe_global(data, "No")?;
                let false_ = self.global_name(Spelling::Base("False".into()));
                let true_ = self.global_name(Spelling::Base("True".into()));
                for constant in [&false_, &true_] {
                    self.homes.insert(constant.clone(), data.file_id);
                }
                self.type_declarations.push(GoDeclaration::Type {
                    name: name.clone(),
                    type_: GoType::Named("uint8".into()),
                });
                self.type_declarations.push(GoDeclaration::Constants {
                    type_name: Some(name.clone()),
                    names: vec![false_.clone(), true_.clone(), nothing.clone()],
                });
                let maybe = MaybeLayout::Boolean { just, true_, false_, nothing };
                Ok(scalar(self, name, maybe))
            }
            Representation::Pointer => {
                let name = self.maybe_full_name(data)?;
                Ok(scalar(self, name, MaybeLayout::Pointer { just, payload }))
            }
            Representation::Struct => self.maybe_struct(data, constructors, just),
        }
    }

    fn maybe_struct(
        &mut self,
        data: &DataType,
        constructors: &[DataConstructor],
        just: String,
    ) -> GoResult<DataLayout> {
        let name = self.maybe_global(data, "")?;
        let nothing = self.maybe_global(data, "No")?;
        let (tag_nothing, tag_just) = self.maybe_tags(data.file_id);
        let plan = self.plan_slots(constructors)?;
        let mut layouts = vec![];
        for (index, constructor) in constructors.iter().enumerate() {
            let tag = if constructor.fields.is_empty() { &tag_nothing } else { &tag_just };
            let slots = plan.constructors[index].iter().cloned();
            let fields = slots.zip(constructor.fields.iter().copied()).collect();
            layouts.push(ConstructorLayout { tag: tag.clone(), fields });
        }
        let erases_arguments = self.erases_arguments(data)?;
        let payloads = constructors.iter().flat_map(|constructor| constructor.fields.iter());
        let erased_payload = payloads
            .map(|&payload| self.monotypes.get(payload))
            .any(|payload| matches!(payload, Monotype::Erased(_) | Monotype::Opaque));
        let literal = erases_arguments || erased_payload;
        let layout = DataLayout {
            name: name.clone(),
            kind: DataKind::Tagged,
            constructors: layouts,
            erases_arguments,
            boxed: self.is_boxed(data)?,
            declaration: None,
            origin_position: plan.pointer_prefix,
            maybe: Some(MaybeLayout::Struct { just, nothing, literal }),
        };
        self.data_layouts.insert(data.clone(), layout.clone());
        let mut fields = vec![];
        for slot in plan.slots {
            fields.push(match slot {
                super::layout::Slot::Tag => ("Tag".to_string(), super::layout::tag_type(2)),
                super::layout::Slot::Field { name, monotype } => (name, self.go_type(monotype)?),
            });
        }
        if let Some(layout) = self.data_layouts.get_mut(data) {
            layout.declaration = Some(self.type_declarations.len());
        }
        self.type_declarations.push(GoDeclaration::Type { name, type_: GoType::Struct(fields) });
        Ok(self.data_layouts.get(data).cloned().unwrap_or(layout))
    }

    fn maybe_global(&mut self, data: &DataType, prefix: &str) -> GoResult<String> {
        let mut full = format!("{prefix}Maybe");
        let mut parts = vec![];
        if !prefix.is_empty() {
            parts.push(NamePart::Text(prefix.into()));
        }
        parts.push(NamePart::Stutter("Maybe".into()));
        for &argument in data.arguments.iter() {
            self.context.type_suffix(argument, &mut full)?;
            self.type_parts(argument, &mut parts)?;
        }
        let name = self.pending_global(identifier(&full), PendingSpelling::Parts(parts));
        self.homes.insert(name.clone(), data.file_id);
        Ok(name)
    }

    fn maybe_full_name(&mut self, data: &DataType) -> GoResult<String> {
        let mut full = "Maybe".to_string();
        for &argument in data.arguments.iter() {
            self.context.type_suffix(argument, &mut full)?;
        }
        Ok(identifier(&full))
    }

    fn maybe_tags(&mut self, file_id: FileId) -> (String, String) {
        if let Some(tags) = &self.maybe_helpers.tags {
            return tags.clone();
        }
        let nothing = self.global_name(Spelling::Base("TagNothing".into()));
        let just = self.global_name(Spelling::Base("TagJust".into()));
        for (name, value) in [(&nothing, 0), (&just, 1)] {
            self.homes.insert(name.clone(), file_id);
            self.type_declarations.push(GoDeclaration::Constant {
                name: name.clone(),
                type_: None,
                value: GoExpression::Integer(value),
            });
        }
        self.maybe_helpers.tags = Some((nothing.clone(), just.clone()));
        (nothing, just)
    }

    pub(super) fn construct_maybe(
        &mut self,
        layout: &DataLayout,
        maybe: &MaybeLayout,
        constructor: usize,
        mut values: Vec<GoExpression>,
    ) -> GoResult<GoExpression> {
        let is_just = !layout.constructors[constructor].fields.is_empty();
        Ok(match maybe {
            MaybeLayout::Int { nothing, .. } | MaybeLayout::Char { nothing, .. } => {
                if is_just {
                    let type_ = GoType::Named(layout.name.clone());
                    GoExpression::Conversion { type_, value: Box::new(values.remove(0)) }
                } else {
                    identifier_expression(nothing)
                }
            }
            MaybeLayout::Boolean { nothing, .. } => {
                if is_just {
                    let just = self.maybe_just_function(layout, maybe)?;
                    call(identifier_expression(&just), values)
                } else {
                    identifier_expression(nothing)
                }
            }
            MaybeLayout::Pointer { .. } => {
                if is_just { values.remove(0) } else { identifier_expression("nil") }
            }
            MaybeLayout::Struct { nothing, literal, .. } => {
                if is_just && *literal {
                    let composite = self.composite(layout, constructor, values);
                    if layout.boxed { GoExpression::Address(Box::new(composite)) } else { composite }
                } else if is_just {
                    let just = self.maybe_just_function(layout, maybe)?;
                    call(identifier_expression(&just), values)
                } else {
                    self.declare_maybe_nothing(layout, nothing, constructor);
                    identifier_expression(nothing)
                }
            }
        })
    }

    pub(super) fn maybe_just_function(
        &mut self,
        layout: &DataLayout,
        maybe: &MaybeLayout,
    ) -> GoResult<String> {
        let name = maybe.just().to_string();
        if !self.maybe_helpers.declared.insert(name.clone()) {
            return Ok(name);
        }
        let (just, constructor) = layout
            .constructors
            .iter()
            .enumerate()
            .find(|(_, constructor)| !constructor.fields.is_empty())
            .expect("invariant violated: Maybe has a Just constructor");
        let (_, payload) = constructor.fields[0];
        let parameter = identifier_expression("just");
        let body = match maybe {
            MaybeLayout::Int { .. } | MaybeLayout::Char { .. } => {
                let type_ = GoType::Named(layout.name.clone());
                vec![GoStatement::Return(Some(GoExpression::Conversion {
                    type_,
                    value: Box::new(parameter),
                }))]
            }
            MaybeLayout::Boolean { true_, false_, .. } => vec![
                GoStatement::If {
                    condition: parameter,
                    then: vec![GoStatement::Return(Some(identifier_expression(true_)))],
                    otherwise: vec![],
                },
                GoStatement::Return(Some(identifier_expression(false_))),
            ],
            MaybeLayout::Pointer { .. } => vec![GoStatement::Return(Some(parameter))],
            MaybeLayout::Struct { .. } => {
                let composite = self.composite(layout, just, vec![parameter]);
                let built = if layout.boxed {
                    GoExpression::Address(Box::new(composite))
                } else {
                    composite
                };
                vec![GoStatement::Return(Some(built))]
            }
        };
        let parameters = vec![("just".into(), self.go_type(payload)?)];
        let result = Some(self.layout_type(layout)?);
        self.type_declarations.push(GoDeclaration::Function {
            name: name.clone(),
            parameters,
            result,
            body,
        });
        Ok(name)
    }

    fn declare_maybe_nothing(&mut self, layout: &DataLayout, nothing: &str, constructor: usize) {
        if !self.maybe_helpers.declared.insert(nothing.to_string()) {
            return;
        }
        let composite = self.composite(layout, constructor, vec![]);
        let value =
            if layout.boxed { GoExpression::Address(Box::new(composite)) } else { composite };
        self.type_declarations.push(GoDeclaration::Variable {
            name: nothing.to_string(),
            type_: None,
            value,
        });
    }

    pub(super) fn layout_type(&mut self, layout: &DataLayout) -> GoResult<GoType> {
        match &layout.maybe {
            Some(MaybeLayout::Pointer { payload, .. }) => self.go_type(*payload),
            _ => Ok(layout.go_type()),
        }
    }

    pub(super) fn constructor_test(
        &self,
        layout: &DataLayout,
        constructor: usize,
        path: GoExpression,
    ) -> Option<GoExpression> {
        let is_just = !layout.constructors[constructor].fields.is_empty();
        if layout.maybe.as_ref().is_some_and(|maybe| maybe.is_nothing(&path)) {
            return Some(GoExpression::Boolean(!is_just));
        }
        let absent = match &layout.maybe {
            None | Some(MaybeLayout::Struct { .. }) => {
                let tag = identifier_expression(&layout.constructors[constructor].tag);
                return match layout.kind {
                    DataKind::Enumeration => Some(binary("==", path, tag)),
                    DataKind::Tagged => Some(binary("==", field(path, "Tag"), tag)),
                    DataKind::Product => None,
                };
            }
            Some(
                MaybeLayout::Int { nothing, .. }
                | MaybeLayout::Char { nothing, .. }
                | MaybeLayout::Boolean { nothing, .. },
            ) => identifier_expression(nothing),
            Some(MaybeLayout::Pointer { .. }) => identifier_expression("nil"),
        };
        Some(binary(if is_just { "!=" } else { "==" }, path, absent))
    }

    pub(super) fn constructor_field(
        &self,
        layout: &DataLayout,
        constructor: usize,
        position: usize,
        path: GoExpression,
    ) -> GoExpression {
        match &layout.maybe {
            None | Some(MaybeLayout::Struct { .. }) => {
                field(path, &layout.constructors[constructor].fields[position].0)
            }
            Some(MaybeLayout::Int { .. }) => GoExpression::Conversion {
                type_: GoType::Named("int32".into()),
                value: Box::new(path),
            },
            Some(MaybeLayout::Char { .. }) => {
                GoExpression::Conversion { type_: GoType::Rune, value: Box::new(path) }
            }
            Some(MaybeLayout::Boolean { true_, .. }) => {
                binary("==", path, identifier_expression(true_))
            }
            Some(MaybeLayout::Pointer { .. }) => path,
        }
    }
}
