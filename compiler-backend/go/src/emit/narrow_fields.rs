use rustc_hash::{FxHashMap, FxHashSet};

use super::headers::Effects;
use super::intervals;
use crate::go_traversal::{self, Walk};
use crate::syntax::{GoDeclaration, GoExpression, GoStatement, GoType, StructField};

pub(super) fn narrow_int_fields(
    declarations: &mut [GoDeclaration],
    data_structs: &FxHashSet<String>,
    effects: &Effects,
    helpers: &FxHashSet<String>,
) {
    let candidates = candidate_fields(declarations, data_structs);
    if candidates.is_empty() {
        return;
    }
    let narrowed = intervals::fields_that_fit(declarations, effects, helpers, &candidates);
    if narrowed.is_empty() {
        return;
    }
    for declaration in declarations.iter_mut() {
        narrow_declared_fields(declaration, data_structs, &narrowed);
        let mut storage = Storage { narrowed: &narrowed, data_structs };
        go_traversal::declaration(&mut storage, declaration);
    }
}

fn candidate_fields(
    declarations: &mut [GoDeclaration],
    data_structs: &FxHashSet<String>,
) -> FxHashSet<String> {
    let mut census = Census::default();
    for declaration in declarations.iter_mut() {
        census.declaration(declaration, data_structs);
    }
    let Census { mut int_fields, other_fields, excluded, positional } = census;
    int_fields.retain(|field, structs| {
        !other_fields.contains(field)
            && !excluded.contains(field)
            && !structs.iter().any(|name| positional.contains(name))
    });
    let mut candidates: FxHashSet<String> = int_fields.into_keys().collect();
    for declaration in declarations.iter() {
        let text = match declaration {
            GoDeclaration::Source { template, .. } => *template,
            GoDeclaration::Written { source, .. } => source.as_str(),
            _ => continue,
        };
        candidates.retain(|field| !mentions_word(text, field));
    }
    candidates
}

#[derive(Default)]
struct Census {
    int_fields: FxHashMap<String, FxHashSet<String>>,
    other_fields: FxHashSet<String>,
    excluded: FxHashSet<String>,
    positional: FxHashSet<String>,
}

impl Census {
    fn declaration(&mut self, declaration: &mut GoDeclaration, data_structs: &FxHashSet<String>) {
        match declaration {
            GoDeclaration::Type { name, type_, .. }
            | GoDeclaration::GenericType { name, type_, .. } => match type_ {
                GoType::Struct(fields) if data_structs.contains(name.as_str()) => {
                    for field in fields.iter() {
                        if field.type_ == GoType::Int {
                            let structs = self.int_fields.entry(field.name.clone()).or_default();
                            structs.insert(name.clone());
                        } else {
                            self.other_fields.insert(field.name.clone());
                        }
                        self.type_(&field.type_);
                    }
                }
                type_ => self.type_(type_),
            },
            GoDeclaration::Alias { type_, .. } => self.type_(type_),
            GoDeclaration::Constant { type_, .. } => {
                type_.iter().for_each(|type_| self.type_(type_))
            }
            GoDeclaration::Variable { type_, .. } => {
                type_.iter().for_each(|type_| self.type_(type_))
            }
            GoDeclaration::Function { parameters, result, .. } => {
                parameters.iter().for_each(|(_, type_)| self.type_(type_));
                result.iter().for_each(|type_| self.type_(type_));
            }
            GoDeclaration::Source { .. }
            | GoDeclaration::Constants { .. }
            | GoDeclaration::Written { .. } => {}
        }
        go_traversal::declaration(self, declaration);
    }

    fn type_(&mut self, type_: &GoType) {
        match type_ {
            GoType::Struct(fields) => {
                for field in fields {
                    self.other_fields.insert(field.name.clone());
                    self.type_(&field.type_);
                }
            }
            GoType::Slice(inner) | GoType::Pointer(inner) => self.type_(inner),
            GoType::Function { parameters, result } => {
                parameters.iter().for_each(|parameter| self.type_(parameter));
                result.iter().for_each(|result| self.type_(result));
            }
            GoType::Generic { arguments, .. } | GoType::Results(arguments) => {
                arguments.iter().for_each(|argument| self.type_(argument));
            }
            GoType::Named(_)
            | GoType::Int
            | GoType::Float64
            | GoType::Bool
            | GoType::Rune
            | GoType::String
            | GoType::EmptyStruct
            | GoType::Any
            | GoType::Erased(_) => {}
        }
    }
}

impl Walk for Census {
    fn statement(&mut self, statement: &mut GoStatement) {
        match statement {
            GoStatement::Variable { type_, .. } | GoStatement::IfAssert { type_, .. } => {
                self.type_(type_)
            }
            _ => {}
        }
        go_traversal::statement(self, statement);
    }

    fn expression(&mut self, value: &mut GoExpression) {
        match value {
            GoExpression::Address(inner) => {
                if let GoExpression::Field { name, .. } = inner.unattributed() {
                    self.excluded.insert(name.clone());
                }
            }
            GoExpression::Composite { type_, fields } => {
                self.type_(type_);
                if fields.iter().any(|(label, _)| label.is_none())
                    && let GoType::Named(name) | GoType::Generic { name, .. } = type_
                {
                    self.positional.insert(name.clone());
                }
            }
            GoExpression::Function { parameters, result, .. } => {
                parameters.iter().for_each(|(_, type_)| self.type_(type_));
                result.iter().for_each(|type_| self.type_(type_));
            }
            GoExpression::Conversion { type_, .. }
            | GoExpression::TypeAssertion { type_, .. }
            | GoExpression::Type(type_) => self.type_(type_),
            GoExpression::Instantiation { arguments, .. } => {
                arguments.iter().for_each(|argument| self.type_(argument))
            }
            _ => {}
        }
        go_traversal::expression(self, value);
    }
}

fn mentions_word(text: &str, word: &str) -> bool {
    let identifier = |character: char| character.is_alphanumeric() || character == '_';
    text.match_indices(word).any(|(at, _)| {
        !text[..at].chars().next_back().is_some_and(identifier)
            && !text[at + word.len()..].chars().next().is_some_and(identifier)
    })
}

fn narrow_declared_fields(
    declaration: &mut GoDeclaration,
    data_structs: &FxHashSet<String>,
    narrowed: &FxHashSet<String>,
) {
    let (GoDeclaration::Type { name, type_: GoType::Struct(fields), .. }
    | GoDeclaration::GenericType { name, type_: GoType::Struct(fields), .. }) = declaration
    else {
        return;
    };
    if !data_structs.contains(name.as_str()) {
        return;
    }
    for StructField { name, type_, .. } in fields.iter_mut() {
        if narrowed.contains(name.as_str()) {
            *type_ = int32();
        }
    }
}

struct Storage<'n> {
    narrowed: &'n FxHashSet<String>,
    data_structs: &'n FxHashSet<String>,
}

impl Storage<'_> {
    fn is_narrowed(&self, value: &GoExpression) -> bool {
        matches!(value.unattributed(), GoExpression::Field { name, .. } if self.narrowed.contains(name))
    }

    fn stored(&self, value: GoExpression) -> GoExpression {
        match value {
            GoExpression::Integer(_) => value,
            GoExpression::Attributed { line, value } => {
                GoExpression::Attributed { line, value: Box::new(self.stored(*value)) }
            }
            GoExpression::Conversion { type_: GoType::Int, value } if self.is_narrowed(&value) => {
                *value
            }
            value => GoExpression::Conversion { type_: int32(), value: Box::new(value) },
        }
    }

    fn store(&self, value: &mut GoExpression) {
        let taken = std::mem::replace(value, GoExpression::Integer(0));
        *value = self.stored(taken);
    }
}

impl Walk for Storage<'_> {
    fn statement(&mut self, statement: &mut GoStatement) {
        let GoStatement::Assign { targets, values } = statement else {
            return go_traversal::statement(self, statement);
        };
        for target in targets.iter_mut() {
            match target {
                GoExpression::Field { value, name } if self.narrowed.contains(name.as_str()) => {
                    self.expression(value)
                }
                target => self.expression(target),
            }
        }
        values.iter_mut().for_each(|value| self.expression(value));
        if targets.len() == values.len() {
            for (target, value) in targets.iter().zip(values.iter_mut()) {
                if self.is_narrowed(target) {
                    self.store(value);
                }
            }
        }
    }

    fn expression(&mut self, value: &mut GoExpression) {
        go_traversal::expression(self, value);
        match value {
            GoExpression::Field { name, .. } if self.narrowed.contains(name.as_str()) => {
                let read = std::mem::replace(value, GoExpression::Integer(0));
                *value = GoExpression::Conversion { type_: GoType::Int, value: Box::new(read) };
            }
            GoExpression::Composite {
                type_: GoType::Named(name) | GoType::Generic { name, .. },
                fields,
            } if self.data_structs.contains(name.as_str()) => {
                for (label, field) in fields.iter_mut() {
                    if label.as_ref().is_some_and(|label| self.narrowed.contains(label)) {
                        self.store(field);
                    }
                }
            }
            _ => {}
        }
    }
}

fn int32() -> GoType {
    GoType::Named("int32".to_string())
}
