//! Struct locals that live as one Go local per field.
//!
//! Go keeps a struct of more than a few words in memory. A local that is
//! built field by field, as a fold's record accumulator or a record update
//! is, then stores to the stack on every field write and reloads on every
//! read, and copying it reads back whole words that separate field stores
//! have just written. When a local of a struct type has a field written in
//! place, and is otherwise read field by field, it becomes one local per
//! field: `accumulator.Vx = ...` becomes `accumulatorVx = ...`. The struct is
//! built only where the value is used whole, by a composite of the field
//! locals.
//!
//! Struct values are copied on assignment, so a field local holds exactly what
//! the struct's field would. A local stays whole when its address is taken,
//! when a closure mentions it (each field would be captured on its own), when
//! a method may be called on it, when it is bound by a range or more than
//! once, or when its value comes from an expression that would have to be
//! evaluated once per field.

use rustc_hash::{FxHashMap, FxHashSet};

use super::aliases::{mentions, target_root};
use super::is_untyped_constant;
use super::locals::NUMBERED;
use crate::go_traversal::{self, Walk};
use crate::syntax::{GoDeclaration, GoExpression, GoStatement, GoType};

/// The fields of each named struct type, in declaration order.
pub(super) type Structs = FxHashMap<String, Vec<(String, GoType)>>;

pub(super) fn structs_of(declarations: &[GoDeclaration]) -> Structs {
    declarations
        .iter()
        .filter_map(|declaration| match declaration {
            GoDeclaration::Type { name, type_: GoType::Struct(fields), .. }
                if !fields.is_empty() =>
            {
                let fields = fields.iter().map(|field| (field.name.clone(), field.type_.clone()));
                Some((name.clone(), fields.collect()))
            }
            _ => None,
        })
        .collect()
}

pub(super) fn split_struct_locals(declarations: &mut [GoDeclaration], structs: &Structs) {
    for declaration in declarations {
        if !matches!(declaration, GoDeclaration::Function { .. }) {
            continue;
        }
        let mut names = declaration.all_names();
        while let Some(split) = next_split(declaration, structs) {
            apply(declaration, &split, &mut names);
        }
    }
}

/// A local to split, with the fields that need a local of their own.
struct Split {
    local: String,
    type_name: String,
    fields: Vec<(String, GoType)>,
    needed: Vec<String>,
    parameter: bool,
}

fn next_split(declaration: &mut GoDeclaration, structs: &Structs) -> Option<Split> {
    let types = Types::of(declaration, structs);
    let parameters: Vec<String> = match declaration {
        GoDeclaration::Function { parameters, .. } => {
            parameters.iter().map(|(name, _)| name.clone()).collect()
        }
        _ => vec![],
    };
    for (local, type_name) in types.single_values() {
        let fields = &structs[&type_name];
        let parameter = parameters.contains(&local);
        let mut census = Census::new(&local, fields, parameter);
        go_traversal::declaration(&mut census, declaration);
        if let Some(needed) = census.needed() {
            return Some(Split { local, type_name, fields: fields.clone(), needed, parameter });
        }
    }
    None
}

fn apply(declaration: &mut GoDeclaration, split: &Split, names: &mut FxHashSet<String>) {
    let locals: FxHashMap<String, String> = split
        .fields
        .iter()
        .map(|(field, _)| (field.clone(), fresh(&split.local, field, names)))
        .collect();
    let mut introduced = vec![];
    go_traversal::each_block_in_declaration(declaration, |block| {
        let mut position = 0;
        while position < block.len() {
            match spliced(&block[position], split, &locals) {
                Some(statements) => {
                    let count = statements.len();
                    introduced.extend(statements.iter().filter_map(replaceable_definition));
                    block.splice(position..=position, statements);
                    position += count;
                }
                None => position += 1,
            }
        }
    });
    go_traversal::declaration(&mut Replace { split, locals: &locals }, declaration);
    if split.parameter
        && let GoDeclaration::Function { body, .. } = declaration
    {
        let read = |field: &String| GoStatement::Define {
            names: vec![locals[field].clone()],
            values: vec![GoExpression::Field {
                value: Box::new(identifier(&split.local)),
                name: field.clone(),
            }],
        };
        body.splice(0..0, split.needed.iter().map(read));
    }
    let types: FxHashMap<&str, &GoType> =
        split.fields.iter().map(|(field, type_)| (locals[field].as_str(), type_)).collect();
    go_traversal::each_block_in_declaration(declaration, |block| {
        for name in &introduced {
            define_at_first_write(block, name, types[name.as_str()]);
        }
    });
}

/// The statements that stand for the local's definition or its whole
/// reassignment, one per needed field.
fn spliced(
    statement: &GoStatement,
    split: &Split,
    locals: &FxHashMap<String, String>,
) -> Option<Vec<GoStatement>> {
    let local = |field: &str| locals[field].clone();
    let definitions = |value: Option<&GoExpression>| {
        let parts = value.map(|value| parts(value, split)).unwrap_or_default();
        let exact = value.is_some_and(|value| !matches!(value, GoExpression::Composite { .. }));
        split
            .needed
            .iter()
            .map(|field| definition(local(field), split.type_of(field), parts.get(field), exact))
            .collect()
    };
    match statement {
        GoStatement::Define { names, values } if names.as_slice() == [split.local.clone()] => {
            Some(definitions(values.first()))
        }
        GoStatement::Variable { name, value, .. } if *name == split.local => {
            Some(definitions(value.as_ref()))
        }
        GoStatement::Assign { targets, values } if matches!(targets.as_slice(), [GoExpression::Identifier(name)] if *name == split.local) =>
        {
            let parts = parts(&values[0], split);
            let targets = split.needed.iter().map(|field| identifier(&local(field))).collect();
            let values = split.needed.iter().map(|field| parts[field].clone()).collect();
            Some(vec![GoStatement::Assign { targets, values }])
        }
        _ => None,
    }
}

/// The value of each field of a struct-valued expression: a composite's own
/// field values, or the fields read from a place.
fn parts(value: &GoExpression, split: &Split) -> FxHashMap<String, GoExpression> {
    match value {
        GoExpression::Composite { fields, .. } => fields
            .iter()
            .filter_map(|(field, value)| Some((field.clone()?, value.clone())))
            .collect(),
        place => split
            .fields
            .iter()
            .map(|(field, _)| {
                let read =
                    GoExpression::Field { value: Box::new(place.clone()), name: field.clone() };
                (field.clone(), read)
            })
            .collect(),
    }
}

impl Split {
    fn type_of(&self, field: &str) -> &GoType {
        let (_, type_) = self.fields.iter().find(|(known, _)| known == field).expect("a field");
        type_
    }
}

/// The local of a field holding `value`. It is `name := value` when Go gives
/// that the field's type: the value is read from a field of the same struct
/// type (`exact`), or it is a typed value of a basic type, which only a value
/// of that very type is assignable to. Otherwise the local is declared with
/// the field's type, as its zero value when there is no value.
fn definition(
    name: String,
    type_: &GoType,
    value: Option<&GoExpression>,
    exact: bool,
) -> GoStatement {
    let basic = match type_ {
        GoType::Int | GoType::Float64 | GoType::Bool | GoType::Rune | GoType::String => true,
        GoType::Named(name) => PREDECLARED.contains(&name.as_str()),
        _ => false,
    };
    match value {
        Some(GoExpression::Identifier(nil)) if nil == "nil" => {
            GoStatement::Variable { name, type_: type_.clone(), value: None }
        }
        Some(value) if exact || basic && !is_untyped_constant(value) => {
            GoStatement::Define { names: vec![name], values: vec![value.clone()] }
        }
        value => GoStatement::Variable { name, type_: type_.clone(), value: value.cloned() },
    }
}

const PREDECLARED: &[&str] = &[
    "int8", "int16", "int32", "int64", "uint", "uint8", "uint16", "uint32", "uint64", "byte",
    "float32", "float64",
];

/// A definition whose value may go unread: none, or one without effects.
fn replaceable_definition(statement: &GoStatement) -> Option<String> {
    match statement {
        GoStatement::Define { names, values } if names.len() == 1 && is_pure(&values[0]) => {
            Some(names[0].clone())
        }
        GoStatement::Variable { name, value, .. } if value.as_ref().is_none_or(is_pure) => {
            Some(name.clone())
        }
        _ => None,
    }
}

/// A field local's definition followed, before any other mention of it, by an
/// assignment that does not read it, becomes a definition of the assigned
/// value: the first value is never read.
fn define_at_first_write(block: &mut Vec<GoStatement>, name: &str, type_: &GoType) {
    let defines = |statement: &GoStatement| match statement {
        GoStatement::Define { names, .. } => names.as_slice() == [name.to_string()],
        GoStatement::Variable { name: defined, .. } => defined == name,
        _ => false,
    };
    let Some(definition_at) = block.iter().position(defines) else { return };
    let Some(offset) =
        block[definition_at + 1..].iter_mut().position(|statement| mentions(statement, name))
    else {
        return;
    };
    let write = definition_at + 1 + offset;
    let GoStatement::Assign { targets, values } = &mut block[write] else { return };
    if !matches!(targets.as_slice(), [GoExpression::Identifier(target)] if target == name)
        || values.len() != 1
        || mentions(&mut GoStatement::Expression(values[0].clone()), name)
    {
        return;
    }
    let value = values.pop().expect("one value");
    block[write] = definition(name.to_string(), type_, Some(&value), false);
    block.remove(definition_at);
}

/// A name for the local of `field` of `local`, marked so that settling the
/// declaration's names drops what it does not need.
fn fresh(local: &str, field: &str, names: &mut FxHashSet<String>) -> String {
    let base = match local.rfind(NUMBERED) {
        Some(mark)
            if local[mark + NUMBERED.len_utf8()..]
                .chars()
                .all(|character| character.is_ascii_digit()) =>
        {
            &local[..mark]
        }
        _ => local,
    };
    let mut candidate = format!("{base}{field}{NUMBERED}");
    let mut counter = 2;
    while names.contains(&candidate) {
        candidate = format!("{base}{field}{NUMBERED}{counter}");
        counter += 1;
    }
    names.insert(candidate.clone());
    candidate
}

/// Field reads become the field's local; a whole use becomes a composite of them.
struct Replace<'a> {
    split: &'a Split,
    locals: &'a FxHashMap<String, String>,
}

impl Walk for Replace<'_> {
    fn expression(&mut self, value: &mut GoExpression) {
        match value {
            GoExpression::Field { value: base, name } if is_identifier(base, &self.split.local) => {
                *value = identifier(&self.locals[name.as_str()]);
            }
            GoExpression::Identifier(name) if *name == self.split.local => {
                let fields = self
                    .split
                    .fields
                    .iter()
                    .map(|(field, _)| (Some(field.clone()), identifier(&self.locals[field])))
                    .collect();
                let type_ = GoType::Named(self.split.type_name.clone());
                *value = GoExpression::Composite { type_, fields };
            }
            _ => go_traversal::expression(self, value),
        }
    }
}

/// How a local is used: which fields are read and written, how often it is
/// used whole, and whether anything keeps it whole.
struct Census<'a> {
    local: &'a str,
    fields: &'a [(String, GoType)],
    reads: FxHashMap<String, usize>,
    targets: FxHashMap<String, usize>,
    whole: usize,
    defined: bool,
    /// How many loops enclose the code visited, and the local's definition.
    depth: usize,
    defined_at: usize,
    /// Whether a field is written inside a loop the definition is outside of.
    written_in_loop: bool,
    changed_in_loop: bool,
    parameter: bool,
    refused: bool,
    in_literal: bool,
    in_header: bool,
}

impl<'a> Census<'a> {
    fn new(local: &'a str, fields: &'a [(String, GoType)], parameter: bool) -> Self {
        Census {
            local,
            fields,
            reads: FxHashMap::default(),
            targets: FxHashMap::default(),
            whole: 0,
            defined: parameter,
            depth: 0,
            defined_at: 0,
            written_in_loop: false,
            changed_in_loop: false,
            parameter,
            refused: false,
            in_literal: false,
            in_header: false,
        }
    }

    /// The fields that need a local, when the local is to be split.
    fn needed(&self) -> Option<Vec<String>> {
        let kept_in_memory = self.fields.len() > REGISTER_FIELDS;
        let carried = kept_in_memory && self.changed_in_loop;
        let worthwhile = if self.parameter { carried } else { self.written_in_loop || carried };
        if self.refused || !self.defined || !worthwhile {
            return None;
        }
        let count =
            |map: &FxHashMap<String, usize>, field: &str| map.get(field).copied().unwrap_or(0);
        let read = |field: &str| count(&self.reads, field) > count(&self.targets, field);
        // A field that is written but never read would be a Go local declared and not used.
        if self.whole == 0 && self.targets.keys().any(|field| !read(field)) {
            return None;
        }
        let needed: Vec<String> = self
            .fields
            .iter()
            .map(|(field, _)| field)
            .filter(|field| self.whole > 0 || read(field))
            .cloned()
            .collect();
        (!needed.is_empty()).then_some(needed)
    }

    fn is_field(&self, name: &str) -> bool {
        self.fields.iter().any(|(field, _)| field == name)
    }

    fn binds(&mut self, name: &str) {
        self.refused |= name == self.local;
    }

    /// Whether a definition's or a whole assignment's value can be taken apart
    /// field by field without evaluating anything twice, out of order or not
    /// at all. A whole assignment's composite names every field, as it has no
    /// statement to declare a zero field in.
    fn splits(&self, value: &GoExpression, covers: bool) -> bool {
        match value {
            GoExpression::Composite { fields, .. } => {
                let known = |field: &Option<String>| {
                    field.as_deref().is_some_and(|field| self.is_field(field))
                };
                fields.iter().all(|(field, value)| known(field) && is_pure(value))
                    && (!covers || fields.len() == self.fields.len())
            }
            place => is_place(place),
        }
    }

    fn looped(&mut self, body: &mut Vec<GoStatement>) {
        self.depth += 1;
        self.block(body);
        self.depth -= 1;
    }

    fn header(&mut self, value: &mut GoExpression) {
        let outside = std::mem::replace(&mut self.in_header, true);
        self.expression(value);
        self.in_header = outside;
    }
}

impl Walk for Census<'_> {
    fn statement(&mut self, statement: &mut GoStatement) {
        match statement {
            GoStatement::Define { names, values }
                if names.iter().any(|name| name == self.local) =>
            {
                let single = names.len() == 1 && values.len() == 1;
                if !single || !self.splits(&values[0], false) || self.in_literal || self.defined {
                    self.refused = true;
                }
                self.defined = true;
                self.defined_at = self.depth;
            }
            GoStatement::Variable { name, value, .. } if name == self.local => {
                if value.as_ref().is_some_and(|value| !self.splits(value, false))
                    || self.in_literal
                    || self.defined
                {
                    self.refused = true;
                }
                self.defined = true;
                self.defined_at = self.depth;
            }
            GoStatement::Assign { targets, values } => {
                for target in targets.iter() {
                    if is_identifier(target, self.local) {
                        let single = targets.len() == 1 && values.len() == 1;
                        if !single || !self.splits(&values[0], true) {
                            self.refused = true;
                        }
                        self.changed_in_loop |= self.depth > 0;
                        values.iter_mut().for_each(|value| self.expression(value));
                        return;
                    }
                    if let Some(field) = written_field(target, self.local) {
                        *self.targets.entry(field.to_string()).or_insert(0) += 1;
                        self.written_in_loop |= self.depth > self.defined_at;
                        self.changed_in_loop |= self.depth > 0;
                    }
                }
            }
            GoStatement::IfAssert { name, value, then, .. } => {
                self.binds(name);
                self.header(value);
                self.block(then);
                return;
            }
            GoStatement::Range { index, element, iterable, body } => {
                index.iter().for_each(|index| self.refused |= index == self.local);
                self.binds(&element.clone());
                self.header(iterable);
                self.looped(body);
                return;
            }
            GoStatement::Counting { variable, start, end, body } => {
                self.refused |= variable == self.local;
                self.header(start);
                self.header(end);
                self.looped(body);
                return;
            }
            GoStatement::CountingDown { variable, start, body } => {
                self.refused |= variable == self.local;
                self.header(start);
                self.looped(body);
                return;
            }
            GoStatement::Loop(body) | GoStatement::LabeledLoop { body, .. } => {
                self.looped(body);
                return;
            }
            GoStatement::If { condition, then, otherwise } => {
                self.header(condition);
                self.block(then);
                self.block(otherwise);
                return;
            }
            GoStatement::Switch { value, cases, default } => {
                if let Some(value) = value {
                    self.header(value);
                }
                for case in cases {
                    case.values.iter_mut().for_each(|value| self.header(value));
                    self.block(&mut case.body);
                }
                if let Some(default) = default {
                    default.covers.iter_mut().for_each(|value| self.header(value));
                    self.block(&mut default.body);
                }
                return;
            }
            _ => {}
        }
        go_traversal::statement(self, statement);
    }

    fn expression(&mut self, value: &mut GoExpression) {
        match value {
            GoExpression::Field { value: base, name } if is_identifier(base, self.local) => {
                self.refused |= !self.is_field(name) || self.in_literal;
                *self.reads.entry(name.clone()).or_insert(0) += 1;
            }
            GoExpression::Identifier(name) if name == self.local => {
                self.refused |= self.in_literal || self.in_header;
                self.whole += 1;
            }
            GoExpression::Address(inner) if target_root(inner) == Some(self.local) => {
                self.refused = true;
            }
            GoExpression::Unary { operator: "&", operand }
                if target_root(operand) == Some(self.local) =>
            {
                self.refused = true;
            }
            GoExpression::Function { parameters, body, .. } => {
                parameters.iter().for_each(|(name, _)| self.refused |= name == self.local);
                let outside = std::mem::replace(&mut self.in_literal, true);
                self.block(body);
                self.in_literal = outside;
            }
            _ => go_traversal::expression(self, value),
        }
    }
}

/// The field of `local` an assignment target writes into: `local.F` or a part of it.
fn written_field<'e>(target: &'e GoExpression, local: &str) -> Option<&'e str> {
    match target {
        GoExpression::Field { value, name } if is_identifier(value, local) => Some(name),
        GoExpression::Field { value, .. } | GoExpression::Index { value, .. } => {
            written_field(value, local)
        }
        _ => None,
    }
}

/// The locals of a declaration that have a named struct type and a single binding.
struct Types<'s> {
    structs: &'s Structs,
    values: FxHashMap<String, String>,
    slices: FxHashMap<String, String>,
    bindings: FxHashMap<String, usize>,
    order: Vec<String>,
}

impl<'s> Types<'s> {
    fn of(declaration: &mut GoDeclaration, structs: &'s Structs) -> Self {
        let mut types = Types {
            structs,
            values: FxHashMap::default(),
            slices: FxHashMap::default(),
            bindings: FxHashMap::default(),
            order: vec![],
        };
        if let GoDeclaration::Function { parameters, .. } = declaration {
            for (name, type_) in parameters.iter() {
                types.bind_typed(name, type_);
            }
        }
        go_traversal::declaration(&mut types, declaration);
        types
    }

    fn single_values(&self) -> Vec<(String, String)> {
        self.order
            .iter()
            .filter(|name| self.bindings.get(*name) == Some(&1))
            .filter_map(|name| Some((name.clone(), self.values.get(name)?.clone())))
            .collect()
    }

    fn struct_name(&self, type_: &GoType) -> Option<String> {
        match type_ {
            GoType::Named(name) if self.structs.contains_key(name) => Some(name.clone()),
            _ => None,
        }
    }

    fn bind(&mut self, name: &str, value: Option<String>, slice: Option<String>) {
        let count = self.bindings.entry(name.to_string()).or_insert(0);
        *count += 1;
        if *count == 1 {
            self.order.push(name.to_string());
        }
        if let Some(value) = value {
            self.values.insert(name.to_string(), value);
        }
        if let Some(slice) = slice {
            self.slices.insert(name.to_string(), slice);
        }
    }

    fn bind_typed(&mut self, name: &str, type_: &GoType) {
        let slice = match type_ {
            GoType::Slice(element) => self.struct_name(element),
            _ => None,
        };
        self.bind(name, self.struct_name(type_), slice);
    }

    /// The struct type of a value, or of a slice's elements.
    fn type_of(&self, value: &GoExpression) -> (Option<String>, Option<String>) {
        match value {
            GoExpression::Identifier(name) => {
                (self.values.get(name).cloned(), self.slices.get(name).cloned())
            }
            GoExpression::Composite { type_: GoType::Slice(element), .. } => {
                (None, self.struct_name(element))
            }
            GoExpression::Composite { type_, .. } => (self.struct_name(type_), None),
            GoExpression::Index { value, .. } => match &**value {
                GoExpression::Identifier(name) => (self.slices.get(name).cloned(), None),
                _ => (None, None),
            },
            _ => (None, None),
        }
    }
}

impl Walk for Types<'_> {
    fn statement(&mut self, statement: &mut GoStatement) {
        match statement {
            GoStatement::Define { names, values } => {
                for (position, name) in names.iter().enumerate() {
                    let (value, slice) = match values.get(position) {
                        Some(value) if names.len() == values.len() => self.type_of(value),
                        _ => (None, None),
                    };
                    self.bind(name, value, slice);
                }
            }
            GoStatement::Variable { name, type_, .. }
            | GoStatement::IfAssert { name, type_, .. } => {
                self.bind_typed(&name.clone(), &type_.clone())
            }
            GoStatement::Range { index, element, iterable, .. } => {
                if let Some(index) = index {
                    self.bind(index, None, None);
                }
                let (_, elements) = self.type_of(iterable);
                self.bind(element, elements, None);
            }
            GoStatement::Counting { variable, .. } | GoStatement::CountingDown { variable, .. } => {
                self.bind(variable, None, None)
            }
            _ => {}
        }
        go_traversal::statement(self, statement);
    }

    fn expression(&mut self, value: &mut GoExpression) {
        if let GoExpression::Function { parameters, .. } = value {
            for (name, type_) in parameters.iter() {
                self.bind_typed(name, type_);
            }
        }
        go_traversal::expression(self, value);
    }
}

/// An expression that can be evaluated again, or not at all, with no difference:
/// it neither calls, nor panics, nor reads anything a field local could change.
fn is_pure(value: &GoExpression) -> bool {
    match value {
        GoExpression::Identifier(_)
        | GoExpression::Qualified { .. }
        | GoExpression::Integer(_)
        | GoExpression::Float(_)
        | GoExpression::String(_)
        | GoExpression::Rune(_)
        | GoExpression::Boolean(_) => true,
        GoExpression::Field { value, .. } => is_pure(value),
        GoExpression::Binary { operator, left, right } => {
            !matches!(*operator, "/" | "%") && is_pure(left) && is_pure(right)
        }
        GoExpression::Unary { operator, operand } => {
            matches!(*operator, "-" | "!" | "^" | "+") && is_pure(operand)
        }
        _ => false,
    }
}

/// A place whose fields can be read one by one: a local, or a field or an
/// element of one at a plain index.
fn is_place(value: &GoExpression) -> bool {
    match value {
        GoExpression::Identifier(name) => name != "nil",
        GoExpression::Field { value, .. } => is_place(value),
        GoExpression::Index { value, index } => {
            is_place(value)
                && matches!(**index, GoExpression::Identifier(_) | GoExpression::Integer(_))
        }
        _ => false,
    }
}

fn is_identifier(value: &GoExpression, name: &str) -> bool {
    matches!(value, GoExpression::Identifier(identifier) if identifier == name)
}

fn identifier(name: &str) -> GoExpression {
    GoExpression::Identifier(name.to_string())
}

/// Go keeps a struct of more than this many fields in memory, so a composite
/// of one assigned to an element is first built on the stack and then copied.
const REGISTER_FIELDS: usize = 4;

/// `elements[i] = T{F: a, G: b, ...}`, for a struct that Go would build on the
/// stack first, becomes `elements[i].F = a`, `elements[i].G = b`, ...: the
/// fields are written where they live. The composite names every field and
/// its values neither call nor mention the element's slice or index, so no
/// field write can change what a later one reads or where it goes.
pub(super) fn store_fields_in_place(declarations: &mut [GoDeclaration], structs: &Structs) {
    for declaration in declarations {
        go_traversal::each_block_in_declaration(declaration, |block| {
            let mut position = 0;
            while position < block.len() {
                match stored_fields(&block[position], structs) {
                    Some(statements) => {
                        let count = statements.len();
                        block.splice(position..=position, statements);
                        position += count;
                    }
                    None => position += 1,
                }
            }
        });
    }
}

fn stored_fields(statement: &GoStatement, structs: &Structs) -> Option<Vec<GoStatement>> {
    let GoStatement::Assign { targets, values } = statement else { return None };
    let ([target @ GoExpression::Index { value: elements, index }], [composite]) =
        (targets.as_slice(), values.as_slice())
    else {
        return None;
    };
    let GoExpression::Composite { type_: GoType::Named(type_name), fields } = composite else {
        return None;
    };
    let declared = structs.get(type_name)?;
    let named = |name: &str| fields.iter().any(|(field, _)| field.as_deref() == Some(name));
    if declared.len() <= REGISTER_FIELDS
        || fields.len() != declared.len()
        || !declared.iter().all(|(field, _)| named(field))
        || !is_place(target)
    {
        return None;
    }
    let mentioned =
        identifiers(&GoExpression::Index { value: elements.clone(), index: index.clone() });
    let independent =
        |value: &GoExpression| is_pure(value) && identifiers(value).is_disjoint(&mentioned);
    if !fields.iter().all(|(_, value)| independent(value)) {
        return None;
    }
    Some(
        fields
            .iter()
            .map(|(field, value)| GoStatement::Assign {
                targets: vec![GoExpression::Field {
                    value: Box::new(target.clone()),
                    name: field.clone().expect("a named field"),
                }],
                values: vec![value.clone()],
            })
            .collect(),
    )
}

fn identifiers(value: &GoExpression) -> FxHashSet<String> {
    let mut found = FxHashSet::default();
    go_traversal::each_expression_in_statement(
        &mut GoStatement::Expression(value.clone()),
        |expression| {
            if let GoExpression::Identifier(name) = expression {
                found.insert(name.clone());
            }
        },
    );
    found
}
