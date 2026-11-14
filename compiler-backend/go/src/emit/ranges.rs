//! Range loops that read their element's fields in place.
//!
//! `for _, element := range array` copies every element into `element`, a block
//! copy per iteration for a large struct even when the body reads one or two
//! fields. When every use of `element` reads a field, the loop becomes
//! `for index := range array` and `element.field` becomes `array[index].field`.
//! Arrays are immutable, so each read sees what the copy would have held. Only
//! structs and pointers to them have fields, so scalar loops keep reading well.
//!
//! A loop keeps its copy when the element is used whole, assigned or
//! addressed, when a closure reads it (the closure could outlive a later
//! reassignment of the array variable), when a method may be called on it, or
//! when the array variable may change during the loop.

use rustc_hash::FxHashSet;

use crate::syntax::{GoDeclaration, GoExpression, GoStatement};

pub fn read_elements_in_place(declarations: &mut [GoDeclaration]) {
    for declaration in declarations {
        let mut names = FxHashSet::default();
        declaration.for_each_name_mut(&mut |name| {
            let (crate::syntax::Name::Reference(name) | crate::syntax::Name::Binder(name)) = name;
            names.insert(name.clone());
        });
        match declaration {
            GoDeclaration::Function { body, .. } => statements(body, &mut names),
            GoDeclaration::Variable { value, .. } => expression(value, &mut names),
            _ => {}
        }
    }
}

fn statements(body: &mut [GoStatement], names: &mut FxHashSet<String>) {
    for statement in body {
        self::statement(statement, names);
    }
}

fn statement(statement: &mut GoStatement, names: &mut FxHashSet<String>) {
    match statement {
        GoStatement::Define { values, .. } => values.iter_mut().for_each(|v| expression(v, names)),
        GoStatement::Variable { value, .. } => {
            if let Some(value) = value {
                expression(value, names);
            }
        }
        GoStatement::Assign { targets, values } => {
            targets.iter_mut().for_each(|v| expression(v, names));
            values.iter_mut().for_each(|v| expression(v, names));
        }
        GoStatement::Expression(value) | GoStatement::Defer(value) => expression(value, names),
        GoStatement::Return(value) => {
            if let Some(value) = value {
                expression(value, names);
            }
        }
        GoStatement::If { condition, then, otherwise } => {
            expression(condition, names);
            statements(then, names);
            statements(otherwise, names);
        }
        GoStatement::Switch { value, cases, default } => {
            if let Some(value) = value {
                expression(value, names);
            }
            for case in cases {
                case.values.iter_mut().for_each(|v| expression(v, names));
                statements(&mut case.body, names);
            }
            if let Some(default) = default {
                statements(&mut default.body, names);
            }
        }
        GoStatement::IfAssert { value, then, .. } => {
            expression(value, names);
            statements(then, names);
        }
        GoStatement::Loop(body)
        | GoStatement::LabeledLoop { body, .. }
        | GoStatement::Block(body) => statements(body, names),
        GoStatement::Counting { start, end, body, .. } => {
            expression(start, names);
            expression(end, names);
            statements(body, names);
        }
        GoStatement::CountingDown { start, body, .. } => {
            expression(start, names);
            statements(body, names);
        }
        GoStatement::Range { index, element, iterable, body } => {
            expression(iterable, names);
            statements(body, names);
            if let GoExpression::Identifier(array) = iterable
                && element != "_"
                && reads_in_place(body, element, array)
            {
                let index = index.get_or_insert_with(|| fresh(names, element)).clone();
                let array = array.clone();
                let element = std::mem::replace(element, "_".to_string());
                read_from_array(body, &element, &array, &index);
            }
        }
        GoStatement::Continue | GoStatement::Break | GoStatement::BreakTo(_) => {}
    }
}

fn expression(value: &mut GoExpression, names: &mut FxHashSet<String>) {
    match value {
        GoExpression::Function { body, .. } => statements(body, names),
        GoExpression::Call { function, arguments } => {
            expression(function, names);
            arguments.iter_mut().for_each(|v| expression(v, names));
        }
        GoExpression::Binary { left, right, .. } => {
            expression(left, names);
            expression(right, names);
        }
        GoExpression::Index { value, index } => {
            expression(value, names);
            expression(index, names);
        }
        GoExpression::Unary { operand: value, .. }
        | GoExpression::Field { value, .. }
        | GoExpression::Address(value)
        | GoExpression::Conversion { value, .. }
        | GoExpression::TypeAssertion { value, .. }
        | GoExpression::Spread(value)
        | GoExpression::Instantiation { function: value, .. } => expression(value, names),
        GoExpression::Composite { fields, .. } => {
            fields.iter_mut().for_each(|(_, v)| expression(v, names))
        }
        GoExpression::Identifier(_)
        | GoExpression::Qualified { .. }
        | GoExpression::Integer(_)
        | GoExpression::Float(_)
        | GoExpression::String(_)
        | GoExpression::Rune(_)
        | GoExpression::Boolean(_)
        | GoExpression::Type(_) => {}
    }
}

fn fresh(names: &mut FxHashSet<String>, element: &str) -> String {
    let mut candidate = format!("{element}Index");
    let mut suffix = 2;
    while names.contains(&candidate) {
        candidate = format!("{element}Index{suffix}");
        suffix += 1;
    }
    names.insert(candidate.clone());
    candidate
}

/// Whether `element` only has its fields read in `body`, outside closures, and
/// `array` is neither rebound nor reassigned there.
fn reads_in_place(body: &[GoStatement], element: &str, array: &str) -> bool {
    let mut check = Check { element, array, reads: 0, refused: false };
    check.statements(body, false);
    !check.refused && check.reads > 0
}

struct Check<'a> {
    element: &'a str,
    array: &'a str,
    reads: usize,
    refused: bool,
}

impl Check<'_> {
    fn binds(&mut self, name: &str) {
        if name == self.element || name == self.array {
            self.refused = true;
        }
    }

    fn statements(&mut self, body: &[GoStatement], closure: bool) {
        for statement in body {
            self.statement(statement, closure);
        }
    }

    fn statement(&mut self, statement: &GoStatement, closure: bool) {
        match statement {
            GoStatement::Define { names, values } => {
                names.iter().for_each(|name| self.binds(name));
                values.iter().for_each(|v| self.expression(v, closure));
            }
            GoStatement::Variable { name, value, .. } => {
                self.binds(name);
                if let Some(value) = value {
                    self.expression(value, closure);
                }
            }
            GoStatement::Assign { targets, values } => {
                for target in targets {
                    let mut root = target;
                    while let GoExpression::Field { value, .. }
                    | GoExpression::Index { value, .. } = root
                    {
                        root = value;
                    }
                    if let GoExpression::Identifier(name) = root
                        && (name == self.element || name == self.array)
                    {
                        self.refused = true;
                    }
                    self.expression(target, closure);
                }
                values.iter().for_each(|v| self.expression(v, closure));
            }
            GoStatement::Expression(value) | GoStatement::Defer(value) => {
                self.expression(value, closure)
            }
            GoStatement::Return(value) => {
                if let Some(value) = value {
                    self.expression(value, closure);
                }
            }
            GoStatement::If { condition, then, otherwise } => {
                self.expression(condition, closure);
                self.statements(then, closure);
                self.statements(otherwise, closure);
            }
            GoStatement::Switch { value, cases, default } => {
                if let Some(value) = value {
                    self.expression(value, closure);
                }
                for case in cases {
                    case.values.iter().for_each(|v| self.expression(v, closure));
                    self.statements(&case.body, closure);
                }
                if let Some(default) = default {
                    default.covers.iter().for_each(|v| self.expression(v, closure));
                    self.statements(&default.body, closure);
                }
            }
            GoStatement::IfAssert { name, value, then, .. } => {
                self.binds(name);
                self.expression(value, closure);
                self.statements(then, closure);
            }
            GoStatement::Loop(body)
            | GoStatement::LabeledLoop { body, .. }
            | GoStatement::Block(body) => self.statements(body, closure),
            GoStatement::Range { index, element, iterable, body } => {
                if let Some(index) = index {
                    self.binds(index);
                }
                self.binds(element);
                self.expression(iterable, closure);
                self.statements(body, closure);
            }
            GoStatement::Counting { variable, start, end, body } => {
                self.binds(variable);
                self.expression(start, closure);
                self.expression(end, closure);
                self.statements(body, closure);
            }
            GoStatement::CountingDown { variable, start, body } => {
                self.binds(variable);
                self.expression(start, closure);
                self.statements(body, closure);
            }
            GoStatement::Continue | GoStatement::Break | GoStatement::BreakTo(_) => {}
        }
    }

    fn expression(&mut self, value: &GoExpression, closure: bool) {
        match value {
            GoExpression::Field { value: base, .. } if matches!(&**base, GoExpression::Identifier(name) if name == self.element) =>
            {
                if closure {
                    self.refused = true;
                }
                self.reads += 1;
            }
            GoExpression::Identifier(name) => {
                if name == self.element {
                    self.refused = true;
                }
            }
            GoExpression::Address(operand) => {
                if let GoExpression::Identifier(name) = &**operand
                    && (name == self.array || name == self.element)
                {
                    self.refused = true;
                }
                self.expression(operand, closure);
            }
            GoExpression::Function { parameters, body, .. } => {
                parameters.iter().for_each(|(name, _)| self.binds(name));
                self.statements(body, true);
            }
            GoExpression::Call { function, arguments } => {
                // An exported name on the element may be a method of a
                // go-support type, whose receiver could be the element's address.
                if let GoExpression::Field { value: base, name } = &**function
                    && let GoExpression::Identifier(base) = &**base
                    && base == self.element
                    && name.starts_with(|c: char| c.is_uppercase())
                {
                    self.refused = true;
                }
                self.expression(function, closure);
                arguments.iter().for_each(|v| self.expression(v, closure));
            }
            GoExpression::Binary { left, right, .. } => {
                self.expression(left, closure);
                self.expression(right, closure);
            }
            GoExpression::Index { value, index } => {
                self.expression(value, closure);
                self.expression(index, closure);
            }
            GoExpression::Unary { operand: value, .. }
            | GoExpression::Field { value, .. }
            | GoExpression::Conversion { value, .. }
            | GoExpression::TypeAssertion { value, .. }
            | GoExpression::Spread(value)
            | GoExpression::Instantiation { function: value, .. } => {
                self.expression(value, closure)
            }
            GoExpression::Composite { fields, .. } => {
                fields.iter().for_each(|(_, v)| self.expression(v, closure))
            }
            GoExpression::Qualified { .. }
            | GoExpression::Integer(_)
            | GoExpression::Float(_)
            | GoExpression::String(_)
            | GoExpression::Rune(_)
            | GoExpression::Boolean(_)
            | GoExpression::Type(_) => {}
        }
    }
}

fn read_from_array(body: &mut [GoStatement], element: &str, array: &str, index: &str) {
    let mut replace = |value: &mut GoExpression| {
        if matches!(value, GoExpression::Identifier(name) if name == element) {
            *value = GoExpression::Index {
                value: Box::new(GoExpression::Identifier(array.to_string())),
                index: Box::new(GoExpression::Identifier(index.to_string())),
            };
        }
    };
    for statement in body {
        each_expression_in_statement(statement, &mut replace);
    }
}

pub(super) fn each_expression_in_statement(
    statement: &mut GoStatement,
    visit: &mut dyn FnMut(&mut GoExpression),
) {
    fn block(body: &mut [GoStatement], visit: &mut dyn FnMut(&mut GoExpression)) {
        for statement in body {
            each_expression_in_statement(statement, visit);
        }
    }
    match statement {
        GoStatement::Define { values, .. } => {
            values.iter_mut().for_each(|v| each_expression(v, visit))
        }
        GoStatement::Variable { value, .. } => {
            if let Some(value) = value {
                each_expression(value, visit);
            }
        }
        GoStatement::Assign { targets, values } => {
            targets.iter_mut().for_each(|v| each_expression(v, visit));
            values.iter_mut().for_each(|v| each_expression(v, visit));
        }
        GoStatement::Expression(value) | GoStatement::Defer(value) => each_expression(value, visit),
        GoStatement::Return(value) => {
            if let Some(value) = value {
                each_expression(value, visit);
            }
        }
        GoStatement::If { condition, then, otherwise } => {
            each_expression(condition, visit);
            block(then, visit);
            block(otherwise, visit);
        }
        GoStatement::Switch { value, cases, default } => {
            if let Some(value) = value {
                each_expression(value, visit);
            }
            for case in cases {
                case.values.iter_mut().for_each(|v| each_expression(v, visit));
                block(&mut case.body, visit);
            }
            if let Some(default) = default {
                default.covers.iter_mut().for_each(|v| each_expression(v, visit));
                block(&mut default.body, visit);
            }
        }
        GoStatement::IfAssert { value, then, .. } => {
            each_expression(value, visit);
            block(then, visit);
        }
        GoStatement::Loop(body)
        | GoStatement::LabeledLoop { body, .. }
        | GoStatement::Block(body) => block(body, visit),
        GoStatement::Range { iterable, body, .. } => {
            each_expression(iterable, visit);
            block(body, visit);
        }
        GoStatement::Counting { start, end, body, .. } => {
            each_expression(start, visit);
            each_expression(end, visit);
            block(body, visit);
        }
        GoStatement::CountingDown { start, body, .. } => {
            each_expression(start, visit);
            block(body, visit);
        }
        GoStatement::Continue | GoStatement::Break | GoStatement::BreakTo(_) => {}
    }
}

/// Visits `value` and every expression inside it, children first.
pub(super) fn each_expression(value: &mut GoExpression, visit: &mut dyn FnMut(&mut GoExpression)) {
    match value {
        GoExpression::Function { body, .. } => {
            for statement in body {
                each_expression_in_statement(statement, visit);
            }
        }
        GoExpression::Call { function, arguments } => {
            each_expression(function, visit);
            arguments.iter_mut().for_each(|v| each_expression(v, visit));
        }
        GoExpression::Binary { left, right, .. } => {
            each_expression(left, visit);
            each_expression(right, visit);
        }
        GoExpression::Index { value, index } => {
            each_expression(value, visit);
            each_expression(index, visit);
        }
        GoExpression::Unary { operand: value, .. }
        | GoExpression::Field { value, .. }
        | GoExpression::Address(value)
        | GoExpression::Conversion { value, .. }
        | GoExpression::TypeAssertion { value, .. }
        | GoExpression::Spread(value)
        | GoExpression::Instantiation { function: value, .. } => each_expression(value, visit),
        GoExpression::Composite { fields, .. } => {
            fields.iter_mut().for_each(|(_, v)| each_expression(v, visit))
        }
        GoExpression::Identifier(_)
        | GoExpression::Qualified { .. }
        | GoExpression::Integer(_)
        | GoExpression::Float(_)
        | GoExpression::String(_)
        | GoExpression::Rune(_)
        | GoExpression::Boolean(_)
        | GoExpression::Type(_) => {}
    }
    visit(value);
}
