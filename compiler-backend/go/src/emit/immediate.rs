//! Function literals called where they are made, `func(coerced int) T { return g(coerced) }(e)`,
//! become the expression they return with the parameters replaced, `g(e)`, where that keeps
//! what the code does:
//!
//! - Go types stay as they were: no parameter or result is an interface, which a value meets
//!   through an implicit conversion, and an untyped constant argument is converted explicitly;
//! - a constant replaces any number of uses, and so does a name or a field read of a variable
//!   that keeps its value; any other variable is read outside the body's literals only;
//! - any other argument replaces one use outside the body's literals, so that it is evaluated
//!   once: a function literal anywhere, and else only as the first thing the body does work on.
//!
//! Emission names a declaration's locals apart, so names mean the same in the body as at the call.

use rustc_hash::{FxHashMap, FxHashSet};

use super::{is_simple, is_untyped_constant, path_root};
use crate::go_traversal::{self, Walk};
use crate::syntax::{GoDeclaration, GoExpression, GoStatement, GoType};

pub(super) fn reduce_immediate_calls(declarations: &mut [GoDeclaration]) {
    for declaration in declarations {
        let mut changing = Changing::default();
        go_traversal::declaration(&mut changing, declaration);
        go_traversal::declaration(
            &mut Immediate { changing, free_variables_change: false },
            declaration,
        );
    }
}

/// [`reduce_immediate_calls`] in one expression, whose free variables may change.
pub(super) fn reduce_immediate_calls_in(expression: &mut GoExpression) {
    let mut changing = Changing::default();
    changing.expression(expression);
    Immediate { changing, free_variables_change: true }.expression(expression)
}

/// Whether an immediately called literal is left in the expression.
pub(super) fn calls_a_literal(expression: &GoExpression) -> bool {
    let mut found = false;
    go_traversal::each_expression_in_statement(
        &mut GoStatement::Expression(expression.clone()),
        |value| {
            found |= matches!(value, GoExpression::Call { function, .. }
            if matches!(function.as_ref(), GoExpression::Function { .. }));
        },
    );
    found
}

struct Immediate {
    changing: Changing,
    free_variables_change: bool,
}

impl Walk for Immediate {
    fn expression(&mut self, value: &mut GoExpression) {
        go_traversal::expression(self, value);
        while let Some(reduced) = self.reduced(value) {
            *value = reduced;
        }
    }
}

impl Immediate {
    fn keeps_value(&self, name: &str) -> bool {
        let known = !self.free_variables_change || self.changing.declared.contains_key(name);
        known && !self.changing.names.contains(name)
    }

    fn reduced(&self, value: &GoExpression) -> Option<GoExpression> {
        let GoExpression::Call { function, arguments } = value else { return None };
        let GoExpression::Function { parameters, result: Some(result), body } = function.as_ref()
        else {
            return None;
        };
        let ([GoStatement::Return(Some(returned))]
        | [GoStatement::Line(_), GoStatement::Return(Some(returned))]) = body.as_slice()
        else {
            return None;
        };
        let typed = !is_interface(result) && !is_untyped_constant(returned);
        if !typed || parameters.len() != arguments.len() {
            return None;
        }
        let mut returned = returned.clone();
        for ((parameter, type_), argument) in parameters.iter().zip(arguments) {
            if is_interface(type_) || !self.keeps_value(parameter) {
                return None;
            }
            let everywhere = uses(&returned, parameter);
            let outside = uses_outside_literals(&returned, parameter);
            let replaceable = match argument {
                GoExpression::Identifier(_) | GoExpression::Field { .. } if is_simple(argument) => {
                    let kept = path_root(argument).is_some_and(|root| self.keeps_value(root));
                    everywhere > 0 && (kept || outside == everywhere)
                }
                argument if is_simple(argument) => everywhere > 0,
                GoExpression::Function { .. } => everywhere == 1 && outside == 1,
                _ => everywhere == 1 && outside == 1 && first_work(&returned, parameter),
            };
            if !replaceable {
                return None;
            }
            let argument = match argument {
                constant if is_untyped_constant(constant) => GoExpression::Conversion {
                    type_: type_.clone(),
                    value: Box::new(constant.clone()),
                },
                argument => argument.clone(),
            };
            let mut statement = GoStatement::Expression(returned);
            go_traversal::each_expression_in_statement(&mut statement, |value| {
                if is_named(value, parameter) {
                    *value = argument.clone();
                }
            });
            let GoStatement::Expression(replaced) = statement else { unreachable!() };
            returned = replaced;
        }
        Some(returned)
    }
}

fn is_interface(type_: &GoType) -> bool {
    matches!(type_, GoType::Any | GoType::Erased(_))
}

fn is_named(value: &GoExpression, name: &str) -> bool {
    matches!(value, GoExpression::Identifier(identifier) if identifier == name)
}

fn uses(expression: &GoExpression, parameter: &str) -> usize {
    let mut uses = 0;
    let mut statement = GoStatement::Expression(expression.clone());
    go_traversal::each_expression_in_statement(&mut statement, |value| {
        uses += usize::from(is_named(value, parameter))
    });
    uses
}

fn uses_outside_literals(expression: &GoExpression, parameter: &str) -> usize {
    let (children, _) = evaluated(expression);
    let own = usize::from(is_named(expression, parameter));
    own + children.into_iter().map(|child| uses_outside_literals(child, parameter)).sum::<usize>()
}

/// Whether the parameter is the first thing in the expression that Go evaluates before any work:
/// a call, a type assertion, an index, a division or a pointer followed, which an argument
/// moved past it could see or come after.
fn first_work(expression: &GoExpression, parameter: &str) -> bool {
    fn first(expression: &GoExpression, parameter: &str) -> Option<bool> {
        if is_named(expression, parameter) {
            return Some(true);
        }
        let (children, works) = evaluated(expression);
        children.into_iter().find_map(|child| first(child, parameter)).or(works.then_some(false))
    }
    first(expression, parameter) == Some(true)
}

/// The parts of an expression Go evaluates with it, in order, outside function literals, and
/// whether the expression itself then does work.
fn evaluated(expression: &GoExpression) -> (Vec<&GoExpression>, bool) {
    match expression {
        GoExpression::Call { function, arguments } => {
            (std::iter::once(function.as_ref()).chain(arguments).collect(), true)
        }
        GoExpression::Binary { operator, left, right } => {
            (vec![left, right], matches!(*operator, "/" | "%"))
        }
        GoExpression::Unary { operator, operand } => (vec![operand], *operator == "*"),
        GoExpression::Index { value, index } => (vec![value, index], true),
        GoExpression::TypeAssertion { value, .. } => (vec![value], true),
        GoExpression::Field { value, .. }
        | GoExpression::Address(value)
        | GoExpression::Conversion { value, .. }
        | GoExpression::Spread(value)
        | GoExpression::Instantiation { function: value, .. } => (vec![value], false),
        GoExpression::Composite { fields, .. } => (fields.iter().map(|(_, f)| f).collect(), false),
        _ => (vec![], false),
    }
}

/// The variables that may change once they have a value: any assigned in a loop or a function
/// literal that can run again after the variable got its value, and any whose field, element or
/// address is written. One assignment per branch after `var result T` gives a value.
#[derive(Default)]
struct Changing {
    names: FxHashSet<String>,
    /// How many loops and function literals enclose the code, and each declaration.
    repeated: usize,
    declared: FxHashMap<String, usize>,
}

impl Changing {
    fn declare<'n>(&mut self, names: impl IntoIterator<Item = &'n String>) {
        for name in names {
            self.declared.insert(name.clone(), self.repeated);
        }
    }

    fn repeating(&mut self, names: Vec<String>, walk: impl FnOnce(&mut Self)) {
        self.repeated += 1;
        self.declare(&names);
        walk(self);
        self.repeated -= 1;
    }
}

/// The variable a place lies within.
fn written_root(place: &GoExpression) -> Option<&String> {
    match place {
        GoExpression::Identifier(name) => Some(name),
        GoExpression::Field { value, .. }
        | GoExpression::Index { value, .. }
        | GoExpression::Unary { operand: value, .. } => written_root(value),
        _ => None,
    }
}

impl Walk for Changing {
    fn expression(&mut self, value: &mut GoExpression) {
        match value {
            GoExpression::Address(place) => {
                self.names.extend(written_root(place).cloned());
                go_traversal::expression(self, value);
            }
            GoExpression::Function { parameters, .. } => {
                let names = parameters.iter().map(|(name, _)| name.clone()).collect();
                self.repeating(names, |changing| go_traversal::expression(changing, value))
            }
            _ => go_traversal::expression(self, value),
        }
    }

    fn statement(&mut self, statement: &mut GoStatement) {
        match statement {
            GoStatement::Assign { targets, .. } => {
                for target in targets.iter() {
                    let Some(root) = written_root(target) else { continue };
                    let declared = self.declared.get(root).copied().unwrap_or(0);
                    if !is_named(target, root) || self.repeated > declared {
                        self.names.insert(root.clone());
                    }
                }
            }
            GoStatement::Define { names, .. } => self.declare(names.iter()),
            GoStatement::Variable { name, .. } | GoStatement::IfAssert { name, .. } => {
                self.declare([&*name])
            }
            GoStatement::Range { index, element, .. } => {
                let names = index.iter().chain([&*element]).cloned().collect();
                return self
                    .repeating(names, |changing| go_traversal::statement(changing, statement));
            }
            GoStatement::Counting { variable, .. } | GoStatement::CountingDown { variable, .. } => {
                self.names.insert(variable.clone());
                return self
                    .repeating(vec![], |changing| go_traversal::statement(changing, statement));
            }
            GoStatement::Loop(_) | GoStatement::LabeledLoop { .. } => {
                return self
                    .repeating(vec![], |changing| go_traversal::statement(changing, statement));
            }
            _ => {}
        }
        go_traversal::statement(self, statement)
    }
}
