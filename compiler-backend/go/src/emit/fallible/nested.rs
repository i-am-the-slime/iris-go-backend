use rustc_hash::{FxHashMap, FxHashSet};

use super::conventions::Conventions;
use super::rewrite::split_locals_again;
use super::zeros::Zeros;
use super::{Conversion, EitherShape, converter};
use crate::emit::locals::NUMBERED;
use crate::emit::{call, identifier_expression};
use crate::go_traversal::{self, Walk};
use crate::syntax::{GoCase, GoDeclaration, GoDefault, GoExpression, GoStatement, GoType};

/// The functions returning `Either e1 (Either e2 a)` return `(A, E2Failure, E1Failure)`, and the
/// calls that keep both results take the three apart, so that the inner `Either` can be split as
/// the outer one is.
pub(super) struct NestedResults<'n> {
    shapes: &'n FxHashMap<String, EitherShape>,
    zeros: &'n Zeros,
    converters: &'n mut FxHashMap<(String, Conversion), String>,
    /// By function, its outer and inner `Either` types.
    functions: FxHashMap<String, (String, String)>,
}

impl<'n> NestedResults<'n> {
    pub(super) fn new(
        shapes: &'n FxHashMap<String, EitherShape>,
        zeros: &'n Zeros,
        converters: &'n mut FxHashMap<(String, Conversion), String>,
    ) -> NestedResults<'n> {
        NestedResults { shapes, zeros, converters, functions: FxHashMap::default() }
    }

    pub(super) fn flatten(
        &mut self,
        declarations: &mut [GoDeclaration],
        conventions: &Conventions,
    ) {
        for (function, outer) in &conventions.functions {
            if let GoType::Named(inner) = &self.shapes[outer].right
                && self.shapes.contains_key(inner)
            {
                self.functions.insert(function.clone(), (outer.clone(), inner.clone()));
            }
        }
        loop {
            let functions = &mut self.functions;
            let mut uses = NestedUses { functions, owner: None, changed: false };
            for declaration in declarations.iter_mut() {
                if let GoDeclaration::Written { source, .. } = declaration {
                    let written: Vec<String> = uses
                        .functions
                        .keys()
                        .filter(|name| source.contains(name.as_str()))
                        .cloned()
                        .collect();
                    for name in written {
                        uses.functions.remove(&name);
                        uses.changed = true;
                    }
                }
                uses.owner = match declaration {
                    GoDeclaration::Function { name, .. } => Some(name.clone()),
                    _ => None,
                };
                go_traversal::declaration(&mut uses, declaration);
            }
            if !uses.changed {
                break;
            }
        }
        if self.functions.is_empty() {
            return;
        }
        for declaration in declarations.iter_mut() {
            let mut names = declaration.all_names();
            let GoDeclaration::Function { name, result, body, .. } = declaration else { continue };
            let own = self.functions.get(name.as_str()).cloned();
            if let Some((outer, inner)) = &own {
                let (outer, inner) = (&self.shapes[outer], &self.shapes[inner]);
                *result = Some(GoType::Results(vec![
                    inner.right.clone(),
                    inner.failure_type(),
                    outer.failure_type(),
                ]));
            }
            let mut changed = false;
            *body = self.block(std::mem::take(body), own.as_ref(), &mut names, &mut changed);
            if changed {
                split_locals_again(body, self.shapes, self.zeros, self.converters, &mut names);
            }
        }
    }

    fn block(
        &mut self,
        statements: Vec<GoStatement>,
        own: Option<&(String, String)>,
        names: &mut FxHashSet<String>,
        changed: &mut bool,
    ) -> Vec<GoStatement> {
        let mut out = Vec::with_capacity(statements.len());
        for statement in statements {
            self.statement(statement, own, names, changed, &mut out);
        }
        out
    }

    fn statement(
        &mut self,
        statement: GoStatement,
        own: Option<&(String, String)>,
        names: &mut FxHashSet<String>,
        changed: &mut bool,
        out: &mut Vec<GoStatement>,
    ) {
        match statement {
            GoStatement::Define { names: defined, values }
                if defined.len() == 2
                    && let Some((_, inner)) = self.called(&values) =>
            {
                *changed = true;
                let (kept, failure) = (defined[0].clone(), defined[1].clone());
                let (value, inner_failure) = match kept.as_str() {
                    "_" => ("_".to_string(), "_".to_string()),
                    _ => self.fresh(&inner, names),
                };
                out.push(GoStatement::Define {
                    names: vec![value.clone(), inner_failure.clone(), failure],
                    values,
                });
                if kept != "_" {
                    let joined = self.joined(&inner, &value, &inner_failure);
                    out.push(GoStatement::Define { names: vec![kept], values: vec![joined] });
                }
            }
            GoStatement::Assign { targets, values }
                if targets.len() == 2
                    && let Some((_, inner)) = self.called(&values) =>
            {
                *changed = true;
                let kept = match targets[0].unattributed() {
                    GoExpression::Identifier(kept) => kept.clone(),
                    _ => unreachable!("invariant violated: a call's results go to locals"),
                };
                let (value, inner_failure) = match kept.as_str() {
                    "_" => ("_".to_string(), "_".to_string()),
                    _ => self.fresh(&inner, names),
                };
                let shape = &self.shapes[&inner];
                if kept != "_" {
                    out.push(GoStatement::Variable {
                        name: value.clone(),
                        type_: shape.right.clone(),
                        value: None,
                    });
                    out.push(GoStatement::Variable {
                        name: inner_failure.clone(),
                        type_: shape.failure_type(),
                        value: None,
                    });
                }
                let failure = targets[1].clone();
                out.push(GoStatement::Assign {
                    targets: vec![
                        identifier_expression(&value),
                        identifier_expression(&inner_failure),
                        failure,
                    ],
                    values,
                });
                if kept != "_" {
                    let joined = self.joined(&inner, &value, &inner_failure);
                    out.push(GoStatement::Assign {
                        targets: vec![identifier_expression(&kept)],
                        values: vec![joined],
                    });
                }
            }
            GoStatement::Return(Some(value)) if let Some((outer, inner)) = own => {
                let (outer, inner) = (outer.clone(), inner.clone());
                self.returned(value, &outer, &inner, names, out);
            }
            GoStatement::If { condition, then, otherwise } => out.push(GoStatement::If {
                condition,
                then: self.block(then, own, names, changed),
                otherwise: self.block(otherwise, own, names, changed),
            }),
            GoStatement::Switch { value, cases, default } => {
                let cases = cases.into_iter().map(|case| GoCase {
                    values: case.values,
                    body: self.block(case.body, own, names, changed),
                    line: case.line,
                });
                let cases = cases.collect();
                out.push(GoStatement::Switch {
                    value,
                    cases,
                    default: default.map(|default| GoDefault {
                        covers: default.covers,
                        body: self.block(default.body, own, names, changed),
                        line: default.line,
                    }),
                })
            }
            GoStatement::IfAssert { name, value, type_, then } => out.push(GoStatement::IfAssert {
                name,
                value,
                type_,
                then: self.block(then, own, names, changed),
            }),
            GoStatement::Loop(body) => {
                out.push(GoStatement::Loop(self.block(body, own, names, changed)))
            }
            GoStatement::LabeledLoop { label, body } => out.push(GoStatement::LabeledLoop {
                label,
                body: self.block(body, own, names, changed),
            }),
            GoStatement::Range { index, element, iterable, body } => out.push(GoStatement::Range {
                index,
                element,
                iterable,
                body: self.block(body, own, names, changed),
            }),
            GoStatement::Counting { variable, start, end, body } => {
                out.push(GoStatement::Counting {
                    variable,
                    start,
                    end,
                    body: self.block(body, own, names, changed),
                })
            }
            GoStatement::CountingDown { variable, start, body } => {
                out.push(GoStatement::CountingDown {
                    variable,
                    start,
                    body: self.block(body, own, names, changed),
                })
            }
            statement => out.push(statement),
        }
    }

    /// The `return` of a function returning a nested `Either`, returning its three results.
    fn returned(
        &mut self,
        value: GoExpression,
        outer: &str,
        inner: &str,
        names: &mut FxHashSet<String>,
        out: &mut Vec<GoStatement>,
    ) {
        if self.called(std::slice::from_ref(&value)).is_some_and(|(called, _)| called == outer) {
            out.push(GoStatement::Return(Some(value)));
            return;
        }
        let (kept, failure) = match value {
            GoExpression::Results(results) if results.len() == 2 => {
                let mut results = results.into_iter();
                let kept = results.next().expect("invariant violated: two results");
                (kept, results.next().expect("invariant violated: two results"))
            }
            value => {
                let (kept, failure) = self.fresh(outer, names);
                out.push(GoStatement::Define {
                    names: vec![kept.clone(), failure.clone()],
                    values: vec![value],
                });
                (identifier_expression(&kept), identifier_expression(&failure))
            }
        };
        let shape = &self.shapes[inner];
        let apart = match kept.unattributed() {
            GoExpression::Composite { fields, .. } if fields.is_empty() => {
                Some((self.zeros.zero(&shape.right), shape.no_failure()))
            }
            value => shape.construction(value).map(|(left, field)| {
                let side = if left { &shape.left } else { &shape.right };
                let field = field.unwrap_or_else(|| self.zeros.zero(side));
                match left {
                    true => (self.zeros.zero(&shape.right), shape.failed_with(field)),
                    false => (field, shape.no_failure()),
                }
            }),
        };
        let (value, inner_failure) = match apart {
            Some(apart) => apart,
            None => {
                let (value, inner_failure) = self.fresh(inner, names);
                let results = converter(self.converters, inner, Conversion::Results);
                out.push(GoStatement::Define {
                    names: vec![value.clone(), inner_failure.clone()],
                    values: vec![call(identifier_expression(&results), vec![kept])],
                });
                (identifier_expression(&value), identifier_expression(&inner_failure))
            }
        };
        out.push(GoStatement::Return(Some(GoExpression::Results(vec![
            value,
            inner_failure,
            failure,
        ]))));
    }

    /// The function returning a nested `Either` that the one value calls, with its inner type.
    fn called(&self, values: &[GoExpression]) -> Option<(String, String)> {
        let [GoExpression::Call { function, .. }] = values else {
            let [value] = values else { return None };
            let GoExpression::Attributed { value, .. } = value else { return None };
            return self.called(std::slice::from_ref(value.as_ref()));
        };
        let GoExpression::Identifier(name) = function.unattributed() else { return None };
        self.functions.get(name).cloned()
    }

    /// Names for the value and failure of an `Either` of the type.
    fn fresh(&self, shape: &str, names: &mut FxHashSet<String>) -> (String, String) {
        let value = crate::emit::inlining::fresh(&self.shapes[shape].value_name, names);
        let failure = crate::emit::inlining::fresh(&format!("err{NUMBERED}"), names);
        (value, failure)
    }

    fn joined(&mut self, shape: &str, value: &str, failure: &str) -> GoExpression {
        let from_results = converter(self.converters, shape, Conversion::FromResults);
        call(
            identifier_expression(&from_results),
            vec![identifier_expression(value), identifier_expression(failure)],
        )
    }
}

/// Drops the functions returning a nested `Either` that the code uses other than by calling them
/// and keeping both results, or returning them from another such function.
struct NestedUses<'n> {
    functions: &'n mut FxHashMap<String, (String, String)>,
    /// The top-level function whose own body the code is in, outside function literals.
    owner: Option<String>,
    changed: bool,
}

impl NestedUses<'_> {
    fn arguments(&mut self, value: &mut GoExpression) {
        match value {
            GoExpression::Attributed { value, .. } => self.arguments(value),
            GoExpression::Call { arguments, .. } => {
                arguments.iter_mut().for_each(|argument| self.expression(argument))
            }
            value => self.expression(value),
        }
    }

    fn called(&self, value: &GoExpression) -> Option<String> {
        let GoExpression::Call { function, .. } = value.unattributed() else { return None };
        let GoExpression::Identifier(name) = function.unattributed() else { return None };
        self.functions.contains_key(name).then(|| name.clone())
    }
}

impl Walk for NestedUses<'_> {
    fn statement(&mut self, statement: &mut GoStatement) {
        match statement {
            GoStatement::Define { names, values }
                if self.owner.is_some()
                    && names.len() == 2
                    && values.len() == 1
                    && self.called(&values[0]).is_some() =>
            {
                self.arguments(&mut values[0]);
            }
            GoStatement::Assign { targets, values }
                if self.owner.is_some()
                    && targets.len() == 2
                    && values.len() == 1
                    && matches!(targets[0].unattributed(), GoExpression::Identifier(_))
                    && self.called(&values[0]).is_some() =>
            {
                self.arguments(&mut values[0]);
            }
            GoStatement::Expression(value) if self.called(value).is_some() => {
                self.arguments(value);
            }
            GoStatement::Return(Some(value)) if let Some(called) = self.called(value) => {
                let outer = &self.functions[&called].0;
                let returned_as_is = self
                    .owner
                    .as_ref()
                    .and_then(|owner| self.functions.get(owner))
                    .is_some_and(|(owner_outer, _)| owner_outer == outer);
                if !returned_as_is {
                    self.functions.remove(&called);
                    self.changed = true;
                }
                self.arguments(value);
            }
            statement => go_traversal::statement(self, statement),
        }
    }

    fn expression(&mut self, value: &mut GoExpression) {
        match value {
            GoExpression::Function { .. } => {
                let owner = self.owner.take();
                go_traversal::expression(self, value);
                self.owner = owner;
            }
            GoExpression::Identifier(name) => {
                if self.functions.remove(name.as_str()).is_some() {
                    self.changed = true;
                }
            }
            value => go_traversal::expression(self, value),
        }
    }
}
