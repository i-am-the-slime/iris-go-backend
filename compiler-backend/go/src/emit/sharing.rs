use rustc_hash::{FxHashMap, FxHashSet};

use super::locals::NUMBERED;
use crate::go_traversal::{self, Walk, each_expression_in_statement};
use crate::naming::{VALUE, lower_camel};
use crate::syntax::{GoDeclaration, GoExpression, GoStatement, GoType};

pub(super) fn share_repeated_constructions(
    declarations: &mut [GoDeclaration],
    record_value_name: &mut dyn FnMut(&str) -> Option<String>,
) {
    for declaration in declarations {
        let GoDeclaration::Function { parameters, body, .. } = declaration else { continue };
        let parameters: Vec<String> = parameters.iter().map(|(name, _)| name.clone()).collect();
        let mut shared: Vec<GoExpression> = vec![];
        while let Some(construction) = repeated_construction(&parameters, body, &shared) {
            let base = construction_name(&construction, record_value_name);
            shared.push(construction.clone());
            let name = format!("{base}{NUMBERED}0{}", shared.len());
            share(body, &parameters, &construction, &name);
        }
    }
}

fn repeated_construction(
    parameters: &[String],
    body: &mut [GoStatement],
    tried: &[GoExpression],
) -> Option<GoExpression> {
    let mut counts: Vec<(GoExpression, usize)> = vec![];
    let mut addressed: Vec<GoExpression> = vec![];
    for statement in body.iter_mut() {
        each_expression_in_statement(statement, |expression| {
            if let GoExpression::Address(value) = expression {
                addressed.push(value.unattributed().clone());
            }
            let value = expression.unattributed();
            if !is_pure_construction(value) {
                return;
            }
            match counts.iter_mut().find(|(seen, _)| seen == value) {
                Some((_, count)) => *count += 1,
                None => counts.push((value.clone(), 1)),
            }
        });
    }
    let bindings = Bindings::of(parameters, body);
    counts
        .into_iter()
        .filter(|(construction, count)| *count > 1 && !addressed.contains(construction))
        .map(|(construction, _)| construction)
        .filter(|construction| !tried.contains(construction))
        .find(|construction| {
            identifiers(construction).iter().all(|name| bindings.never_changes(name))
        })
}

fn is_pure_construction(expression: &GoExpression) -> bool {
    let GoExpression::Composite { type_, fields } = expression else { return false };
    let is_struct =
        matches!(type_, GoType::Named(_) | GoType::Generic { .. } | GoType::Struct(_));
    let reads_locals = fields
        .iter()
        .any(|(_, value)| matches!(value.unattributed(), GoExpression::Identifier(_)));
    let only_names = fields.iter().all(|(label, value)| {
        label.is_some()
            && matches!(
                value.unattributed(),
                GoExpression::Identifier(_) | GoExpression::Qualified { .. }
            )
    });
    is_struct && !fields.is_empty() && reads_locals && only_names
}

fn identifiers(construction: &GoExpression) -> Vec<String> {
    let GoExpression::Composite { fields, .. } = construction else { return vec![] };
    fields
        .iter()
        .filter_map(|(_, value)| match value.unattributed() {
            GoExpression::Identifier(name) => Some(name.clone()),
            _ => None,
        })
        .collect()
}

fn construction_name(
    construction: &GoExpression,
    record_value_name: &mut dyn FnMut(&str) -> Option<String>,
) -> String {
    let GoExpression::Composite { type_, .. } = construction else { return VALUE.into() };
    let spelled = match type_ {
        GoType::Named(name) | GoType::Generic { name, .. } => name.as_str(),
        _ => VALUE,
    };
    if let Some(name) = record_value_name(spelled) {
        return name;
    }
    let last = spelled.rsplit(['.', '/']).next().unwrap_or(spelled);
    let name = lower_camel(last);
    if name.is_empty() { VALUE.to_string() } else { name }
}

fn share(
    body: &mut Vec<GoStatement>,
    parameters: &[String],
    construction: &GoExpression,
    name: &str,
) -> bool {
    let bindings = Bindings::of(parameters, body);
    let wanted: FxHashSet<String> = identifiers(construction)
        .into_iter()
        .filter(|name| bindings.binders.contains_key(name))
        .collect();
    let bound_by_parameters: FxHashSet<String> =
        wanted.iter().filter(|name| parameters.contains(name)).cloned().collect();
    let total = occurrences(body, construction);
    let mut placement = Placement {
        construction,
        name,
        wanted: &wanted,
        bound_outside: bound_by_parameters,
        total,
        placed: false,
    };
    placement.block(body);
    placement.placed
}

struct Placement<'p> {
    construction: &'p GoExpression,
    name: &'p str,
    wanted: &'p FxHashSet<String>,
    bound_outside: FxHashSet<String>,
    total: usize,
    placed: bool,
}

impl Walk for Placement<'_> {
    fn block(&mut self, body: &mut Vec<GoStatement>) {
        if self.placed {
            return;
        }
        if let Some(at) = self.insertion_point(body) {
            for statement in &mut body[at..] {
                replace(statement, self.construction, self.name);
            }
            let define = GoStatement::Define {
                names: vec![self.name.to_string()],
                values: vec![self.construction.clone()],
            };
            body.insert(at, define);
            self.placed = true;
            return;
        }
        let bound_here: Vec<String> = body
            .iter()
            .flat_map(defined_names)
            .filter(|name| self.wanted.contains(name))
            .collect();
        let before = self.bound_outside.clone();
        self.bound_outside.extend(bound_here);
        body.iter_mut().for_each(|statement| self.statement(statement));
        self.bound_outside = before;
    }

    fn expression(&mut self, value: &mut GoExpression) {
        if !self.placed {
            go_traversal::expression(self, value);
        }
    }
}

impl Placement<'_> {
    fn insertion_point(&self, body: &mut [GoStatement]) -> Option<usize> {
        let mut bound = self.bound_outside.clone();
        let mut after = 0;
        for (index, statement) in body.iter().enumerate() {
            let defined = defined_names(statement);
            if defined.iter().any(|name| self.wanted.contains(name)) {
                bound.extend(defined);
                after = index + 1;
            }
        }
        if !self.wanted.iter().all(|name| bound.contains(name)) {
            return None;
        }
        let counts: Vec<usize> = body
            .iter_mut()
            .map(|statement| occurrences_in(statement, self.construction))
            .collect();
        let first = counts.iter().position(|&count| count > 0)?;
        let found: usize = counts[first..].iter().sum();
        (first >= after && found == self.total).then_some(first)
    }
}

fn defined_names(statement: &GoStatement) -> Vec<String> {
    match statement {
        GoStatement::Define { names, .. } => names.clone(),
        GoStatement::Variable { name, .. } => vec![name.clone()],
        _ => vec![],
    }
}

fn occurrences(body: &mut [GoStatement], construction: &GoExpression) -> usize {
    body.iter_mut().map(|statement| occurrences_in(statement, construction)).sum()
}

fn occurrences_in(statement: &mut GoStatement, construction: &GoExpression) -> usize {
    let mut count = 0;
    each_expression_in_statement(statement, |expression| {
        if expression.unattributed() == construction {
            count += 1;
        }
    });
    count
}

fn replace(statement: &mut GoStatement, construction: &GoExpression, name: &str) {
    each_expression_in_statement(statement, |expression| {
        if expression.unattributed() == construction {
            *expression = GoExpression::Identifier(name.to_string());
        }
    });
}

#[derive(Default)]
struct Bindings {
    binders: FxHashMap<String, usize>,
    assigned: FxHashSet<String>,
}

impl Bindings {
    fn of(parameters: &[String], body: &mut [GoStatement]) -> Bindings {
        let mut bindings = Bindings::default();
        for parameter in parameters {
            bindings.bind(parameter);
        }
        for statement in body.iter_mut() {
            bindings.statement(statement);
        }
        bindings
    }

    fn bind(&mut self, name: &str) {
        *self.binders.entry(name.to_string()).or_default() += 1;
    }

    fn never_changes(&self, name: &str) -> bool {
        self.binders.get(name).is_none_or(|&count| count == 1) && !self.assigned.contains(name)
    }
}

impl Walk for Bindings {
    fn statement(&mut self, statement: &mut GoStatement) {
        match statement {
            GoStatement::Define { names, .. } => names.iter().for_each(|name| self.bind(name)),
            GoStatement::Variable { name, .. }
            | GoStatement::IfAssert { name, .. }
            | GoStatement::Counting { variable: name, .. }
            | GoStatement::CountingDown { variable: name, .. } => self.bind(name),
            GoStatement::Range { index, element, .. } => {
                index.iter().for_each(|name| self.bind(name));
                self.bind(element);
            }
            GoStatement::Assign { targets, .. } => {
                for target in targets.iter() {
                    if let Some(root) = root(target) {
                        self.assigned.insert(root);
                    }
                }
            }
            _ => {}
        }
        go_traversal::statement(self, statement);
    }

    fn expression(&mut self, value: &mut GoExpression) {
        match value {
            GoExpression::Function { parameters, .. } => {
                parameters.iter().for_each(|(name, _)| self.bind(name));
            }
            GoExpression::Address(inner) => {
                if let Some(root) = root(inner) {
                    self.assigned.insert(root);
                }
            }
            _ => {}
        }
        go_traversal::expression(self, value);
    }
}

fn root(expression: &GoExpression) -> Option<String> {
    match expression.unattributed() {
        GoExpression::Identifier(name) => Some(name.clone()),
        GoExpression::Field { value, .. } | GoExpression::Index { value, .. } => root(value),
        _ => None,
    }
}
