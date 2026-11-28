use rustc_hash::{FxHashMap, FxHashSet};

use crate::foreign::{ForeignPackages, Forward};
use crate::go_traversal::{self, Walk};
use crate::syntax::{GoDeclaration, GoExpression, GoStatement};

pub(super) struct Forwarders {
    forwards: FxHashMap<(String, String), Forward>,
}

impl Forwarders {
    pub(super) fn new(foreign_packages: &ForeignPackages) -> Forwarders {
        let forwards = foreign_packages
            .sources
            .iter()
            .flat_map(|source| {
                let package = ForeignPackages::package_name(&source.module);
                source.forwarders.iter().map(move |(function, forward)| {
                    ((package.clone(), function.clone()), forward.clone())
                })
            })
            .collect();
        Forwarders { forwards }
    }

    pub(super) fn call_forwarded(&self, declarations: &mut [GoDeclaration]) {
        if self.forwards.is_empty() {
            return;
        }
        for declaration in declarations {
            let mut names = Names::default();
            if let GoDeclaration::Function { parameters, .. } = declaration {
                names.taken.extend(parameters.iter().map(|(name, _)| name.clone()));
            }
            go_traversal::declaration(&mut names, declaration);
            let mut calls = ForwardedCalls { forwarders: self, taken: names.taken };
            go_traversal::declaration(&mut calls, declaration);
        }
    }

    fn forward(&self, function: &GoExpression) -> Option<&Forward> {
        let function = match function.unattributed() {
            GoExpression::Instantiation { function, .. } => function.unattributed(),
            function => function,
        };
        let GoExpression::Qualified { package, name } = function else { return None };
        self.forwards.get(&(package.name().to_string(), name.clone()))
    }
}

#[derive(Default)]
struct Names {
    taken: FxHashSet<String>,
}

impl Walk for Names {
    fn expression(&mut self, value: &mut GoExpression) {
        match value {
            GoExpression::Identifier(name) => {
                self.taken.insert(name.clone());
            }
            GoExpression::Function { parameters, .. } => {
                self.taken.extend(parameters.iter().map(|(name, _)| name.clone()));
            }
            _ => {}
        }
        go_traversal::expression(self, value);
    }

    fn statement(&mut self, statement: &mut GoStatement) {
        match statement {
            GoStatement::Define { names, .. } => self.taken.extend(names.iter().cloned()),
            GoStatement::Variable { name, .. }
            | GoStatement::IfAssert { name, .. }
            | GoStatement::Counting { variable: name, .. }
            | GoStatement::CountingDown { variable: name, .. } => {
                self.taken.insert(name.clone());
            }
            GoStatement::Range { index, element, .. } => {
                self.taken.extend(index.iter().cloned());
                self.taken.insert(element.clone());
            }
            _ => {}
        }
        go_traversal::statement(self, statement);
    }
}

struct ForwardedCalls<'f> {
    forwarders: &'f Forwarders,
    taken: FxHashSet<String>,
}

impl ForwardedCalls<'_> {
    fn fresh(&mut self, base: &str) -> String {
        let mut name = base.to_string();
        let mut suffix = 1;
        while self.taken.contains(&name) {
            suffix += 1;
            name = format!("{base}{suffix}");
        }
        self.taken.insert(name.clone());
        name
    }

    fn copied_receivers(&mut self, statement: &mut GoStatement) -> Vec<GoStatement> {
        let values: Vec<&mut GoExpression> = match statement {
            GoStatement::Define { values, .. } | GoStatement::Assign { values, .. } => {
                values.iter_mut().collect()
            }
            GoStatement::Expression(value)
            | GoStatement::Return(Some(value))
            | GoStatement::If { condition: value, .. }
            | GoStatement::Switch { value: Some(value), .. } => vec![value],
            _ => return vec![],
        };
        let whole = values.len() == 1;
        let mut receivers = Receivers { calls: self, copies: vec![] };
        for value in values {
            if !receivers.copy_receiver(value, whole) {
                receivers.expression(value);
            }
        }
        receivers.copies
    }
}

struct Receivers<'c, 'f> {
    calls: &'c mut ForwardedCalls<'f>,
    copies: Vec<GoStatement>,
}

impl Receivers<'_, '_> {
    fn copy_receiver(&mut self, value: &mut GoExpression, whole: bool) -> bool {
        let GoExpression::Call { function, arguments } = value else { return false };
        let Some(Forward::MethodOfCopy(method)) = self.calls.forwarders.forward(function) else {
            return false;
        };
        let Some(receiver) = arguments.first() else { return false };
        if !(whole || is_load(receiver)) {
            return false;
        }
        let method = method.clone();
        let receiver = arguments.remove(0);
        let copy = self.calls.fresh("receiver");
        self.copies.push(GoStatement::Define { names: vec![copy.clone()], values: vec![receiver] });
        let copied = GoExpression::Identifier(copy);
        **function = GoExpression::Field { value: Box::new(copied), name: method };
        arguments.iter_mut().for_each(|argument| self.expression(argument));
        true
    }
}

impl Walk for Receivers<'_, '_> {
    fn expression(&mut self, value: &mut GoExpression) {
        if matches!(value, GoExpression::Function { .. }) || self.copy_receiver(value, false) {
            return;
        }
        go_traversal::expression(self, value);
    }
}

fn is_load(value: &GoExpression) -> bool {
    match value.unattributed() {
        GoExpression::Identifier(_) | GoExpression::Qualified { .. } => true,
        GoExpression::Field { value, .. } => is_load(value),
        _ => false,
    }
}

impl Walk for ForwardedCalls<'_> {
    fn expression(&mut self, value: &mut GoExpression) {
        go_traversal::expression(self, value);
        if let GoExpression::Qualified { package, name } = value
            && let Some(Forward::Function(function)) =
                self.forwarders.forwards.get(&(package.name().to_string(), name.clone()))
        {
            *name = function.clone();
            return;
        }
        let GoExpression::Call { function, arguments } = value else { return };
        let Some(Forward::Method(method)) = self.forwarders.forward(function) else { return };
        if arguments.is_empty() {
            return;
        }
        let receiver = arguments.remove(0);
        **function = GoExpression::Field { value: Box::new(receiver), name: method.clone() };
    }

    fn block(&mut self, body: &mut Vec<GoStatement>) {
        let mut rewritten = Vec::with_capacity(body.len());
        for mut statement in body.drain(..) {
            self.statement(&mut statement);
            rewritten.extend(self.copied_receivers(&mut statement));
            rewritten.push(statement);
        }
        *body = rewritten;
    }
}
