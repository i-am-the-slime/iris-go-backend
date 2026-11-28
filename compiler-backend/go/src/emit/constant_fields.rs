//! A field that a function always builds with the same constant reads as that constant:
//!
//! ```go
//! func addProduct(deps Deps) RouteRunner {
//!     return RouteRunner{Method: "POST", BodyKind: BodyKindJSONRequestBody, Serving: …}
//! }
//! runner := addProduct(deps)
//! switch runner.BodyKind { case BodyKindNoRequestBody: … case BodyKindJSONRequestBody: … }
//! ```
//!
//! reads `runner.BodyKind` as `BodyKindJSONRequestBody`, and a switch on a constant that one of
//! its cases names is that case's body.

use crate::emit::index_arrays::is_line;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::go_traversal::{self, Walk};
use crate::syntax::{GoDeclaration, GoExpression, GoStatement};

pub(super) fn read_constant_fields(declarations: &mut [GoDeclaration]) {
    let (built, _) = constant_fields(declarations);
    for declaration in declarations.iter_mut() {
        if !built.is_empty() {
            let mut results = Results {
                built: &built,
                results: FxHashMap::default(),
                bound: FxHashMap::default(),
            };
            go_traversal::declaration(&mut results, declaration);
            results.results.retain(|name, _| results.bound.get(name) == Some(&1));
            if !results.results.is_empty() {
                go_traversal::declaration(
                    &mut Reads { results: &results.results, built: &built },
                    declaration,
                );
            }
        }
        go_traversal::declaration(&mut KnownSwitches, declaration);
    }
}

/// The constant fields of the composite each function returns, when returning it is all the
/// function does.
/// Also the composites of the functions that build nothing but constants, which a call of such a
/// function on reads is.
fn constant_fields(declarations: &[GoDeclaration]) -> (Built, FxHashMap<String, GoExpression>) {
    let mut built = FxHashMap::default();
    let mut constants = FxHashMap::default();
    for declaration in declarations {
        let GoDeclaration::Function { name, parameters, body, .. } = declaration else { continue };
        let mut statements = body.iter().filter(|statement| !is_line(statement));
        let first_two = (statements.next(), statements.next());
        let (Some(GoStatement::Return(Some(composite))), None) = first_two else { continue };
        let GoExpression::Composite { fields, .. } = composite else { continue };
        let parameters = parameters.iter().map(|(name, _)| name.as_str());
        let parameters: FxHashSet<&str> = parameters.collect();
        let constant_fields = fields.iter().filter_map(|(field, value)| {
            let field = field.as_ref()?;
            is_constant(value, &parameters).then(|| (field.clone(), value.clone()))
        });
        let constant_fields: FxHashMap<String, GoExpression> = constant_fields.collect();
        if fields.iter().all(|(_, value)| is_constant(value, &parameters)) {
            constants.insert(name.clone(), composite.clone());
        }
        if !constant_fields.is_empty() {
            built.insert(name.clone(), constant_fields);
        }
    }
    (built, constants)
}

type Built = FxHashMap<String, FxHashMap<String, GoExpression>>;

/// Drops the calls whose result is dropped of functions that build only constants, on arguments
/// that are reads: what is left of a call once its fields read as constants.
pub(super) fn drop_calls_of_constant_functions(declarations: &mut [GoDeclaration]) {
    let (_, constants) = constant_fields(declarations);
    if constants.is_empty() {
        return;
    }
    for declaration in declarations.iter_mut() {
        go_traversal::declaration(&mut ConstantCalls { constants: &constants }, declaration);
    }
}

struct ConstantCalls<'c> {
    constants: &'c FxHashMap<String, GoExpression>,
}

impl Walk for ConstantCalls<'_> {
    fn block(&mut self, body: &mut Vec<GoStatement>) {
        body.retain(|statement| {
            let GoStatement::Expression(GoExpression::Call { function, arguments }) = statement
            else {
                return true;
            };
            let constant = matches!(function.as_ref(), GoExpression::Identifier(callee)
                if self.constants.contains_key(callee));
            !(constant && arguments.iter().all(super::wrappers::is_read))
        });
        body.iter_mut().for_each(|statement| self.statement(statement));
    }
}

fn is_constant(value: &GoExpression, parameters: &FxHashSet<&str>) -> bool {
    match value {
        GoExpression::Qualified { .. }
        | GoExpression::Integer(_)
        | GoExpression::String(_)
        | GoExpression::Boolean(_)
        | GoExpression::Rune(_) => true,
        // A name that is no parameter is a package-level value, which never changes.
        GoExpression::Identifier(name) => {
            !parameters.contains(name.as_str()) && name.starts_with(char::is_uppercase)
        }
        GoExpression::Composite { fields, .. } => {
            fields.iter().all(|(_, value)| is_constant(value, parameters))
        }
        _ => false,
    }
}

/// The locals defined once by a call of a function with constant fields, and nowhere written.
struct Results<'b> {
    built: &'b FxHashMap<String, FxHashMap<String, GoExpression>>,
    results: FxHashMap<String, String>,
    bound: FxHashMap<String, usize>,
}

impl Walk for Results<'_> {
    fn statement(&mut self, statement: &mut GoStatement) {
        match statement {
            GoStatement::Define { names, values } => {
                if let [name] = names.as_slice()
                    && let [GoExpression::Call { function, .. }] = values.as_slice()
                    && let GoExpression::Identifier(callee) = function.as_ref()
                    && self.built.contains_key(callee)
                {
                    self.results.insert(name.clone(), callee.clone());
                }
                for name in names.iter() {
                    *self.bound.entry(name.clone()).or_default() += 1;
                }
            }
            GoStatement::Variable { name, .. } | GoStatement::IfAssert { name, .. } => {
                *self.bound.entry(name.clone()).or_default() += 2;
            }
            GoStatement::Assign { targets, .. } => {
                for target in targets.iter() {
                    if let Some(root) = super::aliases::target_root(target) {
                        *self.bound.entry(root.to_string()).or_default() += 2;
                    }
                }
            }
            GoStatement::Range { index, element, .. } => {
                for name in index.iter().chain([&*element]) {
                    *self.bound.entry(name.clone()).or_default() += 2;
                }
            }
            _ => {}
        }
        go_traversal::statement(self, statement);
    }

    fn expression(&mut self, value: &mut GoExpression) {
        match value {
            GoExpression::Address(inner) => {
                if let Some(root) = super::aliases::target_root(inner) {
                    *self.bound.entry(root.to_string()).or_default() += 2;
                }
            }
            GoExpression::Function { parameters, .. } => {
                for (name, _) in parameters.iter() {
                    *self.bound.entry(name.clone()).or_default() += 2;
                }
            }
            _ => {}
        }
        go_traversal::expression(self, value);
    }
}

struct Reads<'r> {
    results: &'r FxHashMap<String, String>,
    built: &'r FxHashMap<String, FxHashMap<String, GoExpression>>,
}

impl Walk for Reads<'_> {
    fn expression(&mut self, value: &mut GoExpression) {
        if let GoExpression::Field { value: record, name: field } = value
            && let GoExpression::Identifier(local) = record.as_ref()
            && let Some(callee) = self.results.get(local)
            && let Some(constant) = self.built[callee].get(field)
        {
            *value = constant.clone();
            return;
        }
        go_traversal::expression(self, value);
    }
}

/// A switch on a constant that a case names is that case's body, when what the body defines
/// is named nowhere else in the enclosing block.
struct KnownSwitches;

impl Walk for KnownSwitches {
    fn block(&mut self, body: &mut Vec<GoStatement>) {
        let mut position = 0;
        while position < body.len() {
            match chosen_case(body, position) {
                Some(chosen) => {
                    body.splice(position..=position, chosen);
                }
                None => {
                    self.statement(&mut body[position]);
                    position += 1;
                }
            }
        }
    }
}

fn chosen_case(block: &mut [GoStatement], position: usize) -> Option<Vec<GoStatement>> {
    let GoStatement::Switch { value: Some(value), cases, default } = &block[position] else {
        return None;
    };
    let constant = match value {
        GoExpression::Qualified { .. } => true,
        GoExpression::Identifier(name) => name.starts_with(char::is_uppercase),
        _ => false,
    };
    if !constant {
        return None;
    }
    let body = match cases.iter().find(|case| case.values.contains(value)) {
        Some(case) => &case.body,
        None => &default.as_ref().filter(|default| default.covers.contains(value))?.body,
    };
    if body.iter().any(|statement| matches!(statement, GoStatement::Break)) {
        return None;
    }
    let body = body.clone();
    let defined = body
        .iter()
        .flat_map(|statement| match statement {
            GoStatement::Define { names, .. } => names.clone(),
            GoStatement::Variable { name, .. } => vec![name.clone()],
            _ => vec![],
        })
        .filter(|name| name != "_");
    let defined: Vec<String> = defined.collect();
    let clash = block.iter_mut().enumerate().any(|(at, statement)| {
        at != position && defined.iter().any(|name| super::aliases::mentions(statement, name))
    });
    (!clash).then_some(body)
}
