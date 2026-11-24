//! Functions that only hand their parameters on, or read a field of one, as a `where` helper
//! `derivativeOf e = derivative variable e` or a record's field getter lifts to, give way to
//! what they do:
//!
//! - a forwarding function, `func f(a A, b B) R { return g(a, b) }`, whose parameters and result
//!   are `g`'s, is another name for `g`;
//! - a call of a field reader, `func f(r R) T { return r.Field }`, is the read, `x.Field`, which
//!   evaluates `x` once as the call did, and a call of an identity, `return r`, is `x`.
//!
//! A function that then has no reference left goes. A declaration whose locals take a wrapper's
//! name keeps reading the local.

use rustc_hash::{FxHashMap, FxHashSet};

use super::operators::is_untyped_constant;
use crate::go_traversal::{self, Walk};
use crate::syntax::{GoDeclaration, GoExpression, GoStatement, GoType};

pub(super) fn inline_wrappers(declarations: &mut Vec<GoDeclaration>) {
    let wrappers = Wrappers::of(declarations);
    if wrappers.forwarded.is_empty() && wrappers.readers.is_empty() {
        return;
    }
    for declaration in declarations.iter_mut() {
        let locals = declaration.declared_names().locals;
        go_traversal::declaration(&mut Rewrite { wrappers: &wrappers, locals }, declaration);
    }
    let mut referenced = FxHashSet::default();
    for declaration in declarations.iter_mut() {
        let names = declaration.declared_names();
        referenced.extend(names.names.into_iter().filter(|name| !names.locals.contains(name)));
    }
    declarations.retain(|declaration| match declaration {
        GoDeclaration::Function { name, .. } if wrappers.replaced(name) => {
            referenced.contains(name)
        }
        _ => true,
    });
}

#[derive(Default)]
struct Wrappers {
    /// Each forwarding function and the function it forwards to, chains followed.
    forwarded: FxHashMap<String, String>,
    /// Each field reader and the fields it reads, outermost last.
    readers: FxHashMap<String, Vec<String>>,
}

impl Wrappers {
    fn of(declarations: &[GoDeclaration]) -> Wrappers {
        let signatures: FxHashMap<&str, (Vec<&GoType>, Option<&GoType>)> = declarations
            .iter()
            .filter_map(|declaration| match declaration {
                GoDeclaration::Function { name, parameters, result, .. } => {
                    let types = parameters.iter().map(|(_, type_)| type_).collect();
                    Some((name.as_str(), (types, result.as_ref())))
                }
                _ => None,
            })
            .collect();
        let written: Vec<&str> = declarations
            .iter()
            .filter_map(|declaration| match declaration {
                GoDeclaration::Written { source, .. } => Some(source.as_str()),
                _ => None,
            })
            .collect();
        let mut wrappers = Wrappers::default();
        for declaration in declarations {
            let GoDeclaration::Function { name, parameters, body, .. } = declaration else {
                continue;
            };
            if name == "main" || written.iter().any(|source| source.contains(name.as_str())) {
                continue;
            }
            let Some(returned) = only_return(body) else { continue };
            if let Some(target) = forwarded_to(returned, parameters)
                && target != *name
                && signatures.get(target.as_str()) == signatures.get(name.as_str())
            {
                wrappers.forwarded.insert(name.clone(), target);
            } else if let Some(fields) = field_read(returned, parameters) {
                wrappers.readers.insert(name.clone(), fields);
            }
        }
        wrappers.follow_chains();
        wrappers
    }

    /// `f` forwarding to `g` forwarding to `h` forwards to `h`; a cycle forwards nowhere.
    fn follow_chains(&mut self) {
        let names: Vec<String> = self.forwarded.keys().cloned().collect();
        for name in names {
            let mut target = self.forwarded[&name].clone();
            let mut seen = FxHashSet::default();
            while let Some(next) = self.forwarded.get(&target) {
                if !seen.insert(target.clone()) || *next == name {
                    break;
                }
                target = next.clone();
            }
            if self.forwarded.contains_key(&target) {
                self.forwarded.remove(&name);
            } else {
                self.forwarded.insert(name, target);
            }
        }
    }

    fn replaced(&self, name: &str) -> bool {
        self.forwarded.contains_key(name) || self.readers.contains_key(name)
    }
}

/// The value a body returns, when returning it is all the body does.
fn only_return(body: &[GoStatement]) -> Option<&GoExpression> {
    let mut statements = body.iter().filter(|statement| !matches!(statement, GoStatement::Line(_)));
    let (Some(GoStatement::Return(Some(value))), None) = (statements.next(), statements.next())
    else {
        return None;
    };
    Some(value)
}

/// `g` of `return g(a, b)` where `a, b` are the parameters in order.
fn forwarded_to(returned: &GoExpression, parameters: &[(String, GoType)]) -> Option<String> {
    let GoExpression::Call { function, arguments } = returned else { return None };
    let GoExpression::Identifier(target) = &**function else { return None };
    let passed = arguments.len() == parameters.len()
        && arguments.iter().zip(parameters).all(|(argument, (parameter, _))| {
            matches!(argument, GoExpression::Identifier(name) if name == parameter)
        });
    passed.then(|| target.clone())
}

/// The fields of `return r.A.B` where `r` is the one parameter.
fn field_read(returned: &GoExpression, parameters: &[(String, GoType)]) -> Option<Vec<String>> {
    let [(parameter, parameter_type)] = parameters else { return None };
    let mut fields = vec![];
    let mut value = returned;
    while let GoExpression::Field { value: inner, name } = value {
        fields.push(name.clone());
        value = inner;
    }
    fields.reverse();
    let read = matches!(value, GoExpression::Identifier(name) if name == parameter);
    let boxes = fields.is_empty() && matches!(parameter_type, GoType::Any | GoType::Erased(_));
    (read && !boxes).then_some(fields)
}

struct Rewrite<'w> {
    wrappers: &'w Wrappers,
    locals: FxHashSet<String>,
}

impl Walk for Rewrite<'_> {
    fn expression(&mut self, value: &mut GoExpression) {
        go_traversal::expression(self, value);
        match value {
            GoExpression::Identifier(name) if !self.locals.contains(name) => {
                if let Some(target) = self.wrappers.forwarded.get(name) {
                    *name = target.clone();
                }
            }
            GoExpression::Call { function, arguments } if arguments.len() == 1 => {
                let GoExpression::Identifier(name) = &**function else { return };
                if self.locals.contains(name) {
                    return;
                }
                let Some(fields) = self.wrappers.readers.get(name) else { return };
                // An untyped constant would lose the type the identity's parameter gave it.
                if fields.is_empty() && is_untyped_constant(&arguments[0]) {
                    return;
                }
                let mut read = arguments.pop().expect("one argument");
                for field in fields {
                    read = GoExpression::Field { value: Box::new(read), name: field.clone() };
                }
                *value = read;
            }
            _ => {}
        }
    }
}
