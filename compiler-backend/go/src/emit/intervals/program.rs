use rustc_hash::{FxHashMap, FxHashSet};

use super::analysis::Analysis;
use super::constraints::kind_of_type;
use super::each_field_write;
use super::names::shape_of_type;
use super::syntax::is_bounds_test;
use crate::emit::headers::Keeping;
use crate::go_traversal::{self, Walk};
use crate::syntax::{GoDeclaration, GoExpression, GoStatement, GoType};

/// Declarations rewritten while the entries were found, with the entry each was rewritten
/// under: the rewrite stands if that entry is the final one.
type Rewritten = FxHashMap<usize, (Option<Entry>, GoDeclaration)>;

/// Whether a declaration is worth interpreting: it has a test or a division to prove, or it
/// calls an internal function whose parameters facts can bound. One that is not still calls
/// its internal callees with nothing known.
pub(super) struct Plan {
    pub(super) interpret: bool,
    /// Whether it has a test or a division to rewrite, rather than only calls to give facts.
    pub(super) rewrites: bool,
    callees: Vec<String>,
}

/// The functions of the program, and those whose every call it can see.
pub(super) struct FunctionTable {
    pub(super) signatures: FxHashMap<String, FunctionSignature>,
    pub(super) internal: FxHashSet<String>,
    pub(super) fields: FxHashSet<String>,
}

pub(super) struct FunctionSignature {
    pub(super) parameters: Vec<GoType>,
    pub(super) result: Option<GoType>,
}

/// What every call of a function gives its parameters, as constraints between places.
#[derive(Clone, PartialEq, Debug, Default)]
pub(super) struct Entry(pub(super) FxHashMap<(Place, Place), i64>);

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(super) enum Place {
    Zero,
    Parameter(usize),
    /// The length of an array parameter: `len(xs)`, or `len(*xs)` for a pointer.
    Length(usize),
}

/// How often a function's entry may grow before its changing constraints are dropped.
const WIDEN_ENTRY_AFTER: usize = 3;

impl FunctionTable {
    pub(super) fn of(
        declarations: &mut [GoDeclaration],
        fields: FxHashSet<String>,
    ) -> FunctionTable {
        let mut signatures = FxHashMap::default();
        let mut mentioned_in_text = FxHashSet::default();
        let names: Vec<String> = declarations
            .iter()
            .filter_map(|declaration| match declaration {
                GoDeclaration::Function { name, .. } => Some(name.clone()),
                _ => None,
            })
            .collect();
        for declaration in declarations.iter() {
            match declaration {
                GoDeclaration::Function { name, parameters, result, .. } => {
                    let parameters = parameters.iter().map(|(_, type_)| type_.clone()).collect();
                    signatures.insert(
                        name.clone(),
                        FunctionSignature { parameters, result: result.clone() },
                    );
                }
                GoDeclaration::Source { template: text, .. } => {
                    names.iter().filter(|name| text.contains(name.as_str())).for_each(|name| {
                        mentioned_in_text.insert(name.clone());
                    });
                }
                GoDeclaration::Written { source: text, .. } => {
                    names.iter().filter(|name| text.contains(name.as_str())).for_each(|name| {
                        mentioned_in_text.insert(name.clone());
                    });
                }
                _ => {}
            }
        }
        let values = used_as_values(declarations);
        let mut counts: FxHashMap<&str, usize> = FxHashMap::default();
        names.iter().for_each(|name| *counts.entry(name).or_default() += 1);
        let internal = names
            .iter()
            .filter(|name| {
                let unexported = name.chars().next().is_some_and(|first| !first.is_uppercase());
                (unexported || !fields.is_empty())
                    && !matches!(name.as_str(), "main" | "init")
                    && counts[name.as_str()] == 1
                    && !values.contains(name.as_str())
                    && !mentioned_in_text.contains(name.as_str())
            })
            .cloned()
            .collect();
        FunctionTable { signatures, internal, fields }
    }

    pub(super) fn plan(&self, declaration: &mut GoDeclaration) -> Plan {
        struct Scan<'p> {
            program: &'p FunctionTable,
            rewrites: bool,
            calls_bounded: bool,
            callees: Vec<String>,
        }
        impl Walk for Scan<'_> {
            fn statement(&mut self, statement: &mut GoStatement) {
                match statement {
                    GoStatement::If { condition, .. } => self.rewrites |= is_bounds_test(condition),
                    GoStatement::Define { values, .. } => {
                        self.rewrites |= values.iter().any(is_bounds_test)
                    }
                    _ => {}
                }
                go_traversal::statement(self, statement);
            }

            fn expression(&mut self, value: &mut GoExpression) {
                if let GoExpression::Call { function, .. } = value {
                    match &**function {
                        GoExpression::Qualified { package, name } => {
                            self.rewrites |=
                                package == "prim" && matches!(name.as_str(), "IntMod" | "IntDiv")
                        }
                        GoExpression::Identifier(callee)
                            if self.program.internal.contains(callee) =>
                        {
                            let bounded =
                                self.program.signatures[callee].parameters.iter().any(|type_| {
                                    kind_of_type(type_).is_some() || shape_of_type(type_).is_some()
                                });
                            self.calls_bounded |= bounded;
                            self.callees.push(callee.clone());
                        }
                        _ => {}
                    }
                }
                go_traversal::expression(self, value);
            }
        }
        let mut scan =
            Scan { program: self, rewrites: false, calls_bounded: false, callees: vec![] };
        go_traversal::declaration(&mut scan, declaration);
        if !self.fields.is_empty() {
            let mut writes = false;
            each_field_write(declaration, &self.fields, &mut |_, _| writes = true);
            let interpret = scan.calls_bounded || writes;
            return Plan { interpret, rewrites: false, callees: scan.callees };
        }
        let interpret = scan.rewrites || scan.calls_bounded;
        Plan { interpret, rewrites: scan.rewrites, callees: scan.callees }
    }

    /// The facts every call gives each internal function's parameters: a fixpoint over the
    /// calls, starting from the functions anything may call.
    pub(super) fn entries(
        &self,
        declarations: &mut [GoDeclaration],
        plans: &[Plan],
        keeping: &Keeping<'_>,
    ) -> (FxHashMap<String, Entry>, Rewritten) {
        let positions: FxHashMap<String, usize> = declarations
            .iter()
            .enumerate()
            .filter_map(|(position, declaration)| match declaration {
                GoDeclaration::Function { name, .. } => Some((name.clone(), position)),
                _ => None,
            })
            .collect();
        let mut entries: FxHashMap<String, Entry> = FxHashMap::default();
        // A call from code not interpreted gives nothing: the entry knows nothing either.
        for plan in plans {
            if !plan.interpret {
                for callee in &plan.callees {
                    entries.insert(callee.clone(), Entry::default());
                }
            }
        }
        let mut updates: FxHashMap<String, usize> = FxHashMap::default();
        // Callers first, so that most functions are interpreted once, under their final entry.
        let mut pending: std::collections::VecDeque<usize> =
            (0..declarations.len()).filter(|position| plans[*position].interpret).collect();
        pending.make_contiguous().sort_by_key(|position| {
            matches!(&declarations[*position], GoDeclaration::Function { name, .. }
                if self.internal.contains(name.as_str()))
        });
        let mut rewritten = Rewritten::default();
        let mut queued: Vec<bool> = plans.iter().map(|plan| plan.interpret).collect();
        while let Some(position) = pending.pop_front() {
            queued[position] = false;
            let declaration = &mut declarations[position];
            let Some(entry) = self.entry_of(declaration, &entries) else { continue };
            let rewrites = plans[position].rewrites;
            let mut analysis = Analysis::new(self, keeping, rewrites);
            if rewrites {
                let mut copy = declaration.clone();
                analysis.declaration(&mut copy, entry.clone());
                rewritten.insert(position, (entry, copy));
            } else {
                analysis.declaration(declaration, entry);
            }
            for (callee, facts) in analysis.calls {
                let merged = match entries.get(&callee) {
                    None => facts,
                    Some(old) => {
                        let joined = old.join(&facts);
                        if updates.get(&callee).copied().unwrap_or(0) >= WIDEN_ENTRY_AFTER {
                            old.widen(&joined)
                        } else {
                            joined
                        }
                    }
                };
                if entries.get(&callee) == Some(&merged) {
                    continue;
                }
                *updates.entry(callee.clone()).or_default() += 1;
                entries.insert(callee.clone(), merged);
                if let Some(&callee_position) = positions.get(&callee)
                    && plans[callee_position].interpret
                    && !queued[callee_position]
                {
                    queued[callee_position] = true;
                    pending.push_back(callee_position);
                }
            }
        }
        (entries, rewritten)
    }

    /// The facts to analyse a declaration under: none for code anything may run, the calls'
    /// for an internal function, and nothing at all for one no call reaches.
    pub(super) fn entry_of(
        &self,
        declaration: &GoDeclaration,
        entries: &FxHashMap<String, Entry>,
    ) -> Option<Option<Entry>> {
        match declaration {
            GoDeclaration::Function { name, .. } if self.internal.contains(name.as_str()) => {
                entries.get(name).map(|entry| Some(entry.clone()))
            }
            GoDeclaration::Function { .. } | GoDeclaration::Variable { .. } => Some(None),
            _ => None,
        }
    }
}

impl Entry {
    pub(super) fn join(&self, other: &Entry) -> Entry {
        let mut joined = FxHashMap::default();
        for (key, value) in &self.0 {
            if let Some(other) = other.0.get(key) {
                joined.insert(*key, (*value).max(*other));
            }
        }
        Entry(joined)
    }

    /// The constraints of `self` that `joined` keeps as they were.
    fn widen(&self, joined: &Entry) -> Entry {
        let kept = self.0.iter().filter(|(key, value)| joined.0.get(key) == Some(value));
        Entry(kept.map(|(key, value)| (*key, *value)).collect())
    }
}

/// The functions some code refers to other than by calling them.
fn used_as_values(declarations: &mut [GoDeclaration]) -> FxHashSet<String> {
    struct Values(FxHashSet<String>);
    impl Walk for Values {
        fn expression(&mut self, value: &mut GoExpression) {
            match value {
                GoExpression::Call { function, arguments } => {
                    if !matches!(&**function, GoExpression::Identifier(_)) {
                        self.expression(function);
                    }
                    arguments.iter_mut().for_each(|argument| self.expression(argument));
                }
                GoExpression::Identifier(name) => {
                    self.0.insert(name.clone());
                }
                _ => go_traversal::expression(self, value),
            }
        }
    }
    let mut values = Values(FxHashSet::default());
    for declaration in declarations.iter_mut() {
        go_traversal::declaration(&mut values, declaration);
    }
    values.0
}
