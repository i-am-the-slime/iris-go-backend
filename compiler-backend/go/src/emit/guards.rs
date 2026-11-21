//! Accesses guarded by one combined bounds test.
//!
//! A swap of two elements reads and writes each index once, and each of the four accesses tests
//! its index on its own:
//!
//! ```go
//! within := i >= 0 && int(i) < len(array)
//! var x int32
//! if within { x = array[i] } else { x = 0 }
//! within2 := j >= 0 && int(j) < len(array)
//! var y int32
//! if within2 { y = array[j] } else { y = 0 }
//! if i >= 0 && int(i) < len(array) { array[i] = y }
//! if j >= 0 && int(j) < len(array) { array[j] = x }
//! ```
//!
//! When nothing between the tests assigns what they read or changes an array's length, every
//! test gives at each access what it would give at the first. One condition joining the distinct
//! tests then guards a copy of the statements in which every access is taken as passed, and the
//! statements as they were run only when some index is out of bounds:
//!
//! ```go
//! if i >= 0 && int(i) < len(array) && j >= 0 && int(j) < len(array) {
//!     x := array[i]; y := array[j]; array[i] = y; array[j] = x   // as Go spells it, in lines
//! } else {
//!     ... the statements above ...
//! }
//! ```
//!
//! Go proves each access of the copy from the condition, so the swap tests two indices once.

use rustc_hash::FxHashSet;

use super::headers::{Effects, Keeping, assigned_root, fresh, is_bounds_test, reads};
use super::locals::NUMBERED;
use crate::syntax::{GoDeclaration, GoExpression, GoStatement};
use crate::walk::{self, Walk};

/// The statements one combined test may guard, counted with the statements of their blocks:
/// every one of them is copied.
const GUARDED_SIZE: usize = 48;

pub(super) fn guard_accesses_together(declarations: &mut [GoDeclaration], effects: &Effects) {
    let keeping = Keeping::of(declarations, effects);
    for declaration in declarations.iter_mut() {
        let mut names = declaration.all_names();
        let GoDeclaration::Function { body, .. } = declaration else { continue };
        Together { keeping: &keeping, names: &mut names }.block(body);
    }
}

struct Together<'k, 'e, 'n> {
    keeping: &'k Keeping<'e>,
    names: &'n mut FxHashSet<String>,
}

impl Walk for Together<'_, '_, '_> {
    /// Nested blocks first, so that the statements a combined test guards are never looked at
    /// again.
    fn block(&mut self, body: &mut Vec<GoStatement>) {
        body.iter_mut().for_each(|statement| self.statement(statement));
        let mut start = 0;
        while start < body.len() {
            start = match self.run_at(body, start) {
                Some(run) => self.guard(body, run).unwrap_or(start + 1),
                None => start + 1,
            };
        }
    }
}

/// Statements `start..end` of a block whose bounds tests may all be taken at `start`.
struct Run {
    start: usize,
    end: usize,
    /// The distinct tests, in the order they are first taken.
    tests: Vec<GoExpression>,
    /// The names bound to a test, `within := test`.
    named: FxHashSet<String>,
    /// The positions of the accesses: `if test { ... }`, or `if within { ... }`.
    sites: Vec<usize>,
    /// The variables the run declares, `var x T`, declared before the combined test so that
    /// both of its branches and the rest of the block see them.
    hoisted: Vec<usize>,
}

impl Together<'_, '_, '_> {
    /// The longest run from `start` that repeats a test, if there is one.
    fn run_at(&self, block: &mut [GoStatement], start: usize) -> Option<Run> {
        let mut run = Run {
            start,
            end: start,
            tests: vec![],
            named: FxHashSet::default(),
            sites: vec![],
            hoisted: vec![],
        };
        let mut rendered: Vec<String> = vec![];
        let mut read = FxHashSet::default();
        let mut written = FxHashSet::default();
        let mut defined = FxHashSet::default();
        let mut size = 0;
        for position in start..block.len() {
            let statement = &mut block[position];
            size += statement_count(statement);
            if size > GUARDED_SIZE || !self.keeping.keeps(std::slice::from_mut(statement)) {
                break;
            }
            let Some(kind) = Kind::of(statement, &run.named) else { break };
            if position == start && matches!(kind, Kind::Plain | Kind::NamedSite) {
                return None;
            }
            let changed = changed_names(statement);
            if !changed.is_disjoint(&read) {
                break;
            }
            if let Some(test) = kind.test() {
                let reads = reads(test);
                if !reads.is_disjoint(&written) || !reads.is_disjoint(&defined) {
                    break;
                }
                read.extend(reads);
                let key = format!("{test:?}");
                if !rendered.contains(&key) {
                    rendered.push(key);
                    run.tests.push(test.clone());
                }
                if let Kind::Test(name, _) = &kind {
                    run.named.insert(name.clone());
                }
            }
            written.extend(changed);
            defined.extend(defined_names(statement));
            if matches!(kind, Kind::Site(..) | Kind::NamedSite) {
                run.sites.push(position);
                run.end = position + 1;
            }
        }
        if run.sites.len() <= run.tests.len() {
            return None;
        }
        self.scoped(block, run)
    }

    /// The run, with the variables it declares to be hoisted before it, or nothing when the
    /// rest of the block reads another name it defines.
    fn scoped(&self, block: &mut [GoStatement], mut run: Run) -> Option<Run> {
        let mut later = FxHashSet::default();
        for statement in &mut block[run.end..] {
            walk::each_expression_in_statement(statement, |expression| {
                if let GoExpression::Identifier(name) = expression {
                    later.insert(name.clone());
                }
            });
        }
        for position in run.start..run.end {
            match &block[position] {
                GoStatement::Variable { value: None, .. } => run.hoisted.push(position),
                statement => {
                    if defined_names(statement).iter().any(|name| later.contains(name)) {
                        return None;
                    }
                }
            }
        }
        Some(run)
    }

    /// Replaces the run with its combined test, and returns the position after it. When the run
    /// takes one test, the other branch is the run with every access failed; otherwise it is the
    /// run as it was, as which test failed is not known.
    fn guard(&mut self, block: &mut Vec<GoStatement>, run: Run) -> Option<usize> {
        let statements: Vec<GoStatement> = block[run.start..run.end].to_vec();
        let (hoisted, statements): (Vec<_>, Vec<_>) = statements
            .into_iter()
            .enumerate()
            .partition(|(offset, _)| run.hoisted.contains(&(run.start + offset)));
        let hoisted: Vec<GoStatement> = hoisted.into_iter().map(|(_, statement)| statement).collect();
        let passed = self.decided(&run, &statements, true);
        let failed = match run.tests.len() {
            1 => self.decided(&run, &statements, false),
            _ => statements.into_iter().map(|(_, statement)| statement).collect(),
        };
        let condition = run
            .tests
            .into_iter()
            .flat_map(conjuncts)
            .reduce(|left, right| GoExpression::Binary {
                operator: "&&",
                left: Box::new(left),
                right: Box::new(right),
            })
            .expect("invariant violated: a run has a test");
        if !all_used(&passed) || !all_used(&failed) {
            return None;
        }
        let guarded = GoStatement::If { condition, then: passed, otherwise: failed };
        let replacement: Vec<GoStatement> = hoisted.into_iter().chain([guarded]).collect();
        let next = run.start + replacement.len();
        block.splice(run.start..run.end, replacement);
        Some(next)
    }

    /// The run's statements with every access's test taken as `passed`: each access is its
    /// branch for that outcome, and a test's name its value.
    fn decided(
        &mut self,
        run: &Run,
        statements: &[(usize, GoStatement)],
        passed: bool,
    ) -> Vec<GoStatement> {
        let mut decided = vec![];
        for (offset, statement) in statements.iter().cloned() {
            match statement {
                GoStatement::Define { names, .. } if run.named.contains(&names[0]) => {}
                GoStatement::If { then, otherwise, .. }
                    if run.sites.contains(&(run.start + offset)) =>
                {
                    let branch = if passed { then } else { otherwise };
                    decided.extend(self.renamed_apart(branch));
                }
                statement => decided.push(statement),
            }
        }
        for statement in &mut decided {
            walk::each_expression_in_statement(statement, |expression| {
                if let GoExpression::Identifier(name) = expression
                    && run.named.contains(name)
                {
                    *expression = GoExpression::Boolean(passed);
                }
            });
        }
        decided
    }

    /// An access's statements, to be spliced into the block around it: each name they define
    /// is a fresh one, so that it neither clashes with nor hides another.
    fn renamed_apart(&mut self, mut statements: Vec<GoStatement>) -> Vec<GoStatement> {
        let defined: Vec<String> = statements.iter().flat_map(defined_names).collect();
        for name in defined {
            let base = name.split(NUMBERED).next().unwrap_or(&name).to_string();
            let renamed = fresh(&base, self.names);
            for statement in &mut statements {
                rename(statement, &name, &renamed);
            }
        }
        statements
    }
}

/// Whether the block reads every name it defines, as Go requires: a branch without an access
/// may leave a value only the access read.
fn all_used(block: &[GoStatement]) -> bool {
    let mut read = FxHashSet::default();
    for statement in &mut block.to_vec() {
        walk::each_expression_in_statement(statement, |expression| {
            if let GoExpression::Identifier(name) = expression {
                read.insert(name.clone());
            }
        });
    }
    block.iter().flat_map(defined_names).all(|name| read.contains(&name))
}

/// The tests a condition joins with `&&`, in order.
fn conjuncts(condition: GoExpression) -> Vec<GoExpression> {
    match condition {
        GoExpression::Binary { operator: "&&", left, right } => {
            let mut all = conjuncts(*left);
            all.extend(conjuncts(*right));
            all
        }
        condition => vec![condition],
    }
}

/// What a statement of a run does.
enum Kind {
    /// `name := test`
    Test(String, GoExpression),
    /// `if test { access }`
    Site(GoExpression),
    /// `if name { access }`, after `name := test`
    NamedSite,
    /// Anything else the run may hold.
    Plain,
}

impl Kind {
    fn of(statement: &GoStatement, named: &FxHashSet<String>) -> Option<Kind> {
        Some(match statement {
            GoStatement::Define { names, values }
                if names.len() == 1 && values.len() == 1 && is_bounds_test(&values[0]) =>
            {
                Kind::Test(names[0].clone(), values[0].clone())
            }
            GoStatement::If { condition: GoExpression::Identifier(name), .. }
                if named.contains(name) =>
            {
                Kind::NamedSite
            }
            GoStatement::If { condition, .. } if is_bounds_test(condition) => {
                Kind::Site(condition.clone())
            }
            GoStatement::Define { .. }
            | GoStatement::Variable { .. }
            | GoStatement::Assign { .. }
            | GoStatement::Expression(_)
            | GoStatement::If { .. }
            | GoStatement::Line(_) => Kind::Plain,
            _ => return None,
        })
    }

    /// The bounds test the statement takes.
    fn test(&self) -> Option<&GoExpression> {
        match self {
            Kind::Test(_, test) | Kind::Site(test) => Some(test),
            Kind::NamedSite | Kind::Plain => None,
        }
    }
}

/// The names a statement binds in its own block.
fn defined_names(statement: &GoStatement) -> Vec<String> {
    match statement {
        GoStatement::Define { names, .. } => names.clone(),
        GoStatement::Variable { name, .. } => vec![name.clone()],
        _ => vec![],
    }
}

/// The names a statement assigns, in its own block or in one nested in it. An element written
/// through a slice leaves the slice as it was.
fn changed_names(statement: &mut GoStatement) -> FxHashSet<String> {
    struct Changed(FxHashSet<String>);
    impl Walk for Changed {
        fn statement(&mut self, statement: &mut GoStatement) {
            if let GoStatement::Assign { targets, .. } = statement {
                for target in targets.iter() {
                    if let Some(root) = assigned_root(target) {
                        self.0.insert(root.to_string());
                    }
                }
            }
            walk::statement(self, statement);
        }

        fn expression(&mut self, value: &mut GoExpression) {
            if let GoExpression::Address(inner) = value
                && let Some(root) = super::aliases::target_root(inner)
            {
                self.0.insert(root.to_string());
            }
            walk::expression(self, value);
        }
    }
    let mut changed = Changed(FxHashSet::default());
    changed.statement(statement);
    changed.0
}

fn statement_count(statement: &mut GoStatement) -> usize {
    struct Count(usize);
    impl Walk for Count {
        fn statement(&mut self, statement: &mut GoStatement) {
            self.0 += 1;
            walk::statement(self, statement);
        }
    }
    let mut count = Count(0);
    count.statement(statement);
    count.0
}

/// Every occurrence of `from` in the statement, bound or used, renamed to `to`.
fn rename(statement: &mut GoStatement, from: &str, to: &str) {
    struct Rename<'a>(&'a str, &'a str);
    impl Walk for Rename<'_> {
        fn statement(&mut self, statement: &mut GoStatement) {
            match statement {
                GoStatement::Define { names, .. } => rename_in(names, self.0, self.1),
                GoStatement::Variable { name, .. } if name == self.0 => *name = self.1.to_string(),
                _ => {}
            }
            walk::statement(self, statement);
        }

        fn expression(&mut self, value: &mut GoExpression) {
            if let GoExpression::Identifier(name) = value
                && name == self.0
            {
                *name = self.1.to_string();
            }
            walk::expression(self, value);
        }
    }
    Rename(from, to).statement(statement);
}

fn rename_in(names: &mut [String], from: &str, to: &str) {
    for name in names.iter_mut().filter(|name| *name == from) {
        *name = to.to_string();
    }
}
