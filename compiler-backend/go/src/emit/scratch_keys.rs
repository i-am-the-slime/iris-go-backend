use rustc_hash::FxHashSet;

use super::aliases::mentions;
use super::{call, identifier_expression};
use crate::syntax::{GoDeclaration, GoExpression, GoStatement, GoType, GoUnaryOperator};

const SCRATCH: &str = "scratch";

pub(super) fn build_looked_up_keys_in_scratch(
    declarations: &mut [GoDeclaration],
    taken: &dyn Fn(&str) -> bool,
) {
    for declaration in declarations {
        let mut names = declaration.all_names();
        let GoDeclaration::Function { body, .. } = declaration else { continue };
        let mut scratch = None;
        statements(body, false, &mut scratch, &mut names, taken);
        if let Some(scratch) = scratch {
            body.insert(0, GoStatement::Variable { name: scratch, type_: bytes(), value: None });
        }
    }
}

fn statements(
    block: &mut [GoStatement],
    looping: bool,
    scratch: &mut Option<String>,
    names: &mut FxHashSet<String>,
    taken: &dyn Fn(&str) -> bool,
) {
    let mut position = 0;
    while position < block.len() {
        if looping {
            build_in_scratch_at(block, position, scratch, names, taken);
        }
        match &mut block[position] {
            GoStatement::If { then, otherwise, .. } => {
                statements(then, looping, scratch, names, taken);
                statements(otherwise, looping, scratch, names, taken);
            }
            GoStatement::IfAssert { then, .. } => statements(then, looping, scratch, names, taken),
            GoStatement::Switch { cases, default, .. } => {
                for case in cases {
                    statements(&mut case.body, looping, scratch, names, taken);
                }
                if let Some(default) = default {
                    statements(&mut default.body, looping, scratch, names, taken);
                }
            }
            GoStatement::Loop(body)
            | GoStatement::Range { body, .. }
            | GoStatement::Counting { body, .. }
            | GoStatement::CountingDown { body, .. }
            | GoStatement::LabeledLoop { body, .. } => {
                statements(body, true, scratch, names, taken)
            }
            _ => {}
        }
        position += 1;
    }
}

/// `key := prim.Concat(…)`, then `_, found := table[key]`, then `if found { … }`, with the key
/// read nowhere else.
fn build_in_scratch_at(
    block: &mut [GoStatement],
    position: usize,
    scratch: &mut Option<String>,
    names: &mut FxHashSet<String>,
    taken: &dyn Fn(&str) -> bool,
) {
    let Some((key, parts)) = concatenation(&block[position]) else { return };
    let Some(lookup) = next_statement(block, position) else { return };
    let Some(found) = lookup_of(&mut block[lookup], &key) else { return };
    let Some(branch) = next_statement(block, lookup) else { return };
    if !tests(&block[branch], &found)
        || block[branch + 1..].iter_mut().any(|later| mentions(later, &key))
    {
        return;
    }
    let scratch = scratch.get_or_insert_with(|| fresh_name(names, taken)).clone();
    let built = appended_parts(&scratch, parts);
    let GoStatement::Define { values, .. } = &mut block[lookup] else {
        unreachable!("invariant violated: the lookup is a definition")
    };
    let GoExpression::Index { index, .. } = &mut values[0] else {
        unreachable!("invariant violated: the lookup indexes its table")
    };
    **index = as_string(&scratch);
    let GoStatement::If { then, otherwise, .. } = &mut block[branch] else {
        unreachable!("invariant violated: the branch is an if")
    };
    for taken_branch in [then, otherwise] {
        if taken_branch.iter_mut().any(|statement| mentions(statement, &key)) {
            let define =
                GoStatement::Define { names: vec![key.clone()], values: vec![as_string(&scratch)] };
            taken_branch.insert(0, define);
        }
    }
    block[position] =
        GoStatement::Assign { targets: vec![identifier_expression(&scratch)], values: vec![built] };
}

fn concatenation(statement: &GoStatement) -> Option<(String, Vec<GoExpression>)> {
    let GoStatement::Define { names, values } = statement else { return None };
    let ([key], [value]) = (names.as_slice(), values.as_slice()) else { return None };
    let GoExpression::Call { function, arguments } = value.unattributed() else { return None };
    let concatenates = matches!(function.unattributed(), GoExpression::Qualified { package, name }
        if package == "prim" && (name == "Concat" || name == "Append"));
    (concatenates && key != "_").then(|| (key.clone(), arguments.clone()))
}

fn next_statement(block: &[GoStatement], position: usize) -> Option<usize> {
    (position + 1..block.len()).find(|&index| !matches!(block[index], GoStatement::Line(_)))
}

/// The answer of `_, found := table[key]` or `value, found := table[key]`.
fn lookup_of(statement: &mut GoStatement, key: &str) -> Option<String> {
    let GoStatement::Define { names, values } = statement else { return None };
    let ([_, found], [GoExpression::Index { value: table, index }]) =
        (names.as_slice(), values.as_mut_slice())
    else {
        return None;
    };
    let indexes_by_key =
        matches!(index.unattributed(), GoExpression::Identifier(name) if name == key);
    let found = found.clone();
    let mut table = GoStatement::Expression((**table).clone());
    (indexes_by_key && found != "_" && !mentions(&mut table, key)).then_some(found)
}

fn tests(statement: &GoStatement, found: &str) -> bool {
    let GoStatement::If { condition, .. } = statement else { return false };
    let condition = match condition.unattributed() {
        GoExpression::Unary { operator: GoUnaryOperator::Not, operand } => operand.unattributed(),
        condition => condition,
    };
    matches!(condition, GoExpression::Identifier(name) if name == found)
}

fn appended_parts(scratch: &str, parts: Vec<GoExpression>) -> GoExpression {
    let mut built = GoExpression::Slice {
        value: Box::new(identifier_expression(scratch)),
        low: None,
        high: Some(Box::new(GoExpression::Integer(0))),
    };
    for part in parts {
        let (append, appended) = match part.unattributed() {
            GoExpression::Call { function, arguments }
                if arguments.len() == 1
                    && matches!(function.unattributed(), GoExpression::Qualified { package, name }
                        if package == "prim" && name == "CharSingleton") =>
            {
                ("AppendRune", arguments[0].clone())
            }
            _ => ("AppendString", part),
        };
        let function = GoExpression::Qualified { package: "prim".into(), name: append.into() };
        built = call(function, vec![built, appended]);
    }
    built
}

fn as_string(scratch: &str) -> GoExpression {
    GoExpression::Conversion {
        type_: GoType::String,
        value: Box::new(identifier_expression(scratch)),
    }
}

fn bytes() -> GoType {
    GoType::Slice(Box::new(GoType::Named("byte".into())))
}

fn fresh_name(names: &mut FxHashSet<String>, taken: &dyn Fn(&str) -> bool) -> String {
    let mut candidate = SCRATCH.to_string();
    let mut suffix = 2;
    while names.contains(&candidate) || taken(&candidate) {
        candidate = format!("{SCRATCH}{suffix}");
        suffix += 1;
    }
    names.insert(candidate.clone());
    candidate
}
