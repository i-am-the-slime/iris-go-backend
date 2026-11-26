//! Views of strings that a loop indexes without changing them.
//!
//! JavaScript indexes a string by UTF-16 code unit in constant time; a Go
//! string is UTF-8, so `charAt i`, `indexOf'` from an offset, `take`, `drop`
//! and `slice` each walk the string from its start to find code unit `i`, and
//! a loop that indexes its way through a string is quadratic. The same holds
//! for `codePointAt i` and `take n` by code point.
//!
//! Where a loop indexes a string the loop never changes at a position that is
//! not a literal, the string is viewed once before the loop, by
//! `prim.UTF16(text)` or `direct.CodePoints(text)`, and every operation on it
//! in the loop asks the view instead: `textUnits.CharAt(just, nothing, i)`.
//! Viewing costs one walk of the string, which the first index past its middle
//! would cost anyway. An index that is a literal walks only as far as the
//! literal, so it alone does not make a view pay.

use rustc_hash::{FxHashMap, FxHashSet};

use super::mutable::in_bounds;
use crate::syntax::{GoExpression, GoStatement, GoType, Name, statements_names};

use crate::go_traversal::{each_block, each_expression_in_statement};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum View {
    CodeUnits,
    CodePoints,
}

impl View {
    fn package(self) -> &'static str {
        match self {
            View::CodeUnits => "prim",
            View::CodePoints => "direct",
        }
    }

    fn constructor(self) -> &'static str {
        match self {
            View::CodeUnits => "UTF16",
            View::CodePoints => "CodePoints",
        }
    }

    fn suffix(self) -> &'static str {
        match self {
            View::CodeUnits => "Units",
            View::CodePoints => "Points",
        }
    }
}

/// A string operation that a view answers by the method of the same meaning.
/// The string is the operation's last argument; the view's method takes the
/// others but the ignored ones.
struct Operation {
    view: View,
    function: &'static str,
    method: &'static str,
    /// The arguments that are positions in the string.
    positions: &'static [usize],
    /// The fallbacks the native operation ignores.
    ignored: &'static [usize],
}

const OPERATIONS: &[Operation] = &[
    units("CodeUnitLength", "Length", &[]),
    units("CodeUnitCharAt", "CharAt", &[0]),
    units("CharAt", "UnsafeCharAt", &[0]),
    units("CodeUnitIndexOfStartingAt", "IndexOfStartingAt", &[1]),
    units("CodeUnitLastIndexOfStartingAt", "LastIndexOfStartingAt", &[1]),
    units("CodeUnitTake", "Take", &[0]),
    units("CodeUnitDrop", "Drop", &[0]),
    units("CodeUnitSlice", "Slice", &[0, 1]),
    points("CodePointLength", "Length", &[], &[]),
    points("CodePointAt", "CodePointAt", &[2], &[0, 1]),
    points("CodePointTake", "Take", &[1], &[0]),
];

const fn units(
    function: &'static str,
    method: &'static str,
    positions: &'static [usize],
) -> Operation {
    Operation { view: View::CodeUnits, function, method, positions, ignored: &[] }
}

const fn points(
    function: &'static str,
    method: &'static str,
    positions: &'static [usize],
    ignored: &'static [usize],
) -> Operation {
    Operation { view: View::CodePoints, function, method, positions, ignored }
}

/// Views, before the loop, the strings the loop indexes without changing,
/// and returns each view's local with the value it holds. `changed` holds
/// every variable the loop binds or writes, `locals` the variables the
/// enclosing declaration binds, and `fresh` names a new local.
pub(super) fn view_invariant_strings(
    looped: &mut Vec<GoStatement>,
    changed: &FxHashSet<String>,
    locals: &FxHashSet<String>,
    fresh: &mut dyn FnMut(String) -> String,
) -> Vec<(String, GoExpression)> {
    let unchanged = |name: &str| locals.contains(name) && !changed.contains(name);
    let aliases = aliases(looped, &unchanged);
    let viewed_string = |name: &str| match aliases.get(name) {
        Some(original) => Some(original.clone()),
        None => unchanged(name).then(|| name.to_string()),
    };
    let mut indexed: Vec<(String, View)> = vec![];
    for statement in looped.iter_mut() {
        each_expression_in_statement(statement, |value| {
            let Some((operation, string)) = operation_on(value) else { return };
            let Some(string) = viewed_string(string) else { return };
            if indexes_at_a_variable_position(operation, value)
                && !indexed.contains(&(string.clone(), operation.view))
            {
                indexed.push((string, operation.view));
            }
        });
    }
    if indexed.is_empty() {
        return vec![];
    }
    let views: Vec<((String, View), String)> = indexed
        .into_iter()
        .map(|(string, view)| {
            let local = fresh(format!("{string}{}", view.suffix()));
            ((string, view), local)
        })
        .collect();
    for statement in looped.iter_mut() {
        each_expression_in_statement(statement, |value| {
            let Some((operation, string)) = operation_on(value) else { return };
            let Some(string) = viewed_string(string) else { return };
            let Some((_, local)) =
                views.iter().find(|(viewed, _)| *viewed == (string.clone(), operation.view))
            else {
                return;
            };
            ask_view(value, operation, local);
        });
    }
    let aliases: FxHashSet<String> = aliases.into_keys().collect();
    drop_unused_aliases(looped, &aliases);
    let mut definitions: Vec<(String, GoExpression)> = vec![];
    for ((string, view), local) in views {
        let value = GoExpression::Call {
            function: Box::new(GoExpression::Qualified {
                package: view.package().into(),
                name: view.constructor().into(),
            }),
            arguments: vec![GoExpression::Identifier(string.clone())],
        };
        definitions.push((local.clone(), value));
        if view == View::CodeUnits {
            definitions.extend(read_ascii_bytes(looped, &string, &local, fresh));
        }
    }
    definitions
}

/// Each `char, found := textUnits.CharAt(i)` of the loop reads a code unit of ASCII text as its
/// byte, where Go inlines it, and asks the view only otherwise:
///
/// ```go
/// var char rune
/// found := i >= 0 && i < len(textASCII)
/// if found {
///     char = rune(textASCII[i])
/// } else {
///     char, found = textUnits.CharAt(i)
/// }
/// ```
///
/// with `textASCII := textUnits.ASCII()` before the loop, the text when every code unit is
/// one byte of it and "" otherwise. Returns that definition when a read uses it.
fn read_ascii_bytes(
    looped: &mut Vec<GoStatement>,
    string: &str,
    view: &str,
    fresh: &mut dyn FnMut(String) -> String,
) -> Option<(String, GoExpression)> {
    let ascii = fresh(format!("{string}ASCII"));
    let mut read = false;
    // A read moved behind the ASCII test is visited again in its new block.
    let mut moved: FxHashSet<String> = FxHashSet::default();
    each_block(looped, |block| {
        let mut position = 0;
        while position < block.len() {
            if let Some((char, found, index)) = char_at_definition(&block[position], view)
                && !moved.contains(&found)
            {
                let byte = GoExpression::Conversion {
                    type_: GoType::Rune,
                    value: Box::new(GoExpression::Index {
                        value: Box::new(GoExpression::Identifier(ascii.clone())),
                        index: Box::new(index.clone()),
                    }),
                };
                if let Some(built) = built_from_char(block, position, &char, &found, &byte) {
                    moved.insert(found.clone());
                    let asked = block.drain(position + 1..position + 3).collect::<Vec<_>>();
                    let defined = std::mem::replace(&mut block[position], built.variable);
                    block.insert(
                        position + 1,
                        GoStatement::If {
                            condition: in_bounds(&index, GoExpression::Identifier(ascii.clone())),
                            then: vec![built.from_byte],
                            otherwise: [vec![defined], asked[1..].to_vec()].concat(),
                        },
                    );
                    read = true;
                    position += 2;
                    continue;
                }
                let asked = block[position].clone();
                let GoStatement::Define { values, .. } = asked else { unreachable!() };
                let targets =
                    [&char, &found].map(|name| GoExpression::Identifier(name.clone())).to_vec();
                let mut rewritten = vec![];
                let mut then = vec![];
                if char != "_" {
                    rewritten.push(GoStatement::Variable {
                        name: char.clone(),
                        type_: GoType::Rune,
                        value: None,
                    });
                    then.push(GoStatement::Assign {
                        targets: vec![GoExpression::Identifier(char.clone())],
                        values: vec![byte],
                    });
                }
                rewritten.push(GoStatement::Define {
                    names: vec![found.clone()],
                    values: vec![in_bounds(&index, GoExpression::Identifier(ascii.clone()))],
                });
                let asked = vec![GoStatement::Assign { targets, values }];
                let found = GoExpression::Identifier(found);
                rewritten.push(match then.is_empty() {
                    true => GoStatement::If {
                        condition: GoExpression::Unary { operator: "!", operand: Box::new(found) },
                        then: asked,
                        otherwise: vec![],
                    },
                    false => GoStatement::If { condition: found, then, otherwise: asked },
                });
                let added = rewritten.len();
                block.splice(position..=position, rewritten);
                read = true;
                position += added;
                continue;
            }
            position += 1;
        }
    });
    let value = GoExpression::Call {
        function: Box::new(GoExpression::Field {
            value: Box::new(GoExpression::Identifier(view.to_string())),
            name: "ASCII".into(),
        }),
        arguments: vec![],
    };
    read.then_some((ascii, value))
}

/// The Maybe that `var maybe T; if found { maybe = just(char) } else { maybe = nothing }` builds
/// right after `char, found := view.CharAt(i)`, where nothing later reads `char` or `found`.
struct BuiltFromChar {
    variable: GoStatement,
    /// `maybe = just(byte)`.
    from_byte: GoStatement,
}

fn built_from_char(
    block: &mut [GoStatement],
    position: usize,
    char: &str,
    found: &str,
    byte: &GoExpression,
) -> Option<BuiltFromChar> {
    let [
        variable @ GoStatement::Variable { name, value: None, .. },
        GoStatement::If { condition: GoExpression::Identifier(tested), then, otherwise },
    ] = block.get(position + 1..position + 3)?
    else {
        return None;
    };
    let [GoStatement::Assign { targets, values }] = then.as_slice() else { return None };
    let ([GoExpression::Identifier(target)], [GoStatement::Assign { .. }]) =
        (targets.as_slice(), otherwise.as_slice())
    else {
        return None;
    };
    if tested != found || target != name {
        return None;
    }
    let variable = variable.clone();
    let mut from_byte = GoStatement::Assign { targets: targets.clone(), values: values.clone() };
    let mut read_later = false;
    statements_names(&mut block[position + 3..], &mut |name| {
        if let Name::Reference(name) | Name::Written(name) = name {
            read_later |= name == char || name == found;
        }
    });
    if read_later {
        return None;
    }
    each_expression_in_statement(&mut from_byte, |value| {
        if matches!(value, GoExpression::Identifier(name) if name == char) {
            *value = byte.clone();
        }
    });
    Some(BuiltFromChar { variable, from_byte })
}

/// `char, found := view.CharAt(i)`, whose `i` is as cheap to repeat as to read, as its two
/// names and `i`.
fn char_at_definition(
    statement: &GoStatement,
    view: &str,
) -> Option<(String, String, GoExpression)> {
    let GoStatement::Define { names, values } = statement else { return None };
    let ([char, found], [GoExpression::Call { function, arguments }]) =
        (names.as_slice(), values.as_slice())
    else {
        return None;
    };
    let GoExpression::Field { value, name } = &**function else { return None };
    let ([index], GoExpression::Identifier(viewed)) = (arguments.as_slice(), &**value) else {
        return None;
    };
    (viewed == view && name == "CharAt" && found != "_" && is_repeatable(index))
        .then(|| (char.clone(), found.clone(), index.clone()))
}

fn is_repeatable(value: &GoExpression) -> bool {
    match value {
        GoExpression::Identifier(_)
        | GoExpression::Qualified { .. }
        | GoExpression::Integer(_)
        | GoExpression::Rune(_)
        | GoExpression::Boolean(_) => true,
        GoExpression::Conversion { value, .. } => is_repeatable(value),
        _ => false,
    }
}

/// The variables that the loop writes only with copies of themselves, as a
/// loop does that carries a variable through a closure's captured copy:
/// `textCaptured := text` and later `text = textCaptured`. Such a variable
/// keeps the value it entered the loop with.
pub(super) fn carried_unchanged(
    looped: &mut Vec<GoStatement>,
    written_by_literals: &FxHashSet<String>,
) -> FxHashSet<String> {
    let mut bindings: FxHashMap<String, usize> = FxHashMap::default();
    let mut writes: FxHashMap<String, usize> = FxHashMap::default();
    statements_names(looped, &mut |name| match name {
        Name::Binder(name) => *bindings.entry(name.clone()).or_default() += 1,
        Name::Written(name) => *writes.entry(name.clone()).or_default() += 1,
        Name::Reference(_) => {}
    });
    let mut copies: FxHashMap<String, String> = FxHashMap::default();
    let mut copied_back: FxHashMap<(String, String), usize> = FxHashMap::default();
    each_block(looped, |block| {
        for statement in block.iter() {
            match statement {
                GoStatement::Define { names, values } => {
                    if let ([copy], [GoExpression::Identifier(original)]) =
                        (names.as_slice(), values.as_slice())
                    {
                        copies.insert(copy.clone(), original.clone());
                    }
                }
                GoStatement::Assign { targets, values } if targets.len() == values.len() => {
                    for (target, value) in targets.iter().zip(values) {
                        if let (GoExpression::Identifier(target), GoExpression::Identifier(value)) =
                            (target, value)
                        {
                            *copied_back.entry((target.clone(), value.clone())).or_default() += 1;
                        }
                    }
                }
                _ => {}
            }
        }
    });
    let is_copy = |copy: &str| bindings.get(copy) == Some(&1) && !writes.contains_key(copy);
    let mut carried = FxHashSet::default();
    for (variable, &written) in &writes {
        if bindings.contains_key(variable) || written_by_literals.contains(variable) {
            continue;
        }
        let restored: usize = copies
            .iter()
            .filter(|(copy, original)| *original == variable && is_copy(copy))
            .map(|(copy, _)| {
                copied_back.get(&(variable.clone(), copy.clone())).copied().unwrap_or(0)
            })
            .sum();
        if restored == written {
            carried.insert(variable.clone());
        }
    }
    carried
}

/// The locals the loop defines once as another name for an unchanged string,
/// `s := text`, and never write, with the string each stands for.
fn aliases(
    looped: &mut Vec<GoStatement>,
    unchanged: &dyn Fn(&str) -> bool,
) -> FxHashMap<String, String> {
    let mut bindings: FxHashMap<String, usize> = FxHashMap::default();
    let mut written: FxHashSet<String> = FxHashSet::default();
    statements_names(looped, &mut |name| match name {
        Name::Binder(name) => *bindings.entry(name.clone()).or_default() += 1,
        Name::Written(name) => {
            written.insert(name.clone());
        }
        Name::Reference(_) => {}
    });
    let mut aliases = FxHashMap::default();
    each_block(looped, |block| {
        for statement in block.iter() {
            let GoStatement::Define { names, values } = statement else { continue };
            let ([alias], [GoExpression::Identifier(original)]) =
                (names.as_slice(), values.as_slice())
            else {
                continue;
            };
            if bindings.get(alias) == Some(&1) && !written.contains(alias) && unchanged(original) {
                aliases.insert(alias.clone(), original.clone());
            }
        }
    });
    aliases
}

/// The operation `value` calls on the string named by its last argument.
fn operation_on(value: &GoExpression) -> Option<(&'static Operation, &str)> {
    let GoExpression::Call { function, arguments } = value else { return None };
    let GoExpression::Qualified { package, name } = &**function else { return None };
    let operation = OPERATIONS
        .iter()
        .find(|operation| operation.view.package() == package && operation.function == name)?;
    let Some(GoExpression::Identifier(string)) = arguments.last() else { return None };
    Some((operation, string))
}

fn indexes_at_a_variable_position(operation: &Operation, value: &GoExpression) -> bool {
    let GoExpression::Call { arguments, .. } = value else { return false };
    operation.positions.iter().any(|&position| !is_literal(&arguments[position]))
}

fn is_literal(value: &GoExpression) -> bool {
    match value {
        GoExpression::Integer(_) => true,
        GoExpression::Conversion { value, .. } => is_literal(value),
        _ => false,
    }
}

/// Turns `package.Function(arguments..., string)` into
/// `local.Method(arguments...)`.
fn ask_view(value: &mut GoExpression, operation: &Operation, local: &str) {
    let GoExpression::Call { function, arguments } = value else { return };
    arguments.pop();
    let mut position = 0;
    arguments.retain(|_| {
        let kept = !operation.ignored.contains(&position);
        position += 1;
        kept
    });
    **function = GoExpression::Field {
        value: Box::new(GoExpression::Identifier(local.to_string())),
        name: operation.method.into(),
    };
}

/// Removes the definitions of aliases that the views left without a use.
fn drop_unused_aliases(looped: &mut Vec<GoStatement>, aliases: &FxHashSet<String>) {
    let mut used: FxHashSet<String> = FxHashSet::default();
    statements_names(looped, &mut |name| {
        if let Name::Reference(name) | Name::Written(name) = name {
            used.insert(name.clone());
        }
    });
    each_block(looped, |block| {
        block.retain(|statement| {
            let GoStatement::Define { names, .. } = statement else { return true };
            let [alias] = names.as_slice() else { return true };
            !aliases.contains(alias) || used.contains(alias)
        });
    });
}
