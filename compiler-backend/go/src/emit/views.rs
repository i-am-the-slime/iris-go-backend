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
use super::{binary, builtin_call, call};
use crate::syntax::{
    GoBinaryOperator, GoBuiltin, GoExpression, GoStatement, GoType, GoUnaryOperator, Name,
    statements_names,
};

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
        match view {
            View::CodeUnits => definitions.extend(read_ascii_bytes(looped, &string, &local, fresh)),
            View::CodePoints => {
                definitions.extend(read_ascii_points(looped, &string, &local, fresh))
            }
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
    let reads =
        ByteReads { method: "CharAt", type_: GoType::Rune, text: ascii.clone(), test: None };
    let mut read = reads.rewrite(looped, view);
    let mut cut_names: FxHashSet<String> = FxHashSet::default();
    each_block(looped, |block| {
        let mut position = 0;
        while position < block.len() {
            let mut cuts = vec![];
            let asking = matches!(&block[position], GoStatement::Assign { targets, .. }
                if matches!(targets.as_slice(), [GoExpression::Identifier(name)] if cut_names.contains(name)));
            if !asking && let Some(values) = evaluated_first(&mut block[position]) {
                for value in values {
                    cut_ascii_text(value, view, &mut |cut| {
                        let name = fresh(format!("{string}Cut"));
                        cut_names.insert(name.clone());
                        cuts.push((name.clone(), cut));
                        GoExpression::Identifier(name)
                    });
                }
            }
            let mut hoisted = vec![];
            for (name, cut) in cuts {
                hoisted.extend(cut.statements(&name, &ascii));
            }
            read |= !hoisted.is_empty();
            position += hoisted.len() + 1;
            block.splice(position - hoisted.len() - 1..position - hoisted.len() - 1, hoisted);
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

fn read_ascii_points(
    looped: &mut Vec<GoStatement>,
    string: &str,
    view: &str,
    fresh: &mut dyn FnMut(String) -> String,
) -> Option<(String, GoExpression)> {
    let ascii = fresh(format!("{string}IsASCII"));
    let reads = ByteReads {
        method: "CodePointAt",
        type_: GoType::Int,
        text: string.to_string(),
        test: Some(ascii.clone()),
    };
    let tested = call(
        GoExpression::Qualified { package: "prim".into(), name: "IsASCII".into() },
        vec![GoExpression::Identifier(string.to_string())],
    );
    reads.rewrite(looped, view).then_some((ascii, tested))
}

struct ByteReads {
    method: &'static str,
    type_: GoType,
    text: String,
    test: Option<String>,
}

impl ByteReads {
    fn condition(&self, index: &GoExpression) -> GoExpression {
        let within = in_bounds(index, GoExpression::Identifier(self.text.clone()));
        match &self.test {
            Some(test) => {
                binary(GoBinaryOperator::LogicalAnd, GoExpression::Identifier(test.clone()), within)
            }
            None => within,
        }
    }

    fn rewrite(&self, looped: &mut Vec<GoStatement>, view: &str) -> bool {
        let mut read = false;
        let mut moved: FxHashSet<String> = FxHashSet::default();
        each_block(looped, |block| {
            let mut position = 0;
            while position < block.len() {
                match self.rewrite_at(block, position, view, &mut moved) {
                    Some(added) => {
                        read = true;
                        position += added;
                    }
                    None => position += 1,
                }
            }
        });
        read
    }

    fn rewrite_at(
        &self,
        block: &mut Vec<GoStatement>,
        position: usize,
        view: &str,
        moved: &mut FxHashSet<String>,
    ) -> Option<usize> {
        let (char, found, index) = char_at_definition(&block[position], view, self.method)?;
        if moved.contains(&found) {
            return None;
        }
        let byte = GoExpression::Conversion {
            type_: self.type_.clone(),
            value: Box::new(GoExpression::Index {
                value: Box::new(GoExpression::Identifier(self.text.clone())),
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
                    condition: self.condition(&index),
                    then: vec![built.from_byte],
                    otherwise: [vec![defined], asked[1..].to_vec()].concat(),
                },
            );
            return Some(2);
        }
        let asked = block[position].clone();
        let GoStatement::Define { values, .. } = asked else { unreachable!() };
        let targets = [&char, &found].map(|name| GoExpression::Identifier(name.clone())).to_vec();
        let mut rewritten = vec![];
        let mut then = vec![];
        if char != "_" {
            rewritten.push(GoStatement::Variable {
                name: char.clone(),
                type_: self.type_.clone(),
                value: None,
            });
            then.push(GoStatement::Assign {
                targets: vec![GoExpression::Identifier(char.clone())],
                values: vec![byte],
            });
        }
        rewritten.push(GoStatement::Define {
            names: vec![found.clone()],
            values: vec![self.condition(&index)],
        });
        let asked = vec![GoStatement::Assign { targets, values }];
        let found = GoExpression::Identifier(found);
        rewritten.push(match then.is_empty() {
            true => GoStatement::If {
                condition: GoExpression::Unary {
                    operator: GoUnaryOperator::Not,
                    operand: Box::new(found),
                },
                then: asked,
                otherwise: vec![],
            },
            false => GoStatement::If { condition: found, then, otherwise: asked },
        });
        let added = rewritten.len();
        block.splice(position..=position, rewritten);
        Some(added)
    }
}

/// A `view.Take(n)` or `view.Drop(n)` whose `n` is as cheap to repeat as to read.
struct Cut {
    kind: CutKind,
    asked: GoExpression,
}

enum CutKind {
    Take(GoExpression),
    Drop(GoExpression),
    Slice(GoExpression, GoExpression),
}

impl Cut {
    /// `var cut string` and the test that slices ASCII text and asks the view only otherwise:
    ///
    /// ```go
    /// if n > 0 && n <= len(textASCII) {
    ///     cut = textASCII[:n]
    /// } else {
    ///     cut = textUnits.Take(n)
    /// }
    /// ```
    ///
    /// and for a drop `n >= 0 && n < len(textASCII)` and `textASCII[n:]`.
    fn statements(self, name: &str, ascii: &str) -> [GoStatement; 2] {
        let text = || Box::new(GoExpression::Identifier(ascii.to_string()));
        let length = || builtin_call(GoBuiltin::Len, vec![*text()]);
        let (condition, sliced) = match self.kind {
            CutKind::Take(count) => {
                let positive =
                    binary(GoBinaryOperator::GreaterThan, count.clone(), GoExpression::Integer(0));
                let within = binary(GoBinaryOperator::LessThanOrEqual, count.clone(), length());
                let high = Some(Box::new(count));
                let sliced = GoExpression::Slice { value: text(), low: None, high };
                (binary(GoBinaryOperator::LogicalAnd, positive, within), sliced)
            }
            CutKind::Drop(count) => {
                let condition = in_bounds(&count, *text());
                let sliced =
                    GoExpression::Slice { value: text(), low: Some(Box::new(count)), high: None };
                (condition, sliced)
            }
            CutKind::Slice(begin, end) => {
                let natural = binary(
                    GoBinaryOperator::GreaterThanOrEqual,
                    begin.clone(),
                    GoExpression::Integer(0),
                );
                let ordered = binary(GoBinaryOperator::LessThanOrEqual, begin.clone(), end.clone());
                let within = binary(GoBinaryOperator::LessThanOrEqual, end.clone(), length());
                let condition = binary(
                    GoBinaryOperator::LogicalAnd,
                    binary(GoBinaryOperator::LogicalAnd, natural, ordered),
                    within,
                );
                let (low, high) = (Some(Box::new(begin)), Some(Box::new(end)));
                (condition, GoExpression::Slice { value: text(), low, high })
            }
        };
        let assign = |value| GoStatement::Assign {
            targets: vec![GoExpression::Identifier(name.to_string())],
            values: vec![value],
        };
        [
            GoStatement::Variable { name: name.to_string(), type_: GoType::String, value: None },
            GoStatement::If {
                condition,
                then: vec![assign(sliced)],
                otherwise: vec![assign(self.asked)],
            },
        ]
    }
}

/// The values a statement evaluates before anything else it does, when it is a definition, an
/// assignment, a call or a return.
fn evaluated_values(statement: &mut GoStatement) -> Option<Vec<&mut GoExpression>> {
    match statement {
        GoStatement::Define { values, .. } => Some(values.iter_mut().collect()),
        GoStatement::Assign { targets, values } => {
            let plain = targets.iter().all(|target| matches!(target, GoExpression::Identifier(_)));
            plain.then(|| values.iter_mut().collect())
        }
        GoStatement::Variable { value: Some(value), .. }
        | GoStatement::Expression(value)
        | GoStatement::Return(Some(value)) => Some(vec![value]),
        _ => None,
    }
}

pub(super) fn evaluated_first(statement: &mut GoStatement) -> Option<Vec<&mut GoExpression>> {
    match statement {
        GoStatement::If { condition: value, .. }
        | GoStatement::Switch { value: Some(value), .. } => Some(vec![value]),
        statement => evaluated_values(statement),
    }
}

/// Replaces each cut of the view in `value`, outside function literals and the branches of `&&`
/// and `||`, by what `replace` names it.
fn cut_ascii_text(
    value: &mut GoExpression,
    view: &str,
    replace: &mut dyn FnMut(Cut) -> GoExpression,
) {
    if let Some(cut) = cut_of(value, view) {
        *value = replace(cut);
        return;
    }
    match value {
        GoExpression::Call { function, arguments } => {
            cut_ascii_text(function, view, replace);
            arguments.iter_mut().for_each(|argument| cut_ascii_text(argument, view, replace));
        }
        GoExpression::Binary { operator, left, .. } if operator.is_logical() => {
            cut_ascii_text(left, view, replace);
        }
        GoExpression::Binary { left, right, .. } => {
            cut_ascii_text(left, view, replace);
            cut_ascii_text(right, view, replace);
        }
        GoExpression::Composite { fields, .. } => {
            fields.iter_mut().for_each(|(_, field)| cut_ascii_text(field, view, replace));
        }
        GoExpression::Unary { operand: value, .. }
        | GoExpression::Conversion { value, .. }
        | GoExpression::Spread(value)
        | GoExpression::Attributed { value, .. } => cut_ascii_text(value, view, replace),
        _ => {}
    }
}

fn cut_of(value: &GoExpression, view: &str) -> Option<Cut> {
    let GoExpression::Call { function, arguments } = value else { return None };
    let GoExpression::Field { value: viewed, name } = &**function else { return None };
    let GoExpression::Identifier(viewed) = &**viewed else { return None };
    if viewed != view || !arguments.iter().all(is_repeatable_count) {
        return None;
    }
    let kind = match (name.as_str(), arguments.as_slice()) {
        ("Take", [count]) => CutKind::Take(count.clone()),
        ("Drop", [count]) => CutKind::Drop(count.clone()),
        ("Slice", [begin, end]) => CutKind::Slice(begin.clone(), end.clone()),
        _ => return None,
    };
    Some(Cut { kind, asked: value.clone() })
}

fn is_repeatable_count(value: &GoExpression) -> bool {
    match value {
        GoExpression::Binary {
            operator:
                GoBinaryOperator::Add | GoBinaryOperator::Subtract | GoBinaryOperator::Multiply,
            left,
            right,
        } => is_repeatable_count(left) && is_repeatable_count(right),
        value => is_repeatable(value),
    }
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
    method: &str,
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
    (viewed == view && name == method && found != "_" && is_repeatable(index))
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
