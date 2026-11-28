use rustc_hash::FxHashMap;
use smol_str::{SmolStr, format_smolstr};

use super::Simplifier;
use crate::monomorphic::traversal::{for_each_child, for_each_child_mut, mentions_local};
use crate::monomorphic::{
    Binding, Expression, ExpressionKind, Function, FunctionId, FunctionSpelling, Local, LocalId,
    PatternKind,
};
use crate::monotype::{DataType, Monotype, MonotypeId};
use crate::naming::capitalise;
use crate::purity::{is_within_size, size};

const CALL_PATTERN_COPIES: usize = 6;
const CALL_PATTERN_SIZE: usize = 600;
const REBUILT_USES: usize = 1;

#[derive(Clone, PartialEq)]
enum Shape {
    Constructor { data: DataType, constructor: usize, fields: Vec<MonotypeId> },
    Record { labels: Vec<(SmolStr, MonotypeId)> },
}

impl Shape {
    fn of(argument: &Expression) -> Option<Shape> {
        match &argument.kind {
            ExpressionKind::Construct { data, constructor, arguments } => {
                Some(Shape::Constructor {
                    data: data.clone(),
                    constructor: *constructor,
                    fields: arguments.iter().map(|argument| argument.monotype).collect(),
                })
            }
            ExpressionKind::Record(fields) if !fields.is_empty() => {
                let labels = fields.iter().map(|(label, value)| (label.clone(), value.monotype));
                let mut labels: Vec<(SmolStr, MonotypeId)> = labels.collect();
                labels.sort_by(|(left, _), (right, _)| left.cmp(right));
                Some(Shape::Record { labels })
            }
            _ => None,
        }
    }

    fn is_empty(&self) -> bool {
        match self {
            Shape::Constructor { fields, .. } => fields.is_empty(),
            Shape::Record { labels } => labels.is_empty(),
        }
    }

    fn matches(&self, argument: &Expression) -> bool {
        match (self, &argument.kind) {
            (
                Shape::Constructor { data, constructor, .. },
                ExpressionKind::Construct { data: given, constructor: chosen, .. },
            ) => data == given && constructor == chosen,
            (Shape::Record { labels }, ExpressionKind::Record(fields)) => {
                labels.len() == fields.len()
                    && labels
                        .iter()
                        .all(|(label, _)| fields.iter().any(|(given, _)| given == label))
            }
            _ => false,
        }
    }

    fn field_values(&self, argument: Expression, kept: &[bool]) -> Vec<Expression> {
        match (self, argument.kind) {
            (Shape::Constructor { .. }, ExpressionKind::Construct { arguments, .. }) => arguments
                .into_iter()
                .zip(kept)
                .filter_map(|(argument, &kept)| kept.then_some(argument))
                .collect(),
            (Shape::Record { labels }, ExpressionKind::Record(mut fields)) => {
                let values = labels.iter().map(|(label, _)| {
                    let position = fields
                        .iter()
                        .position(|(given, _)| given == label)
                        .expect("invariant violated: a matched record has every label");
                    fields.swap_remove(position).1
                });
                values.collect()
            }
            _ => unreachable!("invariant violated: only a matched argument is taken apart"),
        }
    }
}

struct CallPattern {
    position: usize,
    index: usize,
    shape: Shape,
}

/// A copy made for a loop's argument at `index` built with `shape`, which takes the fields
/// `kept` marks.
struct LocalCopy {
    original: LocalId,
    index: usize,
    shape: Shape,
    kept: Vec<bool>,
    copy: Local,
}

impl Simplifier<'_> {
    /// Local loops that pass a value they build to themselves, `go (Just (s + i)) (i + 1)` or
    /// `go { low, high } (i + 1)`, take its fields instead: a copy of the loop for the
    /// constructor or record sees the value its matches and reads look at, and the calls that
    /// build it pass the fields.
    pub(super) fn specialize_call_patterns(
        &mut self,
        mut bindings: Vec<Binding>,
        mut body: Expression,
    ) -> (Vec<Binding>, Expression) {
        let mut made: Vec<LocalCopy> = vec![];
        for _ in 0..CALL_PATTERN_COPIES {
            let Some(pattern) = self.call_pattern(&bindings, &body, &made) else { break };
            let original = bindings[pattern.position].local.id;
            let (copy, kept) = self.call_pattern_copy(&bindings[pattern.position], &pattern);
            made.push(LocalCopy {
                original,
                index: pattern.index,
                shape: pattern.shape,
                kept,
                copy: copy.local.clone(),
            });
            bindings.push(copy);
            for binding in &mut bindings {
                redirect_call_patterns(&mut binding.value, &made);
            }
            redirect_call_patterns(&mut body, &made);
        }
        if made.is_empty() {
            return (bindings, body);
        }
        let start = bindings.len() - made.len();
        for binding in &mut bindings[start..] {
            let value = std::mem::replace(
                &mut binding.value,
                Expression::new(ExpressionKind::Unit, body.monotype),
            );
            let fuel = std::mem::replace(&mut self.fuel, super::INLINE_FUEL);
            let mut value = self.expression(value);
            self.fuel = fuel;
            redirect_call_patterns(&mut value, &made);
            binding.value = value;
        }
        let mentioned = |local: LocalId, bindings: &[Binding], body: &Expression| {
            mentions_local(body, local)
                || bindings.iter().any(|binding| {
                    binding.local.id != local && mentions_local(&binding.value, local)
                })
        };
        loop {
            let unmentioned = |binding: &Binding| !mentioned(binding.local.id, &bindings, &body);
            let Some(unused) = bindings.iter().position(unmentioned) else { break };
            bindings.remove(unused);
        }
        (bindings, body)
    }

    fn call_pattern(
        &self,
        bindings: &[Binding],
        body: &Expression,
        made: &[LocalCopy],
    ) -> Option<CallPattern> {
        for (position, binding) in bindings.iter().enumerate() {
            let ExpressionKind::Lambda { parameters, body: lambda_body } = &binding.value.kind
            else {
                continue;
            };
            if !is_within_size(lambda_body, CALL_PATTERN_SIZE) {
                continue;
            }
            let local = binding.local.id;
            let mut calls = vec![];
            let only_called = bindings.iter().all(|binding| {
                saturated_calls(&binding.value, local, parameters.len(), &mut calls)
            }) && saturated_calls(body, local, parameters.len(), &mut calls);
            if !only_called || calls.is_empty() {
                continue;
            }
            for (index, parameter) in parameters.iter().enumerate() {
                if !worth_copying(lambda_body, parameter.id, Loop::Local(local), index) {
                    continue;
                }
                let monotype = parameter.monotype;
                let shape = calls.iter().find_map(|arguments| {
                    let argument = &arguments[index];
                    let typed = self.monotypes.same_without_causes(argument.monotype, monotype);
                    let shape = typed.then(|| Shape::of(argument)).flatten()?;
                    if parameters.len() == 1 && shape.is_empty() {
                        return None;
                    }
                    let done = made.iter().any(|made| {
                        made.original == local && made.index == index && made.shape == shape
                    });
                    (!done).then_some(shape)
                });
                if let Some(shape) = shape {
                    return Some(CallPattern { position, index, shape });
                }
            }
        }
        None
    }

    fn call_pattern_copy(
        &mut self,
        original: &Binding,
        pattern: &CallPattern,
    ) -> (Binding, Vec<bool>) {
        let mut value = original.value.clone();
        self.rename(&mut value, &mut FxHashMap::default());
        let ExpressionKind::Lambda { mut parameters, mut body } = value.kind else {
            unreachable!("invariant violated: only a local lambda takes call patterns")
        };
        let parameter = parameters.remove(pattern.index);
        let names = matched_names(&body, parameter.id, &pattern.shape);
        let callee = Loop::Local(original.local.id);
        let whole = whole_uses(&body, parameter.id, callee, pattern.index);
        let kept = self.kept_fields(&body, parameter.id, &pattern.shape, parameters.len(), whole);
        let (fields, built, suffix) = self.shape_fields(&pattern.shape, &parameter, names, &kept);
        substitute_local(&mut body, parameter.id, &built);
        for (offset, field) in fields.into_iter().enumerate() {
            parameters.insert(pattern.index + offset, field);
        }
        let monotype = parameters.iter().rev().fold(body.monotype, |result, parameter| {
            self.monotypes.function(parameter.monotype, result)
        });
        let name = format_smolstr!("{}{}", original.local.name, suffix);
        let local = self.fresh(&Local { id: LocalId(0), name, monotype });
        let value = Expression::new(ExpressionKind::Lambda { parameters, body }, monotype)
            .replacing(original.value.position);
        (Binding { local, value }, kept)
    }

    /// The constructor's fields a copy takes: every field but an erased one the loop's matches
    /// never bind, which the copy would only pass around as `any`, and every field when the copy
    /// rebuilds the value.
    fn kept_fields(
        &self,
        body: &Expression,
        parameter: LocalId,
        shape: &Shape,
        other_parameters: usize,
        whole_uses: Option<usize>,
    ) -> Vec<bool> {
        let Shape::Constructor { fields, .. } = shape else { return vec![] };
        if whole_uses.is_some_and(|whole| whole > 0) {
            return vec![true; fields.len()];
        }
        let bound = bound_fields(body, parameter, shape);
        let kept: Vec<bool> = fields
            .iter()
            .zip(bound)
            .map(|(&monotype, bound)| bound || !self.is_erased(monotype))
            .collect();
        let takes_nothing = other_parameters == 0 && !kept.contains(&true);
        if takes_nothing { vec![true; fields.len()] } else { kept }
    }

    fn is_erased(&self, monotype: MonotypeId) -> bool {
        matches!(self.monotypes.get(monotype), Monotype::Erased(_))
    }

    fn shape_fields(
        &mut self,
        shape: &Shape,
        parameter: &Local,
        names: Vec<Option<SmolStr>>,
        kept: &[bool],
    ) -> (Vec<Local>, Expression, SmolStr) {
        match shape {
            Shape::Constructor { data, constructor, fields } => {
                let mut locals: Vec<Local> = vec![];
                let mut arguments: Vec<Expression> = vec![];
                for (position, &monotype) in fields.iter().enumerate() {
                    if !kept[position] {
                        arguments.push(Expression::new(ExpressionKind::Unit, monotype));
                        continue;
                    }
                    let name = names
                        .get(position)
                        .cloned()
                        .flatten()
                        .unwrap_or_else(|| self.monotypes.value_name(monotype));
                    let local = self.fresh(&Local { id: LocalId(0), name, monotype });
                    arguments.push(local.expression());
                    locals.push(local);
                }
                let kind = ExpressionKind::Construct {
                    data: data.clone(),
                    constructor: *constructor,
                    arguments,
                };
                let name = self
                    .monotypes
                    .constructor_name(data, *constructor)
                    .unwrap_or_else(|| capitalise(&parameter.name).into());
                (locals, Expression::new(kind, parameter.monotype), name)
            }
            Shape::Record { labels } => {
                let locals = labels.iter().map(|(label, monotype)| {
                    self.fresh(&Local { id: LocalId(0), name: label.clone(), monotype: *monotype })
                });
                let locals: Vec<Local> = locals.collect();
                let fields = labels
                    .iter()
                    .zip(&locals)
                    .map(|((label, _), local)| (label.clone(), local.expression()))
                    .collect();
                let built = Expression::new(ExpressionKind::Record(fields), parameter.monotype);
                (locals, built, capitalise(&parameter.name).into())
            }
        }
    }
}

/// Collects the arguments of every call of `local`, or says false when `local` is used in
/// another way or given another number of arguments.
fn saturated_calls(
    expression: &Expression,
    local: LocalId,
    arity: usize,
    calls: &mut Vec<Vec<Expression>>,
) -> bool {
    match &expression.kind {
        ExpressionKind::Local(id) => *id != local,
        ExpressionKind::Apply { function, arguments } if matches!(function.kind, ExpressionKind::Local(id) if id == local) =>
        {
            if arguments.len() != arity {
                return false;
            }
            calls.push(arguments.clone());
            arguments.iter().all(|argument| saturated_calls(argument, local, arity, calls))
        }
        _ => {
            let mut only_called = true;
            for_each_child(expression, &mut |child| {
                only_called = only_called && saturated_calls(child, local, arity, calls)
            });
            only_called
        }
    }
}

/// How often the loop uses the parameter whole, when it matches it or reads its fields: a use
/// that passes it on to the loop again in its own place is not counted, and a copy rebuilds it
/// for the others.
fn whole_uses(body: &Expression, parameter: LocalId, callee: Loop, index: usize) -> Option<usize> {
    fn walk(
        expression: &Expression,
        parameter: LocalId,
        callee: Loop,
        index: usize,
        taken_apart: &mut bool,
        whole: &mut usize,
    ) {
        let is_parameter = |expression: &Expression| matches!(expression.kind, ExpressionKind::Local(id) if id == parameter);
        match &expression.kind {
            ExpressionKind::Local(id) if *id == parameter => *whole += 1,
            ExpressionKind::Access { record, .. } if is_parameter(record) => *taken_apart = true,
            ExpressionKind::Case { scrutinees, alternatives } => {
                for scrutinee in scrutinees {
                    if is_parameter(scrutinee) {
                        *taken_apart = true;
                    } else {
                        walk(scrutinee, parameter, callee, index, taken_apart, whole);
                    }
                }
                crate::monomorphic::traversal::for_each_alternative_child(
                    alternatives,
                    &mut |child| walk(child, parameter, callee, index, taken_apart, whole),
                );
            }
            ExpressionKind::Apply { function, arguments } if callee.is(function) => {
                for (position, argument) in arguments.iter().enumerate() {
                    if position != index || !is_parameter(argument) {
                        walk(argument, parameter, callee, index, taken_apart, whole);
                    }
                }
            }
            _ => for_each_child(expression, &mut |child| {
                walk(child, parameter, callee, index, taken_apart, whole)
            }),
        }
    }
    let mut taken_apart = false;
    let mut whole = 0;
    walk(body, parameter, callee, index, &mut taken_apart, &mut whole);
    taken_apart.then_some(whole)
}

/// Whether a copy for the parameter pays: the loop takes it apart, and rebuilds it for at most
/// one other use.
fn worth_copying(body: &Expression, parameter: LocalId, callee: Loop, index: usize) -> bool {
    whole_uses(body, parameter, callee, index).is_some_and(|whole| whole <= REBUILT_USES)
}

/// The names the loop's own match gives the constructor's fields.
fn matched_names(body: &Expression, parameter: LocalId, shape: &Shape) -> Vec<Option<SmolStr>> {
    let Shape::Constructor { constructor, fields, .. } = shape else { return vec![] };
    let mut names = vec![None; fields.len()];
    crate::monomorphic::traversal::visit(body, &mut |node| {
        let ExpressionKind::Case { scrutinees, alternatives } = &node.kind else { return };
        let Some(column) = scrutinees.iter().position(
            |scrutinee| matches!(scrutinee.kind, ExpressionKind::Local(id) if id == parameter),
        ) else {
            return;
        };
        for alternative in alternatives {
            let kind = &alternative.patterns[column].kind;
            let PatternKind::Constructor { constructor: matched, arguments, .. } = kind else {
                continue;
            };
            if matched != constructor {
                continue;
            }
            for (name, argument) in names.iter_mut().zip(arguments) {
                if let (None, PatternKind::Variable(local)) = (&name, &argument.kind) {
                    *name = Some(local.name.clone());
                }
            }
        }
    });
    names
}

/// Which of the constructor's fields a match of the parameter binds or looks into; a match that
/// binds the whole value binds every field.
fn bound_fields(body: &Expression, parameter: LocalId, shape: &Shape) -> Vec<bool> {
    let Shape::Constructor { constructor, fields, .. } = shape else { return vec![] };
    let mut bound = vec![false; fields.len()];
    crate::monomorphic::traversal::visit(body, &mut |node| {
        let ExpressionKind::Case { scrutinees, alternatives } = &node.kind else { return };
        for (column, scrutinee) in scrutinees.iter().enumerate() {
            if !matches!(scrutinee.kind, ExpressionKind::Local(id) if id == parameter) {
                continue;
            }
            for alternative in alternatives {
                match &alternative.patterns[column].kind {
                    PatternKind::Wildcard => {}
                    PatternKind::Constructor { constructor: matched, .. }
                        if matched != constructor => {}
                    PatternKind::Constructor { arguments, .. } => {
                        for (bound, argument) in bound.iter_mut().zip(arguments) {
                            *bound |= !matches!(argument.kind, PatternKind::Wildcard);
                        }
                    }
                    _ => bound.iter_mut().for_each(|bound| *bound = true),
                }
            }
        }
    });
    bound
}

fn substitute_local(expression: &mut Expression, local: LocalId, value: &Expression) {
    if matches!(expression.kind, ExpressionKind::Local(id) if id == local) {
        *expression = value.clone().replacing(expression.position);
        return;
    }
    for_each_child_mut(expression, &mut |child| substitute_local(child, local, value));
}

/// Calls that build the value a copy was made for call the copy with the value's fields.
fn redirect_call_patterns(expression: &mut Expression, made: &[LocalCopy]) {
    for_each_child_mut(expression, &mut |child| redirect_call_patterns(child, made));
    let ExpressionKind::Apply { function, arguments } = &mut expression.kind else { return };
    loop {
        let ExpressionKind::Local(callee) = function.kind else { return };
        let copy = made.iter().find(|made| {
            made.original == callee
                && arguments.get(made.index).is_some_and(|argument| made.shape.matches(argument))
        });
        let Some(LocalCopy { index, shape, kept, copy, .. }) = copy else { return };
        let argument = arguments.remove(*index);
        for (offset, field) in shape.field_values(argument, kept).into_iter().enumerate() {
            arguments.insert(index + offset, field);
        }
        **function = copy.expression().replacing(function.position);
    }
}

#[derive(Clone, Copy)]
enum Loop {
    Local(LocalId),
    Function(FunctionId),
}

impl Loop {
    fn is(self, expression: &Expression) -> bool {
        match (self, &expression.kind) {
            (Loop::Local(local), ExpressionKind::Local(id)) => *id == local,
            (Loop::Function(function), ExpressionKind::Function(id)) => *id == function,
            _ => false,
        }
    }
}

/// A copy made for a top-level loop's argument at `index` built with `shape`, which takes the
/// fields `kept` marks.
#[derive(Clone)]
struct TopLevelCopy {
    original: FunctionId,
    index: usize,
    shape: Shape,
    kept: Vec<bool>,
    copy: FunctionId,
    monotype: MonotypeId,
}

/// The copies of top-level loops made for the values their calls build.
#[derive(Default)]
pub(super) struct CallPatternCopies {
    made: Vec<TopLevelCopy>,
    counts: FxHashMap<FunctionId, usize>,
}

impl Simplifier<'_> {
    /// A call of a recursive top-level function that builds the value it matches calls the copy
    /// of the function that takes the value's fields, as a local loop's calls do.
    pub(super) fn call_pattern_call(
        &mut self,
        callee: FunctionId,
        arguments: Vec<Expression>,
        monotype: MonotypeId,
    ) -> Result<Expression, Vec<Expression>> {
        let Some((index, shape)) = self.top_level_call_pattern(callee, &arguments) else {
            return Err(arguments);
        };
        let made = self
            .call_pattern_copies
            .made
            .iter()
            .find(|made| made.original == callee && made.index == index && made.shape == shape);
        let made = match made {
            Some(made) => made.clone(),
            None => {
                let count = self.call_pattern_copies.counts.entry(callee).or_default();
                if *count >= CALL_PATTERN_COPIES {
                    return Err(arguments);
                }
                *count += 1;
                self.top_level_copy(callee, index, shape.clone())
            }
        };
        let mut arguments = arguments;
        let argument = arguments.remove(index);
        for (offset, field) in shape.field_values(argument, &made.kept).into_iter().enumerate() {
            arguments.insert(index + offset, field);
        }
        let function = Expression::new(ExpressionKind::Function(made.copy), made.monotype);
        if arguments.is_empty() {
            return Ok(function);
        }
        let kind = ExpressionKind::Apply { function: Box::new(function), arguments };
        Ok(Expression::new(kind, monotype))
    }

    fn top_level_call_pattern(
        &self,
        callee: FunctionId,
        arguments: &[Expression],
    ) -> Option<(usize, Shape)> {
        if callee == self.entry || !self.recursive[callee.0 as usize] || self.keeps_calls(callee) {
            return None;
        }
        let function = self.functions[callee.0 as usize].as_ref()?;
        if function.parameters.len() != arguments.len()
            || !is_within_size(&function.body, CALL_PATTERN_SIZE)
        {
            return None;
        }
        let mut parameters = function.parameters.iter().zip(arguments).enumerate();
        parameters.find_map(|(index, (parameter, argument))| {
            let typed = self.monotypes.same_without_causes(argument.monotype, parameter.monotype);
            let shape = typed.then(|| Shape::of(argument)).flatten()?;
            if function.parameters.len() == 1 && shape.is_empty() {
                return None;
            }
            let loop_ = Loop::Function(callee);
            worth_copying(&function.body, parameter.id, loop_, index).then_some((index, shape))
        })
    }

    fn top_level_copy(&mut self, callee: FunctionId, index: usize, shape: Shape) -> TopLevelCopy {
        let original = self.functions[callee.0 as usize]
            .clone()
            .expect("invariant violated: a loop with call patterns is known");
        let mut renaming = FxHashMap::default();
        let mut parameters: Vec<Local> = original
            .parameters
            .iter()
            .map(|parameter| self.rename_binder(parameter, &mut renaming))
            .collect();
        let mut body = original.body;
        self.rename(&mut body, &mut renaming);
        let parameter = parameters.remove(index);
        let names = matched_names(&body, parameter.id, &shape);
        let whole = whole_uses(&body, parameter.id, Loop::Function(callee), index);
        let kept = self.kept_fields(&body, parameter.id, &shape, parameters.len(), whole);
        let (fields, built, suffix) = self.shape_fields(&shape, &parameter, names, &kept);
        substitute_local(&mut body, parameter.id, &built);
        for (offset, field) in fields.into_iter().enumerate() {
            parameters.insert(index + offset, field);
        }
        let monotype = parameters.iter().rev().fold(original.result, |result, parameter| {
            self.monotypes.function(parameter.monotype, result)
        });
        let name = format_smolstr!("{}{}", original.name, suffix);
        let spelling = FunctionSpelling::Lifted { parent: original.name.clone(), local: suffix };
        self.monotypes.function_spellings.entry(name.clone()).or_insert(spelling);
        let copy = FunctionId(self.functions.len() as u32);
        let made = TopLevelCopy { original: callee, index, shape, kept, copy, monotype };
        self.call_pattern_copies.made.push(made.clone());
        let function = Function {
            name,
            origin: original.origin,
            parameters,
            result: original.result,
            body,
            position: original.position,
        };
        self.functions.push(None);
        self.sizes.push(size(&function.body));
        self.recursive.push(true);
        self.uses.push(self.uses[callee.0 as usize]);
        self.suspension.copy(callee);
        let mut function = self.simplified_copy(function);
        let made = self.leave_out_unread_fields(&mut function, made, index);
        self.sizes[copy.0 as usize] = size(&function.body);
        self.functions[copy.0 as usize] = Some(function);
        made
    }

    /// The copy without the fields its simplified body never reads, such as one that only
    /// rebuilt the value for a call that now passes the other fields to another copy. Calls of the
    /// copy that its own body makes leave them out too; one any other function makes keeps them.
    fn leave_out_unread_fields(
        &mut self,
        function: &mut Function,
        made: TopLevelCopy,
        index: usize,
    ) -> TopLevelCopy {
        let mut made = made;
        if !matches!(made.shape, Shape::Constructor { .. }) {
            return made;
        }
        let taken = made.kept.iter().filter(|&&kept| kept).count();
        let unread: Vec<usize> = (index..index + taken)
            .filter(|&position| !mentions_local(&function.body, function.parameters[position].id))
            .collect();
        let called_elsewhere = self.functions.iter().flatten().any(|other| {
            let mut called = false;
            crate::monomorphic::traversal::visit(&other.body, &mut |node| {
                called |= matches!(node.kind, ExpressionKind::Function(id) if id == made.copy);
            });
            called
        });
        if unread.is_empty() || called_elsewhere || unread.len() == function.parameters.len() {
            return made;
        }
        leave_out_arguments(&mut function.body, made.copy, &unread);
        for &position in unread.iter().rev() {
            function.parameters.remove(position);
        }
        for (field, kept) in (index..).zip(made.kept.iter_mut().filter(|kept| **kept)) {
            *kept = !unread.contains(&field);
        }
        let parameters = function.parameters.iter().rev();
        made.monotype = parameters.fold(function.result, |result, parameter| {
            self.monotypes.function(parameter.monotype, result)
        });
        let entry = self
            .call_pattern_copies
            .made
            .iter_mut()
            .find(|entry| entry.copy == made.copy)
            .expect("invariant violated: a copy is recorded when it is made");
        *entry = made.clone();
        made
    }
}

fn leave_out_arguments(expression: &mut Expression, function: FunctionId, positions: &[usize]) {
    for_each_child_mut(expression, &mut |child| leave_out_arguments(child, function, positions));
    let ExpressionKind::Apply { function: callee, arguments } = &mut expression.kind else {
        return;
    };
    if !matches!(callee.kind, ExpressionKind::Function(id) if id == function) {
        return;
    }
    for &position in positions.iter().rev() {
        arguments.remove(position);
    }
}
