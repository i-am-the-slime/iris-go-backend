use rustc_hash::FxHashMap;
use smol_str::{SmolStr, format_smolstr};

use super::Simplifier;
use crate::monomorphic::traversal::{for_each_child, for_each_child_mut};
use crate::monomorphic::{
    Binding, Expression, ExpressionKind, Function, FunctionId, FunctionSpelling, Local, LocalId,
    PatternKind,
};
use crate::monotype::{DataType, MonotypeId};
use crate::naming::capitalise;
use crate::purity::{is_within_size, size};

const CALL_PATTERN_COPIES: usize = 6;
const CALL_PATTERN_SIZE: usize = 600;

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
                let mut labels: Vec<(SmolStr, MonotypeId)> =
                    fields.iter().map(|(label, value)| (label.clone(), value.monotype)).collect();
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

    fn field_values(&self, argument: Expression) -> Vec<Expression> {
        match (self, argument.kind) {
            (Shape::Constructor { .. }, ExpressionKind::Construct { arguments, .. }) => arguments,
            (Shape::Record { labels }, ExpressionKind::Record(mut fields)) => labels
                .iter()
                .map(|(label, _)| {
                    let position = fields
                        .iter()
                        .position(|(given, _)| given == label)
                        .expect("invariant violated: a matched record has every label");
                    fields.swap_remove(position).1
                })
                .collect(),
            _ => unreachable!("invariant violated: only a matched argument is taken apart"),
        }
    }
}

struct CallPattern {
    position: usize,
    index: usize,
    shape: Shape,
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
        let mut made: Vec<(LocalId, usize, Shape, Local)> = vec![];
        for _ in 0..CALL_PATTERN_COPIES {
            let Some(pattern) = self.call_pattern(&bindings, &body, &made) else { break };
            let original = bindings[pattern.position].local.id;
            let copy = self.call_pattern_copy(&bindings[pattern.position], &pattern);
            made.push((original, pattern.index, pattern.shape, copy.local.clone()));
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
            mentions(body, local)
                || bindings
                    .iter()
                    .any(|binding| binding.local.id != local && mentions(&binding.value, local))
        };
        loop {
            let unused =
                bindings.iter().position(|binding| !mentioned(binding.local.id, &bindings, &body));
            let Some(unused) = unused else { break };
            bindings.remove(unused);
        }
        (bindings, body)
    }

    fn call_pattern(
        &self,
        bindings: &[Binding],
        body: &Expression,
        made: &[(LocalId, usize, Shape, Local)],
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
                if !taken_apart_only(lambda_body, parameter.id, Loop::Local(local), index) {
                    continue;
                }
                let shape = calls.iter().find_map(|arguments| {
                    let argument = &arguments[index];
                    let typed =
                        self.monotypes.same_without_causes(argument.monotype, parameter.monotype);
                    let shape = typed.then(|| Shape::of(argument)).flatten()?;
                    if parameters.len() == 1 && shape.is_empty() {
                        return None;
                    }
                    let done = made.iter().any(|(original, at, made, _)| {
                        *original == local && *at == index && *made == shape
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

    fn call_pattern_copy(&mut self, original: &Binding, pattern: &CallPattern) -> Binding {
        let mut value = original.value.clone();
        self.rename(&mut value, &mut FxHashMap::default());
        let ExpressionKind::Lambda { mut parameters, mut body } = value.kind else {
            unreachable!("invariant violated: only a local lambda takes call patterns")
        };
        let parameter = parameters.remove(pattern.index);
        let names = matched_names(&body, parameter.id, &pattern.shape);
        let (fields, built, suffix) = self.shape_fields(&pattern.shape, &parameter, names);
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
        Binding { local, value }
    }

    fn shape_fields(
        &mut self,
        shape: &Shape,
        parameter: &Local,
        names: Vec<Option<SmolStr>>,
    ) -> (Vec<Local>, Expression, SmolStr) {
        match shape {
            Shape::Constructor { data, constructor, fields } => {
                let locals: Vec<Local> = fields
                    .iter()
                    .enumerate()
                    .map(|(position, &monotype)| {
                        let name = names
                            .get(position)
                            .cloned()
                            .flatten()
                            .unwrap_or_else(|| self.monotypes.value_name(monotype));
                        self.fresh(&Local { id: LocalId(0), name, monotype })
                    })
                    .collect();
                let kind = ExpressionKind::Construct {
                    data: data.clone(),
                    constructor: *constructor,
                    arguments: locals.iter().map(Local::expression).collect(),
                };
                let name = self
                    .monotypes
                    .constructor_name(data, *constructor)
                    .unwrap_or_else(|| capitalise(&parameter.name).into());
                (locals, Expression::new(kind, parameter.monotype), name)
            }
            Shape::Record { labels } => {
                let locals: Vec<Local> = labels
                    .iter()
                    .map(|(label, monotype)| {
                        self.fresh(&Local {
                            id: LocalId(0),
                            name: label.clone(),
                            monotype: *monotype,
                        })
                    })
                    .collect();
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

/// Whether the parameter is matched or has its fields read, and is otherwise only passed on
/// to the loop again in its own place.
fn taken_apart_only(body: &Expression, parameter: LocalId, callee: Loop, index: usize) -> bool {
    fn walk(
        expression: &Expression,
        parameter: LocalId,
        callee: Loop,
        index: usize,
        taken_apart: &mut bool,
    ) -> bool {
        let is_parameter = |expression: &Expression| matches!(expression.kind, ExpressionKind::Local(id) if id == parameter);
        match &expression.kind {
            ExpressionKind::Local(id) => *id != parameter,
            ExpressionKind::Access { record, .. } if is_parameter(record) => {
                *taken_apart = true;
                true
            }
            ExpressionKind::Case { scrutinees, alternatives } => {
                let mut only = true;
                for scrutinee in scrutinees {
                    if is_parameter(scrutinee) {
                        *taken_apart = true;
                    } else {
                        only = only && walk(scrutinee, parameter, callee, index, taken_apart);
                    }
                }
                crate::monomorphic::traversal::for_each_alternative_child(
                    alternatives,
                    &mut |child| only = only && walk(child, parameter, callee, index, taken_apart),
                );
                only
            }
            ExpressionKind::Apply { function, arguments } if callee.is(function) => {
                arguments.iter().enumerate().all(|(position, argument)| {
                    (position == index && is_parameter(argument))
                        || walk(argument, parameter, callee, index, taken_apart)
                })
            }
            _ => {
                let mut only = true;
                for_each_child(expression, &mut |child| {
                    only = only && walk(child, parameter, callee, index, taken_apart)
                });
                only
            }
        }
    }
    let mut taken_apart = false;
    walk(body, parameter, callee, index, &mut taken_apart) && taken_apart
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
            let PatternKind::Constructor { constructor: matched, arguments, .. } =
                &alternative.patterns[column].kind
            else {
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

fn substitute_local(expression: &mut Expression, local: LocalId, value: &Expression) {
    if matches!(expression.kind, ExpressionKind::Local(id) if id == local) {
        *expression = value.clone().replacing(expression.position);
        return;
    }
    for_each_child_mut(expression, &mut |child| substitute_local(child, local, value));
}

/// Calls that build the value a copy was made for call the copy with the value's fields.
fn redirect_call_patterns(expression: &mut Expression, made: &[(LocalId, usize, Shape, Local)]) {
    for_each_child_mut(expression, &mut |child| redirect_call_patterns(child, made));
    let ExpressionKind::Apply { function, arguments } = &mut expression.kind else { return };
    loop {
        let ExpressionKind::Local(callee) = function.kind else { return };
        let copy = made.iter().find(|(original, index, shape, _)| {
            *original == callee
                && arguments.get(*index).is_some_and(|argument| shape.matches(argument))
        });
        let Some((_, index, shape, copy)) = copy else { return };
        let argument = arguments.remove(*index);
        for (offset, field) in shape.field_values(argument).into_iter().enumerate() {
            arguments.insert(index + offset, field);
        }
        **function = copy.expression().replacing(function.position);
    }
}

fn mentions(expression: &Expression, local: LocalId) -> bool {
    let mut mentioned = false;
    crate::monomorphic::traversal::visit(expression, &mut |node| {
        mentioned |= matches!(node.kind, ExpressionKind::Local(id) if id == local);
    });
    mentioned
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

/// The copies of top-level loops made for the values their calls build.
#[derive(Default)]
pub(super) struct CallPatternCopies {
    made: Vec<(FunctionId, usize, Shape, FunctionId, MonotypeId)>,
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
        let made = self.call_pattern_copies.made.iter().find(|(original, at, made, _, _)| {
            *original == callee && *at == index && *made == shape
        });
        let (copy, copy_monotype) = match made {
            Some((_, _, _, copy, copy_monotype)) => (*copy, *copy_monotype),
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
        for (offset, field) in shape.field_values(argument).into_iter().enumerate() {
            arguments.insert(index + offset, field);
        }
        let function = Expression::new(ExpressionKind::Function(copy), copy_monotype);
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
        if callee == self.entry || !self.recursive[callee.0 as usize] {
            return None;
        }
        let function = self.functions[callee.0 as usize].as_ref()?;
        if function.parameters.len() != arguments.len()
            || !is_within_size(&function.body, CALL_PATTERN_SIZE)
        {
            return None;
        }
        function.parameters.iter().zip(arguments).enumerate().find_map(
            |(index, (parameter, argument))| {
                let typed =
                    self.monotypes.same_without_causes(argument.monotype, parameter.monotype);
                let shape = typed.then(|| Shape::of(argument)).flatten()?;
                if function.parameters.len() == 1 && shape.is_empty() {
                    return None;
                }
                let loop_ = Loop::Function(callee);
                taken_apart_only(&function.body, parameter.id, loop_, index)
                    .then_some((index, shape))
            },
        )
    }

    fn top_level_copy(
        &mut self,
        callee: FunctionId,
        index: usize,
        shape: Shape,
    ) -> (FunctionId, MonotypeId) {
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
        let (fields, built, suffix) = self.shape_fields(&shape, &parameter, names);
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
        self.call_pattern_copies.made.push((callee, index, shape, copy, monotype));
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
        let function = self.simplified_copy(function);
        self.sizes[copy.0 as usize] = size(&function.body);
        self.functions[copy.0 as usize] = Some(function);
        (copy, monotype)
    }
}
