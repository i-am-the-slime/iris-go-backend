//! Inlining and local rewrites over the monomorphic tree. Specialization leaves
//! long chains of tiny functions behind (class members delegating to other
//! members and foreign imports); inlining them exposes the effect primitives and
//! operators that code generation turns into plain Go.

use rustc_hash::{FxHashMap, FxHashSet};

use crate::foreign::{Comparison, Foreign, Operator};
use crate::mono::{
    Alternative, Binding, Expression, ExpressionKind, Function, FunctionId, Guard, Guarded,
    GuardedBranch, Literal, Local, LocalId, PATTERN_MATCH_FAILURE, Pattern, PatternKind, Program,
    RecordUpdate,
};
use crate::monotype::{Monotype, MonotypeId, Monotypes};
use crate::timing::timed;
use smol_str::SmolStr;

mod choice;
mod fold;
mod object;
mod record;
mod unpack;

const INLINE_SIZE: usize = 40;
const INLINE_FUEL: usize = 2_000;

pub fn simplify(program: Program, monotypes: &mut Monotypes, next_local: u32) -> Program {
    let Program { functions, entry } = program;
    let references: Vec<FxHashSet<FunctionId>> =
        functions.iter().map(|function| function_references(&function.body)).collect();
    let components = strongly_connected_components(&references);
    let mut recursive = vec![false; functions.len()];
    for component in &components {
        let is_recursive =
            component.len() > 1 || references[component[0].0 as usize].contains(&component[0]);
        for function in component {
            recursive[function.0 as usize] = is_recursive;
        }
    }

    let mut uses = vec![0usize; functions.len()];
    for function in &functions {
        visit(&function.body, &mut |node| {
            if let ExpressionKind::Function(id) = node.kind {
                uses[id.0 as usize] += 1;
            }
        });
    }
    let mut simplifier = Simplifier {
        sizes: functions.iter().map(|function| size(&function.body)).collect(),
        functions: functions.iter().cloned().map(Some).collect(),
        recursive,
        uses,
        entry,
        next_local,
        fuel: 0,
        monotypes,
        record_orders: FxHashMap::default(),
        records_settled: false,
    };
    for component in &components {
        for &function in component {
            let mut current = simplifier.functions[function.0 as usize]
                .take()
                .expect("invariant violated: function simplified twice");
            simplifier.fuel = INLINE_FUEL;
            current = simplifier.eta_expand(current);
            current.body = simplifier.expression(current.body);
            current = simplifier.absorb_lambdas(current);
            simplifier.sizes[function.0 as usize] = size(&current.body);
            simplifier.functions[function.0 as usize] = Some(current);
        }
    }
    simplifier.records_settled = true;
    simplifier.fuel = 0;
    for index in 0..simplifier.functions.len() {
        let mut current = simplifier.functions[index]
            .take()
            .expect("invariant violated: function lost during simplification");
        simplifier.settle_records(&mut current.body);
        simplifier.sizes[index] = size(&current.body);
        simplifier.functions[index] = Some(current);
    }
    let functions: Vec<Function> = simplifier
        .functions
        .into_iter()
        .map(|function| function.expect("invariant violated: function lost during simplification"))
        .collect();
    let next_local = simplifier.next_local;
    let program = Program { functions, entry };
    let program =
        timed("lift", || crate::lift::lift_local_functions(program, monotypes, next_local));
    timed("prune", || prune(program.functions, entry))
}

struct Simplifier<'m> {
    functions: Vec<Option<Function>>,
    /// The size of each function's body as it stands in `functions`.
    sizes: Vec<usize>,
    recursive: Vec<bool>,
    uses: Vec<usize>,
    entry: FunctionId,
    next_local: u32,
    fuel: usize,
    monotypes: &'m mut Monotypes,
    record_orders: FxHashMap<LocalId, Vec<SmolStr>>,
    records_settled: bool,
}

impl Simplifier<'_> {
    fn fresh(&mut self, local: &Local) -> Local {
        let id = LocalId(self.next_local);
        self.next_local += 1;
        Local { id, name: local.name.clone(), monotype: local.monotype }
    }

    fn inlinable(&self, id: FunctionId) -> Option<&Function> {
        if id == self.entry || self.recursive[id.0 as usize] {
            return None;
        }
        let function = self.functions[id.0 as usize].as_ref()?;
        let once = self.uses[id.0 as usize] == 1;
        // A copy of a failure saves no work, only adds another place to fail.
        let small = self.sizes[id.0 as usize] <= INLINE_SIZE && !can_fail(&function.body);
        ((small || once) && !function.parameters.is_empty() || is_trivial(&function.body))
            .then_some(function)
    }

    /// A point-free definition such as `void = map (const unit)` becomes a function
    /// of its arguments; partially applying a known function does no work to share.
    fn eta_expand(&mut self, mut function: Function) -> Function {
        if !function.parameters.is_empty()
            || self.monotypes.function_parts(function.result).is_none()
        {
            return function;
        }
        let partial = match &function.body.kind {
            ExpressionKind::Function(_) => true,
            ExpressionKind::Apply { function: callee, arguments } => match callee.kind {
                ExpressionKind::Function(id) => {
                    arguments.iter().all(|argument| self.does_no_work(argument))
                        && self.functions[id.0 as usize]
                            .as_ref()
                            .is_some_and(|callee| callee.parameters.len() > arguments.len())
                }
                _ => false,
            },
            _ => false,
        };
        if !partial {
            return function;
        }
        let mut parameters = vec![];
        let mut result = function.result;
        while let Some((argument, inner)) = self.monotypes.function_parts(result) {
            let template = Local { id: LocalId(0), name: "argument".into(), monotype: argument };
            parameters.push(self.fresh(&template));
            result = inner;
        }
        let arguments = parameters
            .iter()
            .map(|parameter| {
                Expression::new(ExpressionKind::Local(parameter.id), parameter.monotype)
            })
            .collect();
        function.body = Expression::new(
            ExpressionKind::Apply { function: Box::new(function.body), arguments },
            result,
        );
        function.parameters = parameters;
        function.result = result;
        function
    }

    fn does_no_work(&self, expression: &Expression) -> bool {
        does_no_work(self, expression)
    }

    /// A function whose body is a lambda keeps its parameters as Go parameters,
    /// and so does one whose body only chooses between lambdas: the choice is
    /// too cheap to share between applications of the chosen lambda.
    fn absorb_lambdas(&mut self, mut function: Function) -> Function {
        loop {
            if let ExpressionKind::Lambda { .. } = function.body.kind {
                let ExpressionKind::Lambda { parameters, body } = function.body.kind else {
                    unreachable!()
                };
                function.parameters.extend(parameters);
                function.body = *body;
            } else if !function.parameters.is_empty()
                && let Some(template) = chosen_lambda_parameter(&function.body).cloned()
            {
                let parameter = self.fresh(&template);
                let body = std::mem::replace(
                    &mut function.body,
                    Expression::new(ExpressionKind::Unit, parameter.monotype),
                );
                function.body = self.apply_chosen_lambdas(body, &parameter);
                function.parameters.push(parameter);
            } else {
                break;
            }
        }
        function.result = function.body.monotype;
        function
    }

    /// Applies each lambda that `chosen_lambda_parameter` accepted to the
    /// parameter that replaces their first ones.
    fn apply_chosen_lambdas(&mut self, expression: Expression, parameter: &Local) -> Expression {
        let monotype = self.monotypes.result_after(expression.monotype, 1);
        self.map_choices(expression, monotype, &mut |_, chosen| {
            let ExpressionKind::Lambda { mut parameters, body } = chosen.kind else {
                unreachable!("invariant violated: only chosen lambdas take the parameter")
            };
            let first = parameters.remove(0);
            let body = substitute(*body, first.id, &local_expression(parameter));
            if parameters.is_empty() {
                return body;
            }
            Expression::new(ExpressionKind::Lambda { parameters, body: Box::new(body) }, monotype)
        })
    }

    /// Rewrites what a choice evaluates to, through the lets, ifs and cases
    /// that choose it, into expressions of `monotype`.
    fn map_choices(
        &mut self,
        expression: Expression,
        monotype: MonotypeId,
        chosen: &mut impl FnMut(&mut Self, Expression) -> Expression,
    ) -> Expression {
        let kind = match expression.kind {
            ExpressionKind::Let { bindings, body } => {
                let body = self.map_choices(*body, monotype, chosen);
                ExpressionKind::Let { bindings, body: Box::new(body) }
            }
            ExpressionKind::If { condition, then, otherwise } => ExpressionKind::If {
                condition,
                then: Box::new(self.map_choices(*then, monotype, chosen)),
                otherwise: Box::new(self.map_choices(*otherwise, monotype, chosen)),
            },
            ExpressionKind::Case { scrutinees, alternatives } => {
                let alternatives = alternatives
                    .into_iter()
                    .map(|alternative| {
                        let body = match alternative.body {
                            Guarded::Unconditional(body) => {
                                Guarded::Unconditional(self.map_choices(body, monotype, chosen))
                            }
                            Guarded::Guards(branches) => Guarded::Guards(
                                branches
                                    .into_iter()
                                    .map(|branch| GuardedBranch {
                                        guards: branch.guards,
                                        body: self.map_choices(branch.body, monotype, chosen),
                                    })
                                    .collect(),
                            ),
                        };
                        Alternative { patterns: alternative.patterns, body }
                    })
                    .collect();
                ExpressionKind::Case { scrutinees, alternatives }
            }
            ExpressionKind::Fail(message) => ExpressionKind::Fail(message),
            kind => return chosen(self, Expression::new(kind, expression.monotype)),
        };
        Expression::new(kind, monotype)
    }

    /// `(case x of A -> f; B -> g) a` is `case x of A -> f a; B -> g a`, with
    /// `a` evaluated once, before the choice.
    fn apply_choice(
        &mut self,
        choice: Expression,
        arguments: Vec<Expression>,
        monotype: MonotypeId,
    ) -> Expression {
        let mut bindings = vec![];
        let arguments: Vec<Expression> = arguments
            .into_iter()
            .map(|argument| {
                if is_trivial(&argument) {
                    return argument;
                }
                let template =
                    Local { id: LocalId(0), name: "argument".into(), monotype: argument.monotype };
                let local = self.fresh(&template);
                let reference = local_expression(&local);
                bindings.push(Binding { local, value: argument });
                reference
            })
            .collect();
        let applied = self.map_choices(choice, monotype, &mut |simplifier, chosen| {
            simplifier.apply(chosen, arguments.clone(), monotype)
        });
        if bindings.is_empty() {
            return applied;
        }
        Expression::new(ExpressionKind::Let { bindings, body: Box::new(applied) }, monotype)
    }

    fn expression(&mut self, expression: Expression) -> Expression {
        let monotype = expression.monotype;
        let kind = match expression.kind {
            ExpressionKind::Literal(_)
            | ExpressionKind::Unit
            | ExpressionKind::Local(_)
            | ExpressionKind::Fail(_) => expression.kind,
            ExpressionKind::Function(id) => {
                if let Some(function) = self.inlinable(id)
                    && function.parameters.is_empty()
                    && is_trivial(&function.body)
                {
                    let body = function.body.clone();
                    let body = self.rename(body, &mut FxHashMap::default());
                    return self.expression(body);
                }
                ExpressionKind::Function(id)
            }
            ExpressionKind::Array(elements) => ExpressionKind::Array(
                elements.into_iter().map(|element| self.expression(element)).collect(),
            ),
            ExpressionKind::Record(fields) => ExpressionKind::Record(
                fields.into_iter().map(|(label, value)| (label, self.expression(value))).collect(),
            ),
            ExpressionKind::Access { record, label } => {
                let record = self.expression(*record);
                return project(record, label, monotype);
            }
            ExpressionKind::Update { record, updates } => ExpressionKind::Update {
                record: Box::new(self.expression(*record)),
                updates: self.updates(updates),
            },
            ExpressionKind::Construct { data, constructor, arguments } => {
                ExpressionKind::Construct {
                    data,
                    constructor,
                    arguments: arguments
                        .into_iter()
                        .map(|argument| self.expression(argument))
                        .collect(),
                }
            }
            ExpressionKind::Foreign { foreign, arguments } => {
                let arguments: Vec<Expression> =
                    arguments.into_iter().map(|argument| self.expression(argument)).collect();
                return self.foreign(foreign, arguments, monotype);
            }
            ExpressionKind::Reuse { .. } => {
                unreachable!("invariant violated: cells are reused only after simplification")
            }
            ExpressionKind::Apply { function, arguments } => {
                let function = self.expression(*function);
                let arguments: Vec<Expression> =
                    arguments.into_iter().map(|argument| self.expression(argument)).collect();
                return self.apply(function, arguments, monotype);
            }
            ExpressionKind::Lambda { parameters, body } => {
                ExpressionKind::Lambda { parameters, body: Box::new(self.expression(*body)) }
            }
            ExpressionKind::Coerce(value) => {
                let mut value = self.expression(*value);
                if let ExpressionKind::Coerce(inner) = value.kind {
                    value = *inner;
                }
                return self.coerce(value, monotype);
            }
            ExpressionKind::Let { bindings, body } => {
                let bindings: Vec<Binding> = bindings
                    .into_iter()
                    .map(|binding| Binding {
                        local: binding.local,
                        value: self.expression(binding.value),
                    })
                    .collect();
                for binding in &bindings {
                    self.remember_record_order(binding);
                }
                let body = self.expression(*body);
                return self.let_bindings(bindings, body);
            }
            ExpressionKind::If { condition, then, otherwise } => {
                let condition = self.expression(*condition);
                if let ExpressionKind::Literal(Literal::Boolean(value)) = condition.kind {
                    return self.expression(if value { *then } else { *otherwise });
                }
                let then = self.expression(*then);
                let otherwise = self.expression(*otherwise);
                return self.boolean_choice(condition, then, otherwise, monotype);
            }
            ExpressionKind::Case { scrutinees, alternatives } if binds_only(&alternatives) => {
                let alternative =
                    alternatives.into_iter().next().expect("invariant violated: binds_only");
                let Guarded::Unconditional(body) = alternative.body else { unreachable!() };
                let bindings = alternative
                    .patterns
                    .into_iter()
                    .zip(scrutinees)
                    .filter_map(|(pattern, value)| match pattern.kind {
                        // A newtype pattern may bind the wrapped representation of a
                        // recursive newtype, which the binding keeps.
                        PatternKind::Variable(local) if local.monotype != value.monotype => {
                            let monotype = local.monotype;
                            let value =
                                Expression::new(ExpressionKind::Coerce(Box::new(value)), monotype);
                            Some(Binding { local, value })
                        }
                        PatternKind::Variable(local) => Some(Binding { local, value }),
                        _ => None,
                    })
                    .collect();
                let body = Expression::new(
                    ExpressionKind::Let { bindings, body: Box::new(body) },
                    monotype,
                );
                return self.expression(body);
            }
            ExpressionKind::Case { scrutinees, alternatives } => {
                let scrutinees: Vec<Expression> =
                    scrutinees.into_iter().map(|scrutinee| self.expression(scrutinee)).collect();
                let mut scrutinees = scrutinees;
                if let [scrutinee] = scrutinees.as_mut_slice()
                    && let Some(distributed) = self.distribute(scrutinee, &alternatives, monotype)
                {
                    return distributed;
                }
                let (bindings, scrutinees, alternatives) =
                    self.eliminate_columns(scrutinees, alternatives);
                let alternatives: Vec<Alternative> = alternatives
                    .into_iter()
                    .map(|alternative| Alternative {
                        patterns: alternative.patterns,
                        body: self.guarded(alternative.body),
                    })
                    .collect();
                let case = match alternatives.first() {
                    None => Expression::new(
                        ExpressionKind::Fail(SmolStr::new_static(PATTERN_MATCH_FAILURE)),
                        monotype,
                    ),
                    Some(Alternative { body: Guarded::Unconditional(_), .. })
                        if scrutinees.is_empty() =>
                    {
                        let Some(Alternative { body: Guarded::Unconditional(body), .. }) =
                            alternatives.into_iter().next()
                        else {
                            unreachable!()
                        };
                        body
                    }
                    Some(_) => {
                        Expression::new(ExpressionKind::Case { scrutinees, alternatives }, monotype)
                    }
                };
                return self.let_bindings(bindings, case);
            }
            ExpressionKind::EffectPure(value) => {
                ExpressionKind::EffectPure(Box::new(self.expression(*value)))
            }
            ExpressionKind::EffectBind { action, local, body } => {
                let action = self.expression(*action);
                let body = self.expression(*body);
                return self.effect_bind(action, local, body, monotype);
            }
            ExpressionKind::EffectEach { array, element, body } => ExpressionKind::EffectEach {
                array: Box::new(self.expression(*array)),
                element,
                body: Box::new(self.expression(*body)),
            },
            ExpressionKind::EffectWhen { condition, action } => ExpressionKind::EffectWhen {
                condition: Box::new(self.expression(*condition)),
                action: Box::new(self.expression(*action)),
            },
        };
        Expression::new(kind, monotype)
    }

    fn eliminate_columns(
        &mut self,
        mut scrutinees: Vec<Expression>,
        mut alternatives: Vec<Alternative>,
    ) -> (Vec<Binding>, Vec<Expression>, Vec<Alternative>) {
        let mut bindings = vec![];
        for column in (0..scrutinees.len()).rev() {
            let Some(outcomes) = column_outcomes(&scrutinees[column], &alternatives, column) else {
                continue;
            };
            let scrutinee = scrutinees.remove(column);
            let template =
                Local { id: LocalId(0), name: "scrutinee".into(), monotype: scrutinee.monotype };
            let whole = self.fresh(&template);
            let fields: Vec<Local> = match &scrutinee.kind {
                ExpressionKind::Construct { arguments, .. } => arguments
                    .iter()
                    .map(|argument| {
                        let template = Local {
                            id: LocalId(0),
                            name: "field".into(),
                            monotype: argument.monotype,
                        };
                        self.fresh(&template)
                    })
                    .collect(),
                _ => vec![],
            };
            let mut kept = Vec::with_capacity(alternatives.len());
            for (mut alternative, outcome) in alternatives.into_iter().zip(outcomes) {
                let pattern = alternative.patterns.remove(column);
                if let ColumnOutcome::Matches = outcome {
                    for (local, field) in pattern_variables(&pattern) {
                        let value = match field {
                            Some(position) => local_expression(&fields[position]),
                            None => match &scrutinee.kind {
                                ExpressionKind::Construct { data, constructor, .. }
                                    if !fields.is_empty() =>
                                {
                                    let kind = ExpressionKind::Construct {
                                        data: data.clone(),
                                        constructor: *constructor,
                                        arguments: fields.iter().map(local_expression).collect(),
                                    };
                                    Expression::new(kind, scrutinee.monotype)
                                }
                                _ => local_expression(&whole),
                            },
                        };
                        substitute_guarded(&mut alternative.body, local, &value);
                    }
                    kept.push(alternative);
                }
            }
            alternatives = kept;
            match scrutinee.kind {
                ExpressionKind::Construct { arguments, .. } if !fields.is_empty() => {
                    for (local, value) in fields.into_iter().zip(arguments) {
                        bindings.push(Binding { local, value });
                    }
                }
                _ => bindings.push(Binding { local: whole, value: scrutinee }),
            }
        }
        (bindings, scrutinees, alternatives)
    }

    fn updates(&mut self, updates: Vec<RecordUpdate>) -> Vec<RecordUpdate> {
        updates
            .into_iter()
            .map(|update| match update {
                RecordUpdate::Leaf { label, value } => {
                    RecordUpdate::Leaf { label, value: self.expression(value) }
                }
                RecordUpdate::Branch { label, updates } => {
                    RecordUpdate::Branch { label, updates: self.updates(updates) }
                }
            })
            .collect()
    }

    fn guarded(&mut self, guarded: Guarded) -> Guarded {
        match guarded {
            Guarded::Unconditional(body) => Guarded::Unconditional(self.expression(body)),
            Guarded::Guards(branches) => Guarded::Guards(
                branches
                    .into_iter()
                    .map(|branch| GuardedBranch {
                        guards: branch
                            .guards
                            .into_iter()
                            .map(|guard| match guard {
                                Guard::Boolean(condition) => {
                                    Guard::Boolean(self.expression(condition))
                                }
                                Guard::Pattern { pattern, value } => {
                                    Guard::Pattern { pattern, value: self.expression(value) }
                                }
                            })
                            .collect(),
                        body: self.expression(branch.body),
                    })
                    .collect(),
            ),
        }
    }

    fn apply(
        &mut self,
        function: Expression,
        mut arguments: Vec<Expression>,
        monotype: crate::monotype::MonotypeId,
    ) -> Expression {
        if arguments.is_empty() {
            return function;
        }
        match function.kind {
            ExpressionKind::Apply { function: inner, arguments: mut leading } => {
                leading.append(&mut arguments);
                self.apply(*inner, leading, monotype)
            }
            ExpressionKind::Lambda { parameters, body } if self.fuel > 0 => {
                self.fuel -= 1;
                self.beta(parameters, *body, arguments, monotype)
            }
            ExpressionKind::Coerce(inner)
                if self.fuel > 0 && matches!(inner.kind, ExpressionKind::Lambda { .. }) =>
            {
                self.apply_coerced_lambda(*inner, function.monotype, arguments, monotype)
            }
            ExpressionKind::Let { bindings, body } => {
                let body = self.apply(*body, arguments, monotype);
                self.let_bindings(bindings, body)
            }
            ExpressionKind::If { .. } | ExpressionKind::Case { .. } => {
                self.apply_choice(function, arguments, monotype)
            }
            ExpressionKind::Function(id) if self.fuel > 0 => {
                // A partial application inlines too: `beta` binds the given
                // arguments outside the lambda over the missing parameters.
                let inlined = self.inlinable(id).and_then(|function| {
                    (!function.parameters.is_empty())
                        .then(|| (function.parameters.clone(), function.body.clone()))
                });
                let Some((parameters, body)) = inlined else {
                    let function = Expression::new(ExpressionKind::Function(id), function.monotype);
                    let kind = ExpressionKind::Apply { function: Box::new(function), arguments };
                    return Expression::new(kind, monotype);
                };
                self.fuel -= 1;
                let mut renaming = FxHashMap::default();
                let parameters: Vec<Local> = parameters
                    .iter()
                    .map(|parameter| self.rename_binder(parameter, &mut renaming))
                    .collect();
                let body = self.rename(body, &mut renaming);
                self.beta(parameters, body, arguments, monotype)
            }
            kind => {
                let function = Expression::new(kind, function.monotype);
                let kind = ExpressionKind::Apply { function: Box::new(function), arguments };
                Expression::new(kind, monotype)
            }
        }
    }

    /// A lambda seen as another representation of its type, such as a newtype
    /// over a function, takes its arguments in its own representation.
    fn apply_coerced_lambda(
        &mut self,
        lambda: Expression,
        coerced: MonotypeId,
        mut arguments: Vec<Expression>,
        monotype: MonotypeId,
    ) -> Expression {
        let ExpressionKind::Lambda { parameters, body } = lambda.kind else {
            unreachable!("invariant violated: only a coerced lambda is applied through")
        };
        let taken = arguments.len().min(parameters.len());
        if crate::arity::arrows(self.monotypes, coerced) < taken {
            let lambda =
                Expression::new(ExpressionKind::Lambda { parameters, body }, lambda.monotype);
            let function = Expression::new(ExpressionKind::Coerce(Box::new(lambda)), coerced);
            let kind = ExpressionKind::Apply { function: Box::new(function), arguments };
            return Expression::new(kind, monotype);
        }
        self.fuel -= 1;
        let rest = arguments.split_off(taken);
        let arguments: Vec<Expression> = arguments
            .into_iter()
            .zip(&parameters)
            .map(|(argument, parameter)| self.coerce(argument, parameter.monotype))
            .collect();
        let result = self.monotypes.result_after(lambda.monotype, taken);
        let applied = self.beta(parameters, *body, arguments, result);
        let applied = self.coerce(applied, self.monotypes.result_after(coerced, taken));
        self.apply(applied, rest, monotype)
    }

    fn beta(
        &mut self,
        mut parameters: Vec<Local>,
        body: Expression,
        mut arguments: Vec<Expression>,
        monotype: crate::monotype::MonotypeId,
    ) -> Expression {
        let rest = if arguments.len() > parameters.len() {
            arguments.split_off(parameters.len())
        } else {
            vec![]
        };
        let remaining_parameters = parameters.split_off(arguments.len());
        let bindings: Vec<Binding> = parameters
            .into_iter()
            .zip(arguments)
            .map(|(local, value)| Binding { local, value })
            .collect();
        let mut body = body;
        if !remaining_parameters.is_empty() {
            let mut lambda_monotype = body.monotype;
            for parameter in remaining_parameters.iter().rev() {
                lambda_monotype = self.monotypes.function(parameter.monotype, lambda_monotype);
            }
            body = Expression::new(
                ExpressionKind::Lambda { parameters: remaining_parameters, body: Box::new(body) },
                lambda_monotype,
            );
        }
        let body_monotype = body.monotype;
        let result =
            Expression::new(ExpressionKind::Let { bindings, body: Box::new(body) }, body_monotype);
        let result = self.expression(result);
        self.apply(result, rest, monotype)
    }

    fn let_bindings(&mut self, bindings: Vec<Binding>, body: Expression) -> Expression {
        let mut body = body;
        let mut kept = vec![];
        let recursive = bindings.iter().any(|binding| {
            bindings.iter().any(|other| occurrences(&binding.value, other.local.id).total > 0)
        });
        if !recursive
            && let Some(position) = bindings
                .iter()
                .position(|binding| matches!(binding.value.kind, ExpressionKind::Let { .. }))
        {
            return self.float_let(bindings, position, body);
        }
        if recursive {
            let monotype = body.monotype;
            return Expression::new(
                ExpressionKind::Let { bindings, body: Box::new(body) },
                monotype,
            );
        }
        for binding in bindings.into_iter().rev() {
            let uses = occurrences(&body, binding.local.id);
            // A record of trivial fields, such as a rank-N value's
            // specializations, is copied so that its field accesses resolve.
            let trivial_record = matches!(&binding.value.kind, ExpressionKind::Record(fields)
                if fields.iter().all(|(_, value)| is_trivial(value)));
            let substitutable = is_trivial(&binding.value)
                || matches!(binding.value.kind, ExpressionKind::Fail(_))
                || trivial_record
                || uses.total == 0
                || (uses.total == 1
                    && (uses.under_lambda == 0 || self.does_no_work(&binding.value)));
            if substitutable {
                if uses.total > 0 {
                    body = substitute(body, binding.local.id, &binding.value);
                    body = self.expression(body);
                }
            } else if unpack::unpackable(&binding, &body) {
                body = self.unpack(binding, body);
            } else {
                kept.push(binding);
            }
        }
        if kept.is_empty() {
            return body;
        }
        kept.reverse();
        let monotype = body.monotype;
        Expression::new(ExpressionKind::Let { bindings: kept, body: Box::new(body) }, monotype)
    }

    /// `let a = (let b = e in v)` binds `b` before `a`, which evaluates `e`
    /// when it did and lets `a` be judged by `v` alone.
    fn float_let(
        &mut self,
        mut bindings: Vec<Binding>,
        position: usize,
        body: Expression,
    ) -> Expression {
        let mut rest = bindings.split_off(position);
        let value = std::mem::replace(
            &mut rest[0].value,
            Expression::new(ExpressionKind::Unit, body.monotype),
        );
        let ExpressionKind::Let { bindings: inner, body: value } = value.kind else {
            unreachable!("invariant violated: the floated binding holds a let")
        };
        rest[0].value = *value;
        let body = self.let_bindings(rest, body);
        let body = self.let_bindings(inner, body);
        self.let_bindings(bindings, body)
    }

    fn foreign(
        &mut self,
        foreign: Foreign,
        mut arguments: Vec<Expression>,
        monotype: crate::monotype::MonotypeId,
    ) -> Expression {
        match foreign {
            Foreign::EffectPure => {
                let value = arguments.pop().expect("invariant violated: pure has one argument");
                Expression::new(ExpressionKind::EffectPure(Box::new(value)), monotype)
            }
            Foreign::EffectBind => {
                let continuation =
                    arguments.pop().expect("invariant violated: bind has two arguments");
                let action = arguments.pop().expect("invariant violated: bind has two arguments");
                let (local, body) = self.open_continuation(continuation, action.monotype);
                self.effect_bind(action, local, body, monotype)
            }
            Foreign::EffectForEach | Foreign::EffectForArray | Foreign::EffectTraverseArray => {
                let second =
                    arguments.pop().expect("invariant violated: foreach has two arguments");
                let first = arguments.pop().expect("invariant violated: foreach has two arguments");
                let (array, function) = match foreign {
                    Foreign::EffectTraverseArray => (second, first),
                    _ => (first, second),
                };
                let element_monotype = match self.monotypes.get(array.monotype) {
                    crate::monotype::Monotype::Array(element) => *element,
                    _ => array.monotype,
                };
                let (element, body) = self.open_function(function, element_monotype);
                let kind = ExpressionKind::EffectEach {
                    array: Box::new(array),
                    element,
                    body: Box::new(body),
                };
                Expression::new(kind, monotype)
            }
            Foreign::EffectMap => {
                let action = arguments.pop().expect("invariant violated: map has two arguments");
                let function = arguments.pop().expect("invariant violated: map has two arguments");
                let value =
                    self.monotypes.effect_result(action.monotype).unwrap_or(action.monotype);
                let (local, mapped) = self.open_function(function, value);
                let body = Expression::new(ExpressionKind::EffectPure(Box::new(mapped)), monotype);
                self.effect_bind(action, local, body, monotype)
            }
            Foreign::Identity => {
                arguments.pop().expect("invariant violated: identity has one argument")
            }
            Foreign::Record(operation) => self.record_operation(operation, arguments, monotype),
            Foreign::ObjectFoldM => self.object_fold(arguments, monotype),
            Foreign::UnsafeCoerce => {
                let value = arguments.pop().expect("invariant violated: coerce has one argument");
                self.coerce(value, monotype)
            }
            Foreign::Ordering => self.ordering(arguments, monotype),
            Foreign::Operator(_) => self.operator(foreign, arguments, monotype),
            foreign
                if foreign.calls(crate::foreign::INT_DIVIDE)
                    || foreign.calls(crate::foreign::INT_MODULO) =>
            {
                self.operator(foreign, arguments, monotype)
            }
            foreign => Expression::new(ExpressionKind::Foreign { foreign, arguments }, monotype),
        }
    }

    fn ordering(&mut self, arguments: Vec<Expression>, monotype: MonotypeId) -> Expression {
        let [less, equal, greater, left, right]: [Expression; 5] =
            arguments.try_into().expect("invariant violated: ordering has five arguments");
        let mut bindings = vec![];
        let left = self.shared_operand(left, "compared", &mut bindings);
        let right = self.shared_operand(right, "compared", &mut bindings);
        let boolean = self.monotypes.intern(Monotype::Boolean);
        let compare = |comparison, left: &Expression, right: &Expression| {
            let arguments = vec![left.clone(), right.clone()];
            let foreign = Foreign::Operator(Operator::Compare(comparison));
            Expression::new(ExpressionKind::Foreign { foreign, arguments }, boolean)
        };
        let equal_or_greater = ExpressionKind::If {
            condition: Box::new(compare(Comparison::Equal, &left, &right)),
            then: Box::new(equal),
            otherwise: Box::new(greater),
        };
        let chosen = ExpressionKind::If {
            condition: Box::new(compare(Comparison::LessThan, &left, &right)),
            then: Box::new(less),
            otherwise: Box::new(Expression::new(equal_or_greater, monotype)),
        };
        let chosen = Expression::new(chosen, monotype);
        if bindings.is_empty() {
            return chosen;
        }
        Expression::new(ExpressionKind::Let { bindings, body: Box::new(chosen) }, monotype)
    }

    /// The operand itself when it is trivial to repeat, and otherwise a local
    /// bound to it.
    fn shared_operand(
        &mut self,
        operand: Expression,
        name: &'static str,
        bindings: &mut Vec<Binding>,
    ) -> Expression {
        if is_trivial(&operand) {
            return operand;
        }
        let template =
            Local { id: LocalId(0), name: SmolStr::new_static(name), monotype: operand.monotype };
        let local = self.fresh(&template);
        let reference = local_expression(&local);
        bindings.push(Binding { local, value: operand });
        reference
    }

    fn open_continuation(
        &mut self,
        continuation: Expression,
        action: crate::monotype::MonotypeId,
    ) -> (Local, Expression) {
        let argument = self.monotypes.effect_result(action).unwrap_or(action);
        self.open_function(continuation, argument)
    }

    fn open_function(
        &mut self,
        function: Expression,
        argument: crate::monotype::MonotypeId,
    ) -> (Local, Expression) {
        if let ExpressionKind::Lambda { mut parameters, body } = function.kind {
            let local = parameters.remove(0);
            if parameters.is_empty() {
                return (local, *body);
            }
            let monotype = self.monotypes.result_after(function.monotype, 1);
            let lambda = Expression::new(ExpressionKind::Lambda { parameters, body }, monotype);
            return (local, lambda);
        }
        let template = Local { id: LocalId(0), name: "value".into(), monotype: argument };
        let local = self.fresh(&template);
        let result = self.monotypes.result_after(function.monotype, 1);
        let argument = Expression::new(ExpressionKind::Local(local.id), argument);
        let body = self.apply(function, vec![argument], result);
        (local, body)
    }

    fn effect_bind(
        &mut self,
        action: Expression,
        local: Local,
        body: Expression,
        monotype: crate::monotype::MonotypeId,
    ) -> Expression {
        match action.kind {
            ExpressionKind::EffectPure(value) => {
                let bindings = vec![Binding { local, value: *value }];
                self.let_bindings(bindings, body)
            }
            ExpressionKind::EffectBind { action: inner, local: inner_local, body: inner_body } => {
                let rest = self.effect_bind(*inner_body, local, body, monotype);
                let kind = ExpressionKind::EffectBind {
                    action: inner,
                    local: inner_local,
                    body: Box::new(rest),
                };
                Expression::new(kind, monotype)
            }
            ExpressionKind::Let { bindings, body: inner } => {
                let rest = self.effect_bind(*inner, local, body, monotype);
                Expression::new(ExpressionKind::Let { bindings, body: Box::new(rest) }, monotype)
            }
            kind => {
                let action = Expression::new(kind, action.monotype);
                let kind = ExpressionKind::EffectBind {
                    action: Box::new(action),
                    local,
                    body: Box::new(body),
                };
                Expression::new(kind, monotype)
            }
        }
    }

    fn rename_binder(
        &mut self,
        local: &Local,
        renaming: &mut FxHashMap<LocalId, LocalId>,
    ) -> Local {
        let fresh = self.fresh(local);
        renaming.insert(local.id, fresh.id);
        fresh
    }

    fn rename(
        &mut self,
        expression: Expression,
        renaming: &mut FxHashMap<LocalId, LocalId>,
    ) -> Expression {
        let monotype = expression.monotype;
        let kind = match expression.kind {
            ExpressionKind::Local(id) => {
                ExpressionKind::Local(renaming.get(&id).copied().unwrap_or(id))
            }
            ExpressionKind::Lambda { parameters, body } => {
                let parameters = parameters
                    .iter()
                    .map(|parameter| self.rename_binder(parameter, renaming))
                    .collect();
                ExpressionKind::Lambda { parameters, body: Box::new(self.rename(*body, renaming)) }
            }
            ExpressionKind::Let { bindings, body } => {
                let locals: Vec<Local> = bindings
                    .iter()
                    .map(|binding| self.rename_binder(&binding.local, renaming))
                    .collect();
                let bindings = bindings
                    .into_iter()
                    .zip(locals)
                    .map(|(binding, local)| Binding {
                        local,
                        value: self.rename(binding.value, renaming),
                    })
                    .collect();
                ExpressionKind::Let { bindings, body: Box::new(self.rename(*body, renaming)) }
            }
            ExpressionKind::EffectBind { action, local, body } => {
                let action = self.rename(*action, renaming);
                let local = self.rename_binder(&local, renaming);
                ExpressionKind::EffectBind {
                    action: Box::new(action),
                    local,
                    body: Box::new(self.rename(*body, renaming)),
                }
            }
            ExpressionKind::EffectEach { array, element, body } => {
                let array = self.rename(*array, renaming);
                let element = self.rename_binder(&element, renaming);
                ExpressionKind::EffectEach {
                    array: Box::new(array),
                    element,
                    body: Box::new(self.rename(*body, renaming)),
                }
            }
            ExpressionKind::Case { scrutinees, alternatives } => {
                let scrutinees = scrutinees
                    .into_iter()
                    .map(|scrutinee| self.rename(scrutinee, renaming))
                    .collect();
                let alternatives = alternatives
                    .into_iter()
                    .map(|alternative| {
                        let patterns = alternative
                            .patterns
                            .into_iter()
                            .map(|pattern| self.rename_pattern(pattern, renaming))
                            .collect();
                        let body = match alternative.body {
                            Guarded::Unconditional(body) => {
                                Guarded::Unconditional(self.rename(body, renaming))
                            }
                            Guarded::Guards(branches) => Guarded::Guards(
                                branches
                                    .into_iter()
                                    .map(|branch| GuardedBranch {
                                        guards: branch
                                            .guards
                                            .into_iter()
                                            .map(|guard| match guard {
                                                Guard::Boolean(condition) => {
                                                    Guard::Boolean(self.rename(condition, renaming))
                                                }
                                                Guard::Pattern { pattern, value } => {
                                                    let value = self.rename(value, renaming);
                                                    let pattern =
                                                        self.rename_pattern(pattern, renaming);
                                                    Guard::Pattern { pattern, value }
                                                }
                                            })
                                            .collect(),
                                        body: self.rename(branch.body, renaming),
                                    })
                                    .collect(),
                            ),
                        };
                        Alternative { patterns, body }
                    })
                    .collect();
                ExpressionKind::Case { scrutinees, alternatives }
            }
            kind => {
                let mut expression = Expression::new(kind, monotype);
                for child in children_mut(&mut expression) {
                    let taken =
                        std::mem::replace(child, Expression::new(ExpressionKind::Unit, monotype));
                    *child = self.rename(taken, renaming);
                }
                return expression;
            }
        };
        Expression::new(kind, monotype)
    }

    fn rename_pattern(
        &mut self,
        pattern: Pattern,
        renaming: &mut FxHashMap<LocalId, LocalId>,
    ) -> Pattern {
        let kind = match pattern.kind {
            PatternKind::Variable(local) => {
                PatternKind::Variable(self.rename_binder(&local, renaming))
            }
            PatternKind::Named { local, pattern: inner } => PatternKind::Named {
                local: self.rename_binder(&local, renaming),
                pattern: Box::new(self.rename_pattern(*inner, renaming)),
            },
            PatternKind::Array(elements) => PatternKind::Array(
                elements
                    .into_iter()
                    .map(|element| self.rename_pattern(element, renaming))
                    .collect(),
            ),
            PatternKind::Record(fields) => PatternKind::Record(
                fields
                    .into_iter()
                    .map(|(label, field)| (label, self.rename_pattern(field, renaming)))
                    .collect(),
            ),
            PatternKind::Constructor { data, constructor, arguments } => PatternKind::Constructor {
                data,
                constructor,
                arguments: arguments
                    .into_iter()
                    .map(|argument| self.rename_pattern(argument, renaming))
                    .collect(),
            },
            kind => kind,
        };
        Pattern { kind, monotype: pattern.monotype }
    }
}

/// Whether evaluating the expression may reach a failure: a pattern match
/// failure, a crash or a thrown exception. An argument that a foreign function
/// ignores is never evaluated.
fn can_fail(expression: &Expression) -> bool {
    match &expression.kind {
        ExpressionKind::Fail(_)
        | ExpressionKind::Foreign { foreign: Foreign::Crash | Foreign::Throw, .. } => true,
        ExpressionKind::Foreign { foreign, arguments } => {
            let ignored = foreign.ignored_arguments();
            arguments
                .iter()
                .enumerate()
                .any(|(position, argument)| !ignored.contains(&position) && can_fail(argument))
        }
        _ => {
            let mut fails = false;
            for_each_child(expression, &mut |child| fails = fails || can_fail(child));
            fails
        }
    }
}

/// The first parameter of the lambdas that an expression chooses between, when
/// it does nothing else: its conditions, scrutinees and bindings are cheap and
/// cannot fail, so every application may repeat them instead of sharing the
/// chosen lambda.
fn chosen_lambda_parameter(expression: &Expression) -> Option<&Local> {
    match &expression.kind {
        ExpressionKind::Lambda { parameters, .. } => parameters.first(),
        ExpressionKind::Let { bindings, body } => {
            bindings.iter().all(|binding| is_cheap(&binding.value)).then_some(())?;
            chosen_lambda_parameter(body)
        }
        ExpressionKind::If { condition, then, otherwise } => {
            is_cheap(condition).then_some(())?;
            chosen_lambda_parameter(otherwise)?;
            chosen_lambda_parameter(then)
        }
        ExpressionKind::Case { scrutinees, alternatives } => {
            scrutinees.iter().all(is_cheap).then_some(())?;
            let mut chosen = None;
            for alternative in alternatives {
                match &alternative.body {
                    Guarded::Unconditional(body) => {
                        chosen = chosen.or(Some(chosen_lambda_parameter(body)?));
                    }
                    Guarded::Guards(branches) => {
                        for branch in branches {
                            let cheap = branch.guards.iter().all(|guard| match guard {
                                Guard::Boolean(condition) => is_cheap(condition),
                                Guard::Pattern { value, .. } => is_cheap(value),
                            });
                            cheap.then_some(())?;
                            chosen = chosen.or(Some(chosen_lambda_parameter(&branch.body)?));
                        }
                    }
                }
            }
            chosen
        }
        _ => None,
    }
}

/// Whether evaluating the expression costs no more than a few instructions,
/// allocates nothing and cannot fail.
fn is_cheap(expression: &Expression) -> bool {
    match &expression.kind {
        ExpressionKind::Literal(_)
        | ExpressionKind::Unit
        | ExpressionKind::Local(_)
        | ExpressionKind::Function(_) => true,
        ExpressionKind::Foreign { foreign: Foreign::Operator(operator), arguments }
            if *operator != Operator::ArrayIndex && *operator != Operator::StringAppend =>
        {
            arguments.iter().all(is_cheap)
        }
        ExpressionKind::Access { record, .. } => is_cheap(record),
        _ => false,
    }
}

/// A field of a record that was just built is the field's value, once the
/// other fields' values can be dropped.
fn project(record: Expression, label: SmolStr, monotype: MonotypeId) -> Expression {
    match record.kind {
        ExpressionKind::Record(fields)
            if fields.iter().all(|(field, value)| *field == label || is_discardable(value)) =>
        {
            let (_, value) = fields
                .into_iter()
                .find(|(field, _)| *field == label)
                .expect("invariant violated: a record has the field its type promises");
            value
        }
        ExpressionKind::Let { bindings, body } => {
            let body = project(*body, label, monotype);
            Expression::new(ExpressionKind::Let { bindings, body: Box::new(body) }, monotype)
        }
        kind => {
            let record = Expression::new(kind, record.monotype);
            Expression::new(ExpressionKind::Access { record: Box::new(record), label }, monotype)
        }
    }
}

/// Whether evaluating the expression can be skipped without a trace: it is
/// pure, cannot fail, and calls nothing that could.
fn is_discardable(expression: &Expression) -> bool {
    match &expression.kind {
        ExpressionKind::Literal(_)
        | ExpressionKind::Unit
        | ExpressionKind::Local(_)
        | ExpressionKind::Function(_)
        | ExpressionKind::Lambda { .. } => true,
        ExpressionKind::Foreign { foreign: Foreign::Operator(operator), arguments }
            if *operator != Operator::ArrayIndex =>
        {
            arguments.iter().all(is_discardable)
        }
        ExpressionKind::Construct { arguments, .. } | ExpressionKind::Array(arguments) => {
            arguments.iter().all(is_discardable)
        }
        ExpressionKind::Foreign { arguments, .. } => arguments.is_empty(),
        ExpressionKind::Record(fields) => fields.iter().all(|(_, value)| is_discardable(value)),
        ExpressionKind::Access { record: value, .. } | ExpressionKind::Coerce(value) => {
            is_discardable(value)
        }
        _ => false,
    }
}

enum ColumnOutcome {
    Matches,
    Fails,
}

fn column_outcomes(
    scrutinee: &Expression,
    alternatives: &[Alternative],
    column: usize,
) -> Option<Vec<ColumnOutcome>> {
    let mut outcomes = Vec::with_capacity(alternatives.len());
    for alternative in alternatives {
        let pattern = &alternative.patterns[column];
        let outcome = match (&pattern.kind, &scrutinee.kind) {
            (PatternKind::Wildcard | PatternKind::Variable(_), _) => ColumnOutcome::Matches,
            (
                PatternKind::Constructor { constructor, arguments, .. },
                ExpressionKind::Construct { constructor: known, .. },
            ) => {
                if constructor != known {
                    ColumnOutcome::Fails
                } else if arguments.iter().all(|argument| {
                    matches!(argument.kind, PatternKind::Wildcard | PatternKind::Variable(_))
                }) {
                    ColumnOutcome::Matches
                } else {
                    return None;
                }
            }
            (PatternKind::Literal(pattern), ExpressionKind::Literal(known)) => {
                match literals_equal(pattern, known)? {
                    true => ColumnOutcome::Matches,
                    false => ColumnOutcome::Fails,
                }
            }
            _ => return None,
        };
        outcomes.push(outcome);
    }
    Some(outcomes)
}

fn literals_equal(left: &Literal, right: &Literal) -> Option<bool> {
    match (left, right) {
        (Literal::Int(left), Literal::Int(right)) => Some(left == right),
        (Literal::String(left), Literal::String(right)) => Some(left == right),
        (Literal::Char(left), Literal::Char(right)) => Some(left == right),
        (Literal::Boolean(left), Literal::Boolean(right)) => Some(left == right),
        _ => None,
    }
}

fn pattern_variables(pattern: &Pattern) -> Vec<(LocalId, Option<usize>)> {
    match &pattern.kind {
        PatternKind::Variable(local) => vec![(local.id, None)],
        PatternKind::Constructor { arguments, .. } => arguments
            .iter()
            .enumerate()
            .filter_map(|(position, argument)| match &argument.kind {
                PatternKind::Variable(local) => Some((local.id, Some(position))),
                _ => None,
            })
            .collect(),
        _ => vec![],
    }
}

fn local_expression(local: &Local) -> Expression {
    Expression::new(ExpressionKind::Local(local.id), local.monotype)
}

fn substitute_guarded(guarded: &mut Guarded, local: LocalId, value: &Expression) {
    match guarded {
        Guarded::Unconditional(body) => substitute_in_place(body, local, value),
        Guarded::Guards(branches) => {
            for branch in branches {
                for guard in &mut branch.guards {
                    match guard {
                        Guard::Boolean(condition) => substitute_in_place(condition, local, value),
                        Guard::Pattern { value: guarded_value, .. } => {
                            substitute_in_place(guarded_value, local, value)
                        }
                    }
                }
                substitute_in_place(&mut branch.body, local, value);
            }
        }
    }
}

/// The direct sub-expressions of node kinds that bind nothing.
fn children_mut(expression: &mut Expression) -> Vec<&mut Expression> {
    match &mut expression.kind {
        ExpressionKind::Array(elements) => elements.iter_mut().collect(),
        ExpressionKind::Record(fields) => fields.iter_mut().map(|(_, value)| value).collect(),
        ExpressionKind::Access { record, .. } => vec![record],
        ExpressionKind::Update { record, updates } => {
            let mut children = vec![record.as_mut()];
            update_children(updates, &mut children);
            children
        }
        ExpressionKind::Construct { arguments, .. } | ExpressionKind::Foreign { arguments, .. } => {
            arguments.iter_mut().collect()
        }
        ExpressionKind::Reuse { cell, arguments, .. } => {
            let mut children: Vec<&mut Expression> = arguments.iter_mut().collect();
            children.push(cell);
            children
        }
        ExpressionKind::Apply { function, arguments } => {
            let mut children = vec![function.as_mut()];
            children.extend(arguments.iter_mut());
            children
        }
        ExpressionKind::If { condition, then, otherwise } => vec![condition, then, otherwise],
        ExpressionKind::EffectPure(value) | ExpressionKind::Coerce(value) => vec![value],
        ExpressionKind::EffectWhen { condition, action } => vec![condition, action],
        _ => vec![],
    }
}

/// The guards and bodies of a case's alternatives.
fn for_each_alternative_child<'e>(
    alternatives: &'e [Alternative],
    visitor: &mut impl FnMut(&'e Expression),
) {
    for alternative in alternatives {
        match &alternative.body {
            Guarded::Unconditional(body) => visitor(body),
            Guarded::Guards(branches) => {
                for branch in branches {
                    for guard in &branch.guards {
                        match guard {
                            Guard::Boolean(condition) => visitor(condition),
                            Guard::Pattern { value, .. } => visitor(value),
                        }
                    }
                    visitor(&branch.body);
                }
            }
        }
    }
}

fn update_children<'a>(updates: &'a mut [RecordUpdate], children: &mut Vec<&'a mut Expression>) {
    for update in updates {
        match update {
            RecordUpdate::Leaf { value, .. } => children.push(value),
            RecordUpdate::Branch { updates, .. } => update_children(updates, children),
        }
    }
}

/// A case whose first alternative only names its scrutinees is a let.
fn binds_only(alternatives: &[Alternative]) -> bool {
    let Some(first) = alternatives.first() else { return false };
    matches!(first.body, Guarded::Unconditional(_))
        && first
            .patterns
            .iter()
            .all(|pattern| matches!(pattern.kind, PatternKind::Variable(_) | PatternKind::Wildcard))
}

fn alternatives_size(alternatives: &[Alternative]) -> usize {
    let mut total = 0;
    for alternative in alternatives {
        match &alternative.body {
            Guarded::Unconditional(body) => total += size(body),
            Guarded::Guards(branches) => {
                for branch in branches {
                    total += size(&branch.body);
                    for guard in &branch.guards {
                        total += match guard {
                            Guard::Boolean(condition) => size(condition),
                            Guard::Pattern { value, .. } => size(value),
                        };
                    }
                }
            }
        }
    }
    total
}

pub(crate) trait KnownFunctions {
    fn known(&self, id: FunctionId) -> Option<&Function>;
    fn is_recursive(&self, id: FunctionId) -> bool;
}

impl KnownFunctions for Simplifier<'_> {
    fn known(&self, id: FunctionId) -> Option<&Function> {
        self.functions[id.0 as usize].as_ref()
    }

    fn is_recursive(&self, id: FunctionId) -> bool {
        self.recursive[id.0 as usize]
    }
}

pub(crate) fn does_no_work(known: &impl KnownFunctions, expression: &Expression) -> bool {
    match &expression.kind {
        ExpressionKind::Fail(_) | ExpressionKind::Lambda { .. } => true,
        ExpressionKind::Coerce(value)
        | ExpressionKind::Access { record: value, .. }
        | ExpressionKind::EffectPure(value)
        | ExpressionKind::EffectBind { action: value, .. }
        | ExpressionKind::EffectEach { array: value, .. } => does_no_work(known, value),
        ExpressionKind::EffectWhen { condition, action } => {
            does_no_work(known, condition) && does_no_work(known, action)
        }
        ExpressionKind::Construct { arguments, .. } | ExpressionKind::Array(arguments) => {
            arguments.iter().all(|argument| does_no_work(known, argument))
        }
        ExpressionKind::Record(fields) => {
            fields.iter().all(|(_, value)| does_no_work(known, value))
        }
        ExpressionKind::Foreign { foreign, arguments } => {
            let builds_value = foreign.is_effectful() || matches!(foreign, Foreign::Identity);
            (builds_value || arguments.is_empty())
                && arguments.iter().all(|argument| does_no_work(known, argument))
        }
        ExpressionKind::Apply { function, arguments } => {
            let builds_value = match &function.kind {
                ExpressionKind::Function(id) => known.known(*id).is_some_and(|callee| {
                    callee.parameters.len() > arguments.len()
                        || (!known.is_recursive(*id) && does_no_work(known, &callee.body))
                }),
                ExpressionKind::Lambda { parameters, body } => {
                    parameters.len() > arguments.len() || does_no_work(known, body)
                }
                _ => false,
            };
            builds_value && arguments.iter().all(|argument| does_no_work(known, argument))
        }
        _ => is_trivial(expression),
    }
}

pub(crate) fn is_trivial(expression: &Expression) -> bool {
    match &expression.kind {
        ExpressionKind::Literal(_) | ExpressionKind::Unit | ExpressionKind::Local(_) => true,
        ExpressionKind::Function(_) => true,
        ExpressionKind::Foreign { arguments, .. } => arguments.is_empty(),
        ExpressionKind::Construct { arguments, .. } => arguments.is_empty(),
        ExpressionKind::Lambda { parameters, body } => is_foreign_wrapper(parameters, body),
        _ => false,
    }
}

fn is_foreign_wrapper(parameters: &[Local], body: &Expression) -> bool {
    let ExpressionKind::Foreign { arguments, .. } = &body.kind else { return false };
    arguments.len() == parameters.len()
        && arguments.iter().zip(parameters).all(|(argument, parameter)| {
            matches!(argument.kind, ExpressionKind::Local(id) if id == parameter.id)
        })
}

fn size(expression: &Expression) -> usize {
    let mut total = 0;
    visit(expression, &mut |_| total += 1);
    total
}

#[derive(Default)]
struct Occurrences {
    total: usize,
    under_lambda: usize,
}

fn occurrences(expression: &Expression, local: LocalId) -> Occurrences {
    let mut result = Occurrences::default();
    count(expression, local, false, &mut result);
    result
}

fn count(expression: &Expression, local: LocalId, under_lambda: bool, result: &mut Occurrences) {
    // Callers tell no, one and several occurrences apart, and where a single
    // one is; past two there is nothing more to learn.
    if result.total >= 2 {
        return;
    }
    match &expression.kind {
        ExpressionKind::Local(id) if *id == local => {
            result.total += 1;
            if under_lambda {
                result.under_lambda += 1;
            }
        }
        ExpressionKind::Lambda { body, .. } => count(body, local, true, result),
        ExpressionKind::EffectEach { array, body, .. } => {
            count(array, local, under_lambda, result);
            count(body, local, true, result);
        }
        _ => for_each_child(expression, &mut |child| count(child, local, under_lambda, result)),
    }
}

pub fn visit(expression: &Expression, visitor: &mut impl FnMut(&Expression)) {
    visitor(expression);
    for_each_child(expression, &mut |child| visit(child, visitor));
}

pub fn for_each_child<'e>(expression: &'e Expression, visitor: &mut impl FnMut(&'e Expression)) {
    match &expression.kind {
        ExpressionKind::Literal(_)
        | ExpressionKind::Unit
        | ExpressionKind::Local(_)
        | ExpressionKind::Function(_)
        | ExpressionKind::Fail(_) => {}
        ExpressionKind::Array(elements) => elements.iter().for_each(visitor),
        ExpressionKind::Record(fields) => fields.iter().for_each(|(_, value)| visitor(value)),
        ExpressionKind::Access { record, .. } => visitor(record),
        ExpressionKind::Update { record, updates } => {
            visitor(record);
            for_each_update(updates, visitor);
        }
        ExpressionKind::Construct { arguments, .. } | ExpressionKind::Foreign { arguments, .. } => {
            arguments.iter().for_each(visitor)
        }
        ExpressionKind::Reuse { cell, arguments, .. } => {
            arguments.iter().for_each(&mut *visitor);
            visitor(cell);
        }
        ExpressionKind::Apply { function, arguments } => {
            visitor(function);
            arguments.iter().for_each(visitor);
        }
        ExpressionKind::Lambda { body, .. } => visitor(body),
        ExpressionKind::Let { bindings, body } => {
            bindings.iter().for_each(|binding| visitor(&binding.value));
            visitor(body);
        }
        ExpressionKind::If { condition, then, otherwise } => {
            visitor(condition);
            visitor(then);
            visitor(otherwise);
        }
        ExpressionKind::Case { scrutinees, alternatives } => {
            scrutinees.iter().for_each(&mut *visitor);
            for alternative in alternatives {
                match &alternative.body {
                    Guarded::Unconditional(body) => visitor(body),
                    Guarded::Guards(branches) => {
                        for branch in branches {
                            for guard in &branch.guards {
                                match guard {
                                    Guard::Boolean(condition) => visitor(condition),
                                    Guard::Pattern { value, .. } => visitor(value),
                                }
                            }
                            visitor(&branch.body);
                        }
                    }
                }
            }
        }
        ExpressionKind::EffectPure(value) | ExpressionKind::Coerce(value) => visitor(value),
        ExpressionKind::EffectBind { action, body, .. } => {
            visitor(action);
            visitor(body);
        }
        ExpressionKind::EffectEach { array, body, .. } => {
            visitor(array);
            visitor(body);
        }
        ExpressionKind::EffectWhen { condition, action } => {
            visitor(condition);
            visitor(action);
        }
    }
}

fn for_each_update<'e>(updates: &'e [RecordUpdate], visitor: &mut impl FnMut(&'e Expression)) {
    for update in updates {
        match update {
            RecordUpdate::Leaf { value, .. } => visitor(value),
            RecordUpdate::Branch { updates, .. } => for_each_update(updates, visitor),
        }
    }
}

fn substitute(expression: Expression, local: LocalId, value: &Expression) -> Expression {
    let mut expression = expression;
    substitute_in_place(&mut expression, local, value);
    expression
}

fn substitute_in_place(expression: &mut Expression, local: LocalId, value: &Expression) {
    if let ExpressionKind::Local(id) = expression.kind
        && id == local
    {
        // The reference may expect another representation of the same value,
        // as a newtype constructor's result does a recursive newtype.
        let monotype = expression.monotype;
        *expression = value.clone();
        if expression.monotype != monotype {
            let coerced =
                std::mem::replace(expression, Expression::new(ExpressionKind::Unit, monotype));
            expression.kind = ExpressionKind::Coerce(Box::new(coerced));
        }
        return;
    }
    for_each_child_mut(expression, &mut |child| substitute_in_place(child, local, value));
}

pub fn for_each_child_mut(expression: &mut Expression, visitor: &mut impl FnMut(&mut Expression)) {
    match &mut expression.kind {
        ExpressionKind::Literal(_)
        | ExpressionKind::Unit
        | ExpressionKind::Local(_)
        | ExpressionKind::Function(_)
        | ExpressionKind::Fail(_) => {}
        ExpressionKind::Lambda { body, .. } => visitor(body),
        ExpressionKind::Let { bindings, body } => {
            bindings.iter_mut().for_each(|binding| visitor(&mut binding.value));
            visitor(body);
        }
        ExpressionKind::Case { scrutinees, alternatives } => {
            scrutinees.iter_mut().for_each(&mut *visitor);
            for alternative in alternatives {
                match &mut alternative.body {
                    Guarded::Unconditional(body) => visitor(body),
                    Guarded::Guards(branches) => {
                        for branch in branches {
                            for guard in &mut branch.guards {
                                match guard {
                                    Guard::Boolean(condition) => visitor(condition),
                                    Guard::Pattern { value, .. } => visitor(value),
                                }
                            }
                            visitor(&mut branch.body);
                        }
                    }
                }
            }
        }
        ExpressionKind::EffectBind { action, body, .. } => {
            visitor(action);
            visitor(body);
        }
        ExpressionKind::EffectEach { array, body, .. } => {
            visitor(array);
            visitor(body);
        }
        _ => {
            for child in children_mut(expression) {
                visitor(child);
            }
        }
    }
}

pub(crate) fn function_references(expression: &Expression) -> FxHashSet<FunctionId> {
    let mut references = FxHashSet::default();
    visit(expression, &mut |node| {
        if let ExpressionKind::Function(id) = node.kind {
            references.insert(id);
        }
    });
    references
}

/// Tarjan's algorithm; components come out callees first.
pub(crate) fn strongly_connected_components(
    references: &[FxHashSet<FunctionId>],
) -> Vec<Vec<FunctionId>> {
    struct State<'r> {
        references: &'r [FxHashSet<FunctionId>],
        index: Vec<Option<usize>>,
        lowlink: Vec<usize>,
        on_stack: Vec<bool>,
        stack: Vec<usize>,
        next: usize,
        components: Vec<Vec<FunctionId>>,
    }

    fn connect(state: &mut State<'_>, node: usize) {
        state.index[node] = Some(state.next);
        state.lowlink[node] = state.next;
        state.next += 1;
        state.stack.push(node);
        state.on_stack[node] = true;
        let mut successors: Vec<usize> =
            state.references[node].iter().map(|id| id.0 as usize).collect();
        successors.sort_unstable();
        for successor in successors {
            match state.index[successor] {
                None => {
                    connect(state, successor);
                    state.lowlink[node] = state.lowlink[node].min(state.lowlink[successor]);
                }
                Some(index) if state.on_stack[successor] => {
                    state.lowlink[node] = state.lowlink[node].min(index);
                }
                Some(_) => {}
            }
        }
        if Some(state.lowlink[node]) == state.index[node] {
            let mut component = vec![];
            while let Some(member) = state.stack.pop() {
                state.on_stack[member] = false;
                component.push(FunctionId(member as u32));
                if member == node {
                    break;
                }
            }
            state.components.push(component);
        }
    }

    let count = references.len();
    let mut state = State {
        references,
        index: vec![None; count],
        lowlink: vec![0; count],
        on_stack: vec![false; count],
        stack: vec![],
        next: 0,
        components: vec![],
    };
    for node in 0..count {
        if state.index[node].is_none() {
            connect(&mut state, node);
        }
    }
    state.components
}

fn prune(functions: Vec<Function>, entry: FunctionId) -> Program {
    prune_unreachable(functions, entry).0
}

pub(crate) fn prune_unreachable(
    functions: Vec<Function>,
    entry: FunctionId,
) -> (Program, FxHashMap<FunctionId, FunctionId>) {
    let mut reachable = vec![false; functions.len()];
    let mut pending = vec![entry];
    while let Some(id) = pending.pop() {
        if std::mem::replace(&mut reachable[id.0 as usize], true) {
            continue;
        }
        pending.extend(function_references(&functions[id.0 as usize].body));
    }
    let mut renumbering = FxHashMap::default();
    let mut kept = vec![];
    for (index, function) in functions.into_iter().enumerate() {
        if reachable[index] {
            renumbering.insert(FunctionId(index as u32), FunctionId(kept.len() as u32));
            kept.push(function);
        }
    }
    for function in &mut kept {
        renumber(&mut function.body, &renumbering);
    }
    let entry = renumbering[&entry];
    (Program { functions: kept, entry }, renumbering)
}

fn renumber(expression: &mut Expression, renumbering: &FxHashMap<FunctionId, FunctionId>) {
    if let ExpressionKind::Function(id) = &mut expression.kind {
        *id = renumbering[id];
        return;
    }
    for_each_child_mut(expression, &mut |child| renumber(child, renumbering));
}
