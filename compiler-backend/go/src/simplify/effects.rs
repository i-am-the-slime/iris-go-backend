use smol_str::SmolStr;

use super::{Simplifier, choice, three_way};
use crate::foreign::{Comparison, Foreign, GoPackage, Operator};
use crate::monomorphic::{
    Alternative, Binding, Expression, ExpressionKind, Guarded, Literal, Local, LocalId, Results,
};
use crate::monotype::{Monotype, MonotypeId};
use crate::purity::{is_discardable, is_trivial, runs_effect_when_applied, size};

const PUSHED_CONTINUATION_SIZE: usize = 80;

const VIEWING_CONTINUATION_SIZE: usize = 320;

impl Simplifier<'_> {
    pub(super) fn foreign(
        &mut self,
        foreign: &'static Foreign,
        arguments: Vec<Expression>,
        monotype: crate::monotype::MonotypeId,
    ) -> Expression {
        if let Some(outside) =
            choice::negative_within(foreign, &arguments, monotype, self.monotypes)
        {
            return outside;
        }
        if let Some(elements) = choice::negative_update(foreign, &arguments) {
            return elements;
        }
        if let Some(value) = three_way::constant_comparison(foreign, &arguments) {
            return Expression::new(ExpressionKind::Literal(Literal::Boolean(value)), monotype);
        }
        let arguments = match self.literal_array_operation(foreign, arguments, monotype) {
            Ok(evaluated) => return evaluated,
            Err(arguments) => arguments,
        };
        let arguments = match self.short_circuit(foreign, arguments, monotype) {
            Ok(searched) => return searched,
            Err(arguments) => arguments,
        };
        let arguments = match self.reduction(foreign, arguments, monotype) {
            Ok(reduced) => return reduced,
            Err(arguments) => arguments,
        };
        let arguments = match self.unconsed(foreign, arguments, monotype) {
            Ok(unconsed) => return unconsed,
            Err(arguments) => arguments,
        };
        let mut arguments = match self.sequenced_fold(foreign, arguments, monotype) {
            Ok(looped) => return looped,
            Err(arguments) => arguments,
        };
        match foreign {
            Foreign::Perform { function, .. }
                if function.package == GoPackage::Aff
                    && function.name == "TraverseParArrayDirect"
                    && !self.suspension.traversal_may_suspend(
                        &arguments[0],
                        &arguments[1],
                        self.monotypes,
                    ) =>
            {
                self.foreign(&Foreign::EffectTraverseArrayResults, arguments, monotype)
            }
            Foreign::Perform { function, .. }
                if function.package == GoPackage::Aff
                    && function.name == "SequenceParArrayDirect"
                    && !self.suspension.may_suspend(&arguments[0], self.monotypes) =>
            {
                Expression::new(
                    ExpressionKind::Foreign { foreign: &crate::foreign::SEQUENCE_ARRAY, arguments },
                    monotype,
                )
            }
            Foreign::Perform { function, .. }
                if function.package == GoPackage::Direct
                    && function.name == "SequenceArray"
                    && self.sequences_unit_actions(&arguments[0]) =>
            {
                self.sequenced_unit_actions(arguments, monotype)
            }
            Foreign::Perform { function, .. }
                if function.package == GoPackage::Aff
                    && function.name == "ParApplyDirect"
                    && arguments
                        .iter()
                        .all(|argument| !self.suspension.may_suspend(argument, self.monotypes)) =>
            {
                self.sequential_apply(arguments, monotype)
            }
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
            Foreign::EffectForEach
            | Foreign::EffectForArray
            | Foreign::EffectTraverseArray
            | Foreign::EffectForArrayResults
            | Foreign::EffectTraverseArrayResults => {
                let second =
                    arguments.pop().expect("invariant violated: foreach has two arguments");
                let first = arguments.pop().expect("invariant violated: foreach has two arguments");
                let (array, function) = match foreign {
                    Foreign::EffectTraverseArray | Foreign::EffectTraverseArrayResults => {
                        (second, first)
                    }
                    _ => (first, second),
                };
                let results = match foreign {
                    Foreign::EffectForArrayResults | Foreign::EffectTraverseArrayResults => {
                        Results::Collected
                    }
                    _ => Results::Discarded,
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
                    results,
                };
                Expression::new(kind, monotype)
            }
            Foreign::EffectForArrayWithIndex | Foreign::EffectTraverseArrayWithIndex => {
                self.each_with_index(foreign, arguments, monotype)
            }
            Foreign::EffectFoldArray => self.fold_array(arguments, monotype),
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
            Foreign::RecordGet if has_literal_label(&arguments) => {
                let record = arguments.pop().expect("invariant violated: get has two arguments");
                let label = arguments.pop().expect("invariant violated: get has two arguments");
                let ExpressionKind::Literal(Literal::String(label)) = label.kind else {
                    unreachable!("invariant violated: the label was just matched as a string")
                };
                self.field_of(record, SmolStr::from(label), monotype)
            }
            Foreign::Record(operation) => self.record_operation(*operation, arguments, monotype),
            Foreign::RecordHas => self.record_has(arguments, monotype),
            Foreign::ObjectFoldM => self.object_fold(arguments, monotype),
            Foreign::UnsafeCoerce => {
                let value = arguments.pop().expect("invariant violated: coerce has one argument");
                self.coerce(value, monotype)
            }
            Foreign::Ordering => self.ordering(arguments, monotype),
            Foreign::Operator(_) => self.operator(foreign, arguments, monotype),
            Foreign::Int64 { .. } => self.int64_operation(foreign, arguments, monotype),
            foreign
                if foreign.calls(crate::foreign::ARRAY_CONCAT)
                    && matches!(arguments[0].kind, ExpressionKind::Array(_)) =>
            {
                self.concatenation(arguments, monotype)
            }
            // A string's code units are the chars it was built from, one by one, lone
            // surrogates included: the array is its own.
            foreign
                if foreign.calls(crate::foreign::TO_CHAR_ARRAY)
                    && matches!(&arguments[0].kind, ExpressionKind::Foreign { foreign, .. }
                        if foreign.calls(crate::foreign::FROM_CHAR_ARRAY)) =>
            {
                let ExpressionKind::Foreign { mut arguments, .. } =
                    arguments.pop().expect("invariant violated: toCharArray has one argument").kind
                else {
                    unreachable!("invariant violated: the argument was just matched as a foreign")
                };
                arguments.pop().expect("invariant violated: fromCharArray has one argument")
            }
            foreign
                if foreign.calls(crate::foreign::FROM_CHAR_ARRAY)
                    && matches!(&arguments[0].kind, ExpressionKind::Foreign { foreign, .. }
                        if foreign.calls(crate::foreign::TO_CHAR_ARRAY)) =>
            {
                let ExpressionKind::Foreign { arguments, .. } = arguments
                    .pop()
                    .expect("invariant violated: fromCharArray has one argument")
                    .kind
                else {
                    unreachable!("invariant violated: the argument was just matched as a foreign")
                };
                let foreign = crate::foreign::WELL_FORMED_STRING.interned();
                Expression::new(ExpressionKind::Foreign { foreign, arguments }, monotype)
            }
            foreign
                if foreign.calls(crate::foreign::INT_DIVIDE)
                    || foreign.calls(crate::foreign::INT_MODULO)
                    || foreign.calls(crate::foreign::SHOW_NUMBER)
                    || foreign.calls(crate::foreign::STRING_TO_UPPER)
                    || foreign.calls(crate::foreign::STRING_TO_LOWER)
                    || foreign.calls(crate::foreign::STRING_TRIM) =>
            {
                self.operator(foreign, arguments, monotype)
            }
            foreign => Expression::new(ExpressionKind::Foreign { foreign, arguments }, monotype),
        }
    }

    fn sequential_apply(&mut self, arguments: Vec<Expression>, monotype: MonotypeId) -> Expression {
        let [functions, values]: [Expression; 2] =
            arguments.try_into().expect("invariant violated: a parallel apply has two arguments");
        let function_type =
            self.monotypes.effect_result(functions.monotype).unwrap_or(functions.monotype);
        let value_type = self.monotypes.effect_result(values.monotype).unwrap_or(values.monotype);
        let result = self.monotypes.effect_result(monotype).unwrap_or(monotype);
        let template =
            Local { id: LocalId(0), name: SmolStr::new_static("f"), monotype: function_type };
        let function = self.fresh(&template);
        let template = Local {
            id: LocalId(0),
            name: self.monotypes.value_name(value_type),
            monotype: value_type,
        };
        let value = self.fresh(&template);
        let applied = self.apply(function.expression(), vec![value.expression()], result);
        let pure = Expression::new(ExpressionKind::EffectPure(Box::new(applied)), monotype);
        let inner = ExpressionKind::EffectBind {
            action: Box::new(values),
            local: value,
            body: Box::new(pure),
        };
        let inner = Expression::new(inner, monotype);
        let outer = ExpressionKind::EffectBind {
            action: Box::new(functions),
            local: function,
            body: Box::new(inner),
        };
        Expression::new(outer, monotype)
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
            let foreign = Foreign::Operator(Operator::Compare(comparison)).interned();
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
    pub(super) fn shared_operand(
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
        let reference = local.expression();
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
        let name = self.monotypes.value_name(argument);
        let template = Local { id: LocalId(0), name, monotype: argument };
        let local = self.fresh(&template);
        let result = self.monotypes.result_after(function.monotype, 1);
        let argument = Expression::new(ExpressionKind::Local(local.id), argument);
        let body = self.apply(function, vec![argument], result);
        (local, body)
    }

    pub(super) fn effect_bind(
        &mut self,
        action: Expression,
        local: Local,
        body: Expression,
        monotype: crate::monotype::MonotypeId,
    ) -> Expression {
        if let ExpressionKind::EffectPure(value) = &action.kind
            && matches!(value.kind, ExpressionKind::Construct { .. })
            && cases_on(&body, local.id)
        {
            return self.bind_chosen(action, local, body, monotype);
        }
        match action.kind {
            ExpressionKind::EffectPure(value)
                if builds_safely(&body) && !self.defers_work(&local, &body) =>
            {
                let bindings = vec![Binding { local, value: *value }];
                self.let_bindings(bindings, body)
            }
            ExpressionKind::EffectBind { action: inner, local: inner_local, body: inner_body } => {
                let inner = self.keeping_ranked_position(*inner, action.position);
                let rest = self.effect_bind(*inner_body, local, body, monotype);
                let kind = ExpressionKind::EffectBind {
                    action: Box::new(inner),
                    local: inner_local,
                    body: Box::new(rest),
                };
                Expression::new(kind, monotype)
            }
            ExpressionKind::Let { bindings, body: inner } => {
                let rest = self.effect_bind(*inner, local, body, monotype);
                self.let_bindings(bindings, rest)
            }
            ExpressionKind::If { .. } | ExpressionKind::Case { .. }
                if chooses_only_pure(&action)
                    && builds_safely(&body)
                    && !self.defers_work(&local, &body) =>
            {
                let value_monotype =
                    self.monotypes.effect_result(action.monotype).unwrap_or(local.monotype);
                let value = self.map_choices(action, value_monotype, &mut |_, chosen| {
                    let ExpressionKind::EffectPure(value) = chosen.kind else {
                        unreachable!("invariant violated: every choice was checked to be pure")
                    };
                    *value
                });
                self.let_bindings(vec![Binding { local, value }], body)
            }
            ExpressionKind::If { .. } | ExpressionKind::Case { .. }
                if PushedContinuation::measure(&action, &body, local.id)
                    .is_some_and(|pushed| pushed.fits()) =>
            {
                let mut original = Some((local, body));
                let copied =
                    original.clone().expect("invariant violated: the continuation is there");
                self.push_into_choices(action, monotype, &mut |simplifier, chosen| {
                    let (local, body) = match original.take() {
                        Some(kept) => kept,
                        None => simplifier.renamed_continuation(&copied),
                    };
                    simplifier.bind_chosen(chosen, local, body, monotype)
                })
            }
            kind => {
                let action = Expression::new(kind, action.monotype).located(action.position);
                if self.returns_its_unit(&action, &local, &body, monotype) {
                    return action;
                }
                if let Some(chosen) = self.peek_choice(&action, &local, &body, monotype) {
                    return chosen;
                }
                let kind = ExpressionKind::EffectBind {
                    action: Box::new(action),
                    local,
                    body: Box::new(body),
                };
                Expression::new(kind, monotype)
            }
        }
    }

    /// `map_choices` for a continuation pushed into the choices: the lets on the way are
    /// settled again, since the continuation may take apart what they bind.
    fn push_into_choices(
        &mut self,
        expression: Expression,
        monotype: MonotypeId,
        chosen: &mut impl FnMut(&mut Self, Expression) -> Expression,
    ) -> Expression {
        match expression.kind {
            ExpressionKind::Let { bindings, body } => {
                let body = self.push_into_choices(*body, monotype, chosen);
                self.let_bindings(bindings, body)
            }
            ExpressionKind::If { condition, then, otherwise } => {
                let then = self.push_into_choices(*then, monotype, chosen);
                let otherwise = self.push_into_choices(*otherwise, monotype, chosen);
                let kind = ExpressionKind::If {
                    condition,
                    then: Box::new(then),
                    otherwise: Box::new(otherwise),
                };
                Expression::new(kind, monotype)
            }
            ExpressionKind::Case { .. } => {
                self.map_choices(expression, monotype, &mut |simplifier, leaf| {
                    simplifier.push_into_choices(leaf, monotype, chosen)
                })
            }
            ExpressionKind::Fail(message) => {
                Expression::new(ExpressionKind::Fail(message), monotype)
            }
            kind => chosen(self, Expression::new(kind, expression.monotype)),
        }
    }

    fn renamed_continuation(&mut self, continuation: &(Local, Expression)) -> (Local, Expression) {
        let (local, body) = continuation;
        let mut renaming = rustc_hash::FxHashMap::default();
        let local = self.rename_binder(local, &mut renaming);
        let mut body = body.clone();
        self.rename(&mut body, &mut renaming);
        (local, body)
    }

    /// The continuation of a bind run after one of the choices of its action: a constructor
    /// the choice returns is matched where the continuation looks at it, with its fields bound
    /// once beforehand.
    fn bind_chosen(
        &mut self,
        chosen: Expression,
        local: Local,
        body: Expression,
        monotype: MonotypeId,
    ) -> Expression {
        let ExpressionKind::EffectPure(value) = chosen.kind else {
            return self.effect_bind(chosen, local, body, monotype);
        };
        if !matches!(value.kind, ExpressionKind::Construct { .. }) {
            let action = Expression::new(ExpressionKind::EffectPure(value), chosen.monotype);
            return self.effect_bind(action, local, body, monotype);
        }
        let mut bindings = vec![];
        let built = self.shared_construction(*value, &mut bindings);
        self.substituting_alias(&local, &built);
        let body = super::substitute(body, local.id, &built, self.monotypes);
        let body = self.expression(body);
        self.let_bindings(bindings, body)
    }

    fn shared_construction(
        &mut self,
        value: Expression,
        bindings: &mut Vec<Binding>,
    ) -> Expression {
        let ExpressionKind::Construct { data, constructor, arguments } = value.kind else {
            return self.shared_operand(value, "field", bindings);
        };
        let arguments = arguments
            .into_iter()
            .map(|argument| self.shared_construction(argument, bindings))
            .collect();
        Expression::new(ExpressionKind::Construct { data, constructor, arguments }, value.monotype)
    }

    fn returns_its_unit(
        &self,
        action: &Expression,
        local: &Local,
        body: &Expression,
        monotype: crate::monotype::MonotypeId,
    ) -> bool {
        let ExpressionKind::EffectPure(value) = &body.kind else { return false };
        let unit = matches!(
            value.kind,
            ExpressionKind::Unit | ExpressionKind::Foreign { foreign: Foreign::Unit, .. }
        );
        unit && matches!(self.monotypes.get(local.monotype), Monotype::Unit)
            && self.monotypes.same_without_causes(action.monotype, monotype)
    }

    /// Whether binding `local` to a pure value in place of running a bind would build `body`, a
    /// thunk's body, where the action is built rather than where it runs. A bind the source
    /// writes as `pure unit >>= \_ -> later` says that `later` waits for the action to run.
    fn defers_work(&self, local: &Local, body: &Expression) -> bool {
        self.thunk_parameters.contains(&local.id) && !self.does_no_work(body)
    }

    /// A thunk applied to a local, as a bind's continuation is to the local the bind binds, makes
    /// that local the thunk's parameter.
    /// A local bound to a function that runs an action in pure code runs it wherever it is
    /// applied, whether a let or an inlined call binds it.
    pub(super) fn remember_unsafely_effectful(&mut self, binding: &Binding) {
        if runs_effect_when_applied(self, &binding.value) {
            self.unsafely_effectful_locals.insert(binding.local.id);
        }
    }

    pub(super) fn pass_on_thunk_parameter(&mut self, binding: &Binding) {
        if let ExpressionKind::Local(argument) = binding.value.kind
            && self.thunk_parameters.contains(&binding.local.id)
        {
            self.thunk_parameters.insert(argument);
        }
    }

    /// `concat [a, mempty, b]` without the arrays that are empty, such as `mempty`'s, and a
    /// lone array that remains for itself: `[]` when none does.
    fn concatenation(
        &mut self,
        mut arguments: Vec<Expression>,
        monotype: MonotypeId,
    ) -> Expression {
        let array = arguments.pop().expect("invariant violated: concat has one argument");
        let ExpressionKind::Array(mut arrays) = array.kind else {
            unreachable!("invariant violated: the argument was just matched as an array")
        };
        arrays.retain(|array| !self.is_empty_array(array));
        match arrays.len() {
            0 => Expression::new(ExpressionKind::Array(vec![]), monotype),
            1 => arrays.pop().expect("invariant violated: one array remains"),
            _ => {
                let array = Expression::new(ExpressionKind::Array(arrays), array.monotype);
                let foreign = crate::foreign::ARRAY_CONCAT.interned();
                Expression::new(
                    ExpressionKind::Foreign { foreign, arguments: vec![array] },
                    monotype,
                )
            }
        }
    }

    pub(super) fn is_empty_array(&self, expression: &Expression) -> bool {
        match &expression.kind {
            ExpressionKind::Array(elements) => elements.is_empty(),
            ExpressionKind::Coerce(value) => self.is_empty_array(value),
            ExpressionKind::Function(id) => {
                self.functions[id.0 as usize].as_ref().is_some_and(|function| {
                    function.parameters.is_empty()
                        && !self.recursive[id.0 as usize]
                        && self.is_empty_array(&function.body)
                })
            }
            _ => false,
        }
    }
}

/// Whether the expression starts with a `case` of the local, maybe as the first action it runs.
fn cases_on(expression: &Expression, local: LocalId) -> bool {
    match &expression.kind {
        ExpressionKind::Case { scrutinees, .. } => scrutinees
            .iter()
            .any(|scrutinee| matches!(scrutinee.kind, ExpressionKind::Local(id) if id == local)),
        ExpressionKind::EffectBind { action, .. } => cases_on(action, local),
        ExpressionKind::EffectPure(value) | ExpressionKind::Let { body: value, .. } => {
            cases_on(value, local)
        }
        _ => false,
    }
}

/// What running a bind's continuation after each choice of its action adds to the code, when the
/// continuation starts by matching the local and that match decides every constructor a choice
/// returns: such a choice keeps only the alternative it picks. A choice that does more keeps the
/// whole continuation, and the largest copy is the one that would be there anyway. A choice that
/// returns an array combinators build, `Emit (take n (map f chunk))`, lets the alternative read
/// it without storing it, which is worth more copies.
struct PushedContinuation<'e> {
    alternatives: &'e [Alternative],
    column: usize,
    whole: usize,
    copies: Vec<usize>,
    constructions: usize,
    viewed: bool,
    bound: Vec<(LocalId, &'e Expression)>,
}

impl<'e> PushedContinuation<'e> {
    fn measure(
        action: &'e Expression,
        body: &'e Expression,
        local: LocalId,
    ) -> Option<PushedContinuation<'e>> {
        let (alternatives, column) = first_match(body, local)?;
        let mut pushed = PushedContinuation {
            alternatives,
            column,
            whole: size(body),
            copies: vec![],
            constructions: 0,
            viewed: false,
            bound: vec![],
        };
        pushed.choice(action, false)?;
        (pushed.constructions > 0).then_some(pushed)
    }

    fn fits(&self) -> bool {
        let largest = self.copies.iter().copied().max().unwrap_or(0);
        let added = self.copies.iter().sum::<usize>() - largest;
        let budget = if self.viewed { VIEWING_CONTINUATION_SIZE } else { PUSHED_CONTINUATION_SIZE };
        added <= budget
    }

    fn choice(&mut self, expression: &'e Expression, returned: bool) -> Option<()> {
        match &expression.kind {
            ExpressionKind::EffectPure(value) if !returned => self.choice(value, true)?,
            ExpressionKind::Construct { .. } if returned => {
                let outcomes =
                    super::coverage::column_outcomes(expression, self.alternatives, self.column)?;
                let chosen = outcomes.iter().position(|outcome| {
                    matches!(outcome, super::coverage::ColumnOutcome::Matches)
                })?;
                self.constructions += 1;
                self.viewed |= self.builds_view(expression);
                self.copies
                    .push(super::coverage::alternatives_size(&self.alternatives[chosen..=chosen]));
            }
            ExpressionKind::Fail(_) => {}
            ExpressionKind::Let { bindings, body } => {
                self.bound
                    .extend(bindings.iter().map(|binding| (binding.local.id, &binding.value)));
                self.choice(body, returned)?
            }
            ExpressionKind::EffectBind { body, .. } if !returned => self.choice(body, false)?,
            ExpressionKind::If { then, otherwise, .. } => {
                self.choice(then, returned)?;
                self.choice(otherwise, returned)?;
            }
            ExpressionKind::Case { alternatives, .. } => {
                for alternative in alternatives {
                    match &alternative.body {
                        Guarded::Unconditional(body) => self.choice(body, returned)?,
                        Guarded::Guards(branches) => {
                            for branch in branches {
                                self.choice(&branch.body, returned)?
                            }
                        }
                    }
                }
            }
            _ => self.copies.push(self.whole),
        }
        Some(())
    }

    fn builds_view(&self, construction: &Expression) -> bool {
        let ExpressionKind::Construct { arguments, .. } = &construction.kind else {
            return match &construction.kind {
                ExpressionKind::Local(id) => self
                    .bound
                    .iter()
                    .any(|(bound, value)| bound == id && super::views::builds_view(value)),
                _ => super::views::builds_view(construction),
            };
        };
        arguments.iter().any(|argument| self.builds_view(argument))
    }
}

fn first_match(
    expression: &Expression,
    local: LocalId,
) -> Option<(&[crate::monomorphic::Alternative], usize)> {
    match &expression.kind {
        ExpressionKind::Case { scrutinees, alternatives } => {
            let column = scrutinees.iter().position(
                |scrutinee| matches!(scrutinee.kind, ExpressionKind::Local(id) if id == local),
            )?;
            Some((alternatives, column))
        }
        ExpressionKind::Let { body, .. } | ExpressionKind::EffectPure(body) => {
            first_match(body, local)
        }
        ExpressionKind::EffectBind { action, .. } => first_match(action, local),
        _ => None,
    }
}

fn builds_safely(expression: &Expression) -> bool {
    match &expression.kind {
        ExpressionKind::EffectPure(value) => is_discardable(value),
        ExpressionKind::EffectBind { action, .. } => builds_safely(action),
        ExpressionKind::Let { bindings, body } => {
            bindings.iter().all(|binding| is_discardable(&binding.value)) && builds_safely(body)
        }
        ExpressionKind::If { condition, then, otherwise } => {
            is_discardable(condition) && builds_safely(then) && builds_safely(otherwise)
        }
        ExpressionKind::Case { scrutinees, alternatives } => {
            scrutinees.iter().all(is_discardable)
                && alternatives.iter().all(|alternative| match &alternative.body {
                    Guarded::Unconditional(body) => builds_safely(body),
                    Guarded::Guards(branches) => branches.iter().all(|branch| {
                        branch.guards.iter().all(|guard| is_discardable(guard.value()))
                            && builds_safely(&branch.body)
                    }),
                })
        }
        ExpressionKind::Foreign { foreign, .. } => foreign.is_effectful(),
        ExpressionKind::EffectEach { .. }
        | ExpressionKind::Apply { .. }
        | ExpressionKind::Local(_)
        | ExpressionKind::Function(_) => true,
        _ => false,
    }
}

fn chooses_only_pure(expression: &Expression) -> bool {
    match &expression.kind {
        ExpressionKind::EffectPure(_) => true,
        ExpressionKind::Let { body, .. } => chooses_only_pure(body),
        ExpressionKind::If { condition, then, otherwise } => {
            is_discardable(condition) && chooses_only_pure(then) && chooses_only_pure(otherwise)
        }
        ExpressionKind::Case { scrutinees, alternatives } => {
            scrutinees.iter().all(is_discardable)
                && alternatives.iter().all(|alternative| match &alternative.body {
                    Guarded::Unconditional(body) => chooses_only_pure(body),
                    Guarded::Guards(branches) => branches.iter().all(|branch| {
                        branch.guards.iter().all(|guard| is_discardable(guard.value()))
                            && chooses_only_pure(&branch.body)
                    }),
                })
        }
        _ => false,
    }
}

fn has_literal_label(arguments: &[Expression]) -> bool {
    let [label, _] = arguments else { return false };
    matches!(label.kind, ExpressionKind::Literal(Literal::String(_)))
}

impl Simplifier<'_> {
    fn sequences_unit_actions(&self, actions: &Expression) -> bool {
        let Monotype::Array(action) = *self.monotypes.get(actions.monotype) else { return false };
        self.monotypes
            .effect_result(action)
            .is_some_and(|result| matches!(self.monotypes.get(result), Monotype::Unit))
    }

    fn sequenced_unit_actions(
        &mut self,
        arguments: Vec<Expression>,
        monotype: crate::monotype::MonotypeId,
    ) -> Expression {
        let [actions] = <[Expression; 1]>::try_from(arguments)
            .unwrap_or_else(|_| unreachable!("invariant violated: a sequence has one argument"));
        let Monotype::Array(action) = *self.monotypes.get(actions.monotype) else {
            unreachable!("invariant violated: a sequence runs an array of actions")
        };
        let element = self.named_local("action", action);
        let kind = ExpressionKind::EffectEach {
            array: Box::new(actions),
            body: Box::new(element.expression()),
            element,
            results: Results::Collected,
        };
        Expression::new(kind, monotype)
    }
}
