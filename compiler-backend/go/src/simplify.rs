//! Inlining and local rewrites over the monomorphic tree. Specialization leaves
//! long chains of tiny functions behind (class members delegating to other
//! members and foreign imports); inlining them exposes the effect primitives and
//! operators that code generation turns into plain Go.

use std::collections::hash_map::Entry;

use rustc_hash::{FxHashMap, FxHashSet};

use crate::foreign::{Boundary, Foreign, LineCoverage};
use crate::graph::{on_cycles, strongly_connected};
use crate::monomorphic::traversal::{
    for_each_binder_mut, for_each_child_mut, prune_unreachable, reference_graph, visit,
};
use crate::monomorphic::{
    Alternative, Binding, Expression, ExpressionKind, Function, FunctionId, Guard, Guarded,
    GuardedBranch, Literal, Local, LocalId, PATTERN_MATCH_FAILURE, Pattern, PatternKind, Program,
    RecordUpdate, Results, SourcePosition,
};
use crate::monotype::{Monotype, MonotypeId, Monotypes};
use crate::naming::{is_vague, is_vaguely_spelled};
use crate::purity::{
    KnownFunctions, can_fail, captures_free, captures_reference, does_no_work, is_cheap,
    is_deferrable, is_discardable, is_foreign_wrapper, is_trivial, is_within_size, mentions_any,
    occurrences_up_to, only_called, runs_any_effect, runs_effect, size,
};
use crate::suspension::Suspension;
use crate::timing::timed;
use smol_str::SmolStr;

use self::arguments::ArgumentSpecializations;
use self::call_patterns::CallPatternCopies;
use self::coverage::{binds_only, decided_guards, reachable};
use self::fold::shares_branch_with_next;

mod arguments;
mod call_patterns;
mod choice;
mod coerced;
mod constants;
mod coverage;
mod effects;
mod find;
mod fold;
mod lengths;
mod object;
mod population_count;
mod record;
mod record_views;
mod reductions;
mod rename;
mod shared_calls;
mod short_circuit;
mod sink;
mod tail_choices;
mod thaw;
mod three_way;
mod traversals;
mod uncons;
mod unpack;
mod views;

const INLINE_SIZE: usize = 40;

const OWN_FUNCTION_SIZE: usize = 120;

/// The size of a function that returns a closure copied to each of its calls.
const CLOSURE_RESULT_SIZE: usize = 160;

/// The size of a local helper that is copied to each of its calls whatever it works on.
const TINY_HELPER: usize = 12;

/// The size of a loop body a function is still inlined with at more than one call.
const COPIED_LOOP_BODY: usize = 8;

/// The names simplification and specialization give the values they introduce.
const MADE_UP_NAMES: &[&str] = &["argument", "binding", "element", "field", "scrutinee", "value"];
const INLINE_FUEL: usize = 2_000;

pub fn simplify(
    program: Program,
    monotypes: &mut Monotypes,
    next_local: u32,
    thunk_parameters: FxHashSet<LocalId>,
    coverage: Option<LineCoverage>,
    calls_kept: &FxHashSet<FunctionId>,
) -> Program {
    let suspension = Suspension::analyse(&program, monotypes);
    let Program { functions, entry } = program;
    let entry_file = functions[entry.0 as usize].origin;
    let entry_file = entry_file.filter(|_| coverage == Some(LineCoverage::Every));
    let references = reference_graph(&functions);
    let components = strongly_connected(&references);
    let recursive = on_cycles(&references, &components);
    let mut uses = vec![0usize; functions.len()];
    for function in &functions {
        visit(&function.body, &mut |node| {
            if let ExpressionKind::Function(id) = node.kind {
                uses[id.0 as usize] += 1;
            }
        });
    }
    let sizes = functions.iter().map(|function| size(&function.body)).collect();
    let mut simplifier = Simplifier {
        sizes,
        functions: functions.into_iter().map(Some).collect(),
        recursive,
        uses,
        entry,
        next_local,
        fuel: 0,
        monotypes,
        record_orders: FxHashMap::default(),
        narrowed_records: FxHashMap::default(),
        record_views: FxHashMap::default(),
        view_fields: FxHashSet::default(),
        records_settled: false,
        suspension,
        unsafely_effectful_locals: FxHashSet::default(),
        thunk_parameters,
        names: FxHashMap::default(),
        copies: FxHashSet::default(),
        forwarded: FxHashMap::default(),
        argument_specializations: ArgumentSpecializations::default(),
        call_pattern_copies: CallPatternCopies::default(),
        appenders: FxHashSet::default(),
        evaluated_constants: FxHashMap::default(),
        stores_built: false,
        source_ranks: SourceRanks { entry: entry_file, home: None },
        calls_kept: calls_kept.clone(),
    };
    for component in &components {
        for &function in component {
            let mut current = simplifier.functions[function]
                .take()
                .expect("invariant violated: function simplified twice");
            simplifier.source_ranks.home = current.origin.filter(|_| entry_file.is_some());
            simplifier.fuel = INLINE_FUEL;
            current = simplifier.eta_expand(current);
            current.body = simplifier.expression(current.body);
            if let [only] = component.as_slice()
                && simplifier.recursive[*only]
                && let Some(counted) = population_count::population_count(
                    &current,
                    FunctionId(*only as u32),
                    simplifier.monotypes,
                )
            {
                current.body = counted;
                simplifier.recursive[*only] = false;
            }
            current = simplifier.absorb_lambdas(current);
            simplifier.adopt_names(&mut current);
            simplifier.sizes[function] = size(&current.body);
            simplifier.functions[function] = Some(current);
        }
    }
    simplifier.records_settled = true;
    simplifier.fuel = 0;
    for index in 0..simplifier.functions.len() {
        let mut current = simplifier.functions[index]
            .take()
            .expect("invariant violated: function lost during simplification");
        simplifier.sequence_folds(&mut current.body);
        simplifier.settle_records(&mut current.body);
        simplifier.sink_lets(&mut current.body);
        simplifier.share_repeated_calls(&mut current.body);
        thaw::thaw_fresh_arrays_in_place(&mut current.body, simplifier.monotypes);
        simplifier.sizes[index] = size(&current.body);
        simplifier.functions[index] = Some(current);
    }
    let functions: Vec<Function> = simplifier
        .functions
        .into_iter()
        .map(|function| function.expect("invariant violated: function lost during simplification"))
        .collect();
    let next_local = simplifier.next_local;
    let mut program = Program { functions, entry };
    if coverage == Some(LineCoverage::Every) {
        crate::call_sites::attribute_inlined_code_to_call_sites(&mut program);
    }
    let program =
        timed("lift", || crate::lift::lift_local_functions(program, monotypes, next_local));
    let program = timed("prune", || prune(program.functions, entry));
    tail_choices::branch_tail_calls(program)
}

struct Simplifier<'m> {
    /// The functions called rather than copied into their callers: the map operations that
    /// [`crate::maps`] lets a Go map do, which the emitter recognises by their calls.
    calls_kept: FxHashSet<FunctionId>,
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
    /// Records bound by an update or a coercion, which a coercion that widens them again
    /// reads through.
    narrowed_records: FxHashMap<LocalId, Expression>,
    record_views: FxHashMap<LocalId, Expression>,
    view_fields: FxHashSet<LocalId>,
    records_settled: bool,
    suspension: Suspension,
    unsafely_effectful_locals: FxHashSet<LocalId>,
    /// The parameters of the lambdas the source writes as thunks, `\_ -> later`: what their
    /// bodies build waits for the thunk to be called, so it stays inside them unless it is free.
    thunk_parameters: FxHashSet<LocalId>,
    /// The names that locals take over from the aliases substituted for them: `argv <- args`
    /// binds `argv` to what `args` names after its type, `array`, and the Go variable is `argv`.
    names: FxHashMap<LocalId, AdoptedName>,
    copies: FxHashSet<LocalId>,
    forwarded: FxHashMap<LocalId, LocalId>,
    argument_specializations: ArgumentSpecializations,
    call_pattern_copies: CallPatternCopies,
    /// The locals bound to the appender a traversal threads: `append values x` is `snoc values x`,
    /// which a loop that owns the values extends in place.
    appenders: FxHashSet<LocalId>,
    /// What calls with constant arguments evaluated to at compile time, when that is a constant.
    evaluated_constants:
        FxHashMap<(FunctionId, Vec<Expression>, Option<SmolStr>), Option<Expression>>,
    /// Whether the call being simplified is an element of an array literal, whose value is
    /// stored rather than taken apart.
    stores_built: bool,
    source_ranks: SourceRanks,
}

struct SourceRanks {
    entry: Option<files::FileId>,
    home: Option<files::FileId>,
}

impl SourceRanks {
    fn rank(&self, position: Option<SourcePosition>) -> u8 {
        let Some(position) = position else { return 0 };
        if Some(position.file) == self.entry {
            2
        } else if Some(position.file) == self.home {
            1
        } else {
            0
        }
    }

    fn outranks(&self, position: Option<SourcePosition>, other: Option<SourcePosition>) -> bool {
        self.rank(position) > self.rank(other)
    }

    fn ranks_any(&self) -> bool {
        self.entry.is_some()
    }
}

#[derive(Debug, Clone)]
struct AdoptedName {
    name: SmolStr,
    written_here: bool,
}

impl Simplifier<'_> {
    /// Notes that `alias` is replaced by `value`: a local `value` whose name the compiler made
    /// up takes the alias's name where that says what the value is. `argv <- args` binds `argv`
    /// to what `args` names after its type, `array`, and the Go variable is `argv`.
    fn substituting_alias(&mut self, alias: &Local, value: &Expression) {
        let ExpressionKind::Local(mut target) = value.kind else { return };
        while let Some(&next) = self.forwarded.get(&target) {
            target = next;
        }
        self.forwarded.insert(alias.id, target);
        let own = AdoptedName {
            name: alias.name.clone(),
            written_here: !self.copies.contains(&alias.id),
        };
        let adopted = match self.names.get(&alias.id) {
            Some(_) if own.written_here && self.says_what_it_is(&own, alias.monotype) => own,
            Some(adopted) => adopted.clone(),
            None => own,
        };
        if !self.says_what_it_is(&adopted, alias.monotype) {
            return;
        }
        match self.names.entry(target) {
            Entry::Vacant(entry) => {
                entry.insert(adopted);
            }
            Entry::Occupied(mut entry) => {
                if adopted.written_here && !entry.get().written_here {
                    entry.insert(adopted);
                }
            }
        }
    }

    /// Whether a local's name is one the compiler gives a value nothing else names: after its
    /// type, or after the part it plays.
    fn is_made_up(&self, name: &str, monotype: MonotypeId) -> bool {
        name == self.monotypes.value_name(monotype) || MADE_UP_NAMES.contains(&name)
    }

    fn says_what_it_is(&self, adopted: &AdoptedName, monotype: MonotypeId) -> bool {
        let vague = match adopted.written_here {
            true => is_vaguely_spelled(&adopted.name),
            false => is_vague(&adopted.name),
        };
        !vague && !self.is_made_up(&adopted.name, monotype)
    }

    /// Renames the function's locals whose names say little after the aliases that were
    /// substituted for them.
    fn adopt_names(&mut self, function: &mut Function) {
        if self.names.is_empty() {
            return;
        }
        let names = std::mem::take(&mut self.names);
        let mut rename = |local: &mut Local| {
            let Some(adopted) = names.get(&local.id) else { return };
            let copied = self.copies.contains(&local.id);
            if self.is_made_up(&local.name, local.monotype) || (adopted.written_here && copied) {
                local.name = adopted.name.clone();
            }
        };
        function.parameters.iter_mut().for_each(&mut rename);
        for_each_binder_mut(&mut function.body, &mut rename);
        self.names = names;
    }

    fn fresh(&mut self, local: &Local) -> Local {
        Local::fresh(&mut self.next_local, local.name.clone(), local.monotype)
    }

    fn inlinable(&self, id: FunctionId) -> Option<&Function> {
        if id == self.entry || self.recursive[id.0 as usize] || self.keeps_calls(id) {
            return None;
        }
        let function = self.functions[id.0 as usize].as_ref()?;
        // A JSON reader carries Yoga.JSON's whole reader as its slow path: it is called, the
        // way a Go program calls `json.Unmarshal`, wherever it is used.
        if matches!(
            function.body.kind,
            ExpressionKind::Foreign { foreign: Foreign::Json(crate::foreign::JsonCodec::Read), .. }
        ) {
            return None;
        }
        let once = self.uses[id.0 as usize] == 1 && !self.stands_on_its_own(id, function);
        // A copy of a failure saves no work, only adds another place to fail; a copy of a loop
        // saves only a call, and repeats the whole loop at every call.
        // A function that answers with a constructor holding a closure, such as `Right` of the
        // record builder a decoder composes field by field, is copied up to a larger size: at its
        // call the closure is applied and resolves. One that returns a function is not: an `Event`
        // is one, and most of the code that uses it builds more of them.
        let holds_closure = matches!(self.monotypes.get(function.result), Monotype::Data(_))
            && self.monotypes.holds_function(function.result);
        let limit = match holds_closure {
            true => CLOSURE_RESULT_SIZE,
            false => INLINE_SIZE,
        };
        let small = self.sizes[id.0 as usize] <= limit
            && !can_fail(&function.body)
            && !runs_own_loop(&function.body);
        ((small || once) && !function.parameters.is_empty() || is_trivial(&function.body))
            .then_some(function)
    }

    /// Whether a function called once stays a function of its own, as the programmer named it:
    /// one that is more than a few lines and works on plain values, such as `validRows` or a
    /// message's decoder. Copied into its caller it saves only a call, and the caller grows by
    /// the whole of it. A function that takes or returns a function, or a record or array of
    /// them such as a codec, is still copied, since its caller's lambdas then become plain code.
    fn stands_on_its_own(&self, id: FunctionId, function: &Function) -> bool {
        let size = self.sizes[id.0 as usize];
        let plain = |monotype: MonotypeId| !self.builds_functions(monotype, 2);
        // A large function that takes records of functions, such as a test runner's reporters,
        // stays one: only its result decides.
        let plain_parameter = |monotype: MonotypeId| match size > 2 * OWN_FUNCTION_SIZE {
            true => !self.monotypes.holds_function(monotype),
            false => plain(monotype),
        };
        size > OWN_FUNCTION_SIZE
            && function.parameters.iter().all(|parameter| plain_parameter(parameter.monotype))
            && plain(function.result)
    }

    /// A function that only looks a data type's constructor up in a table of text, as `show`
    /// of an enumeration does, called more than once with an argument whose constructor
    /// the call cannot tell, not even by choosing it: one function reads better than a copy of
    /// the table at every call, and Go inlines it itself.
    fn keeps_table_call(
        &self,
        id: FunctionId,
        function: &Function,
        arguments: &[Expression],
    ) -> bool {
        if self.uses[id.0 as usize] < 2 {
            return false;
        }
        let ExpressionKind::Case { scrutinees, alternatives } = &function.body.kind else {
            return false;
        };
        let [scrutinee] = scrutinees.as_slice() else { return false };
        let ExpressionKind::Local(looked_up) = scrutinee.kind else { return false };
        let Some(position) =
            function.parameters.iter().position(|parameter| parameter.id == looked_up)
        else {
            return false;
        };
        let text = |expression: &Expression| {
            matches!(expression.kind, ExpressionKind::Literal(Literal::String(_)))
        };
        let enumeration = match self.monotypes.get(scrutinee.monotype) {
            Monotype::Data(data) => self.monotypes.enumeration_size(data).is_some(),
            _ => false,
        };
        // Only text: a table of numbers or constructors, as `fromEnum`, is often looked up by
        // code that inlining goes on to decide.
        let table = alternatives.len() > 1
            && enumeration
            && alternatives.iter().all(|alternative| {
                matches!(&alternative.body, Guarded::Unconditional(body) if text(body))
            });
        let unknown = |argument: &Expression| {
            !matches!(
                argument.kind,
                ExpressionKind::Literal(_)
                    | ExpressionKind::Construct { .. }
                    | ExpressionKind::If { .. }
                    | ExpressionKind::Case { .. }
                    | ExpressionKind::Let { .. }
            )
        };
        table && arguments.get(position).is_some_and(unknown)
    }

    fn saturated_callback(&mut self, argument: Expression, binds: bool) -> Expression {
        let ExpressionKind::Function(id) = argument.kind else { return argument };
        let Some(function) = self.inlinable(id) else { return argument };
        let count = function.parameters.len();
        let wraps_foreign = is_foreign_wrapper(&function.parameters, &function.body);
        let bound_once = binds && count > 0 && self.uses[id.0 as usize] == 1;
        let templates: Vec<Local> = function.parameters.clone();
        if !(wraps_foreign || bound_once)
            || crate::arity::arrows(self.monotypes, argument.monotype) < count
        {
            return argument;
        }
        let mut parameters = vec![];
        let mut result = argument.monotype;
        for template in &templates {
            let Some((parameter, inner)) = self.monotypes.function_parts(result) else {
                return argument;
            };
            let name =
                if is_vague(&template.name) { "value".into() } else { template.name.clone() };
            let template = Local { id: LocalId(0), name, monotype: parameter };
            parameters.push(self.fresh(&template));
            result = inner;
        }
        let function = Expression::new(ExpressionKind::Function(id), argument.monotype);
        let arguments = parameters.iter().map(Local::expression).collect();
        let body = self.apply(function, arguments, result);
        Expression::new(
            ExpressionKind::Lambda { parameters, body: Box::new(body) },
            argument.monotype,
        )
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
        let names = self.remaining_parameter_names(&function.body);
        let mut parameters = vec![];
        let mut result = function.result;
        while let Some((argument, inner)) = self.monotypes.function_parts(result) {
            let name = names
                .get(parameters.len())
                .cloned()
                .unwrap_or_else(|| self.monotypes.value_name(argument));
            let template = Local { id: LocalId(0), name, monotype: argument };
            parameters.push(self.fresh(&template));
            result = inner;
        }
        let arguments = parameters.iter().map(Local::expression).collect();
        function.body = Expression::new(
            ExpressionKind::Apply { function: Box::new(function.body), arguments },
            result,
        );
        function.parameters = parameters;
        function.result = result;
        function
    }

    /// The names of the parameters a partial application of a known function
    /// has yet to be given.
    fn remaining_parameter_names(&self, body: &Expression) -> Vec<SmolStr> {
        let (id, given) = match &body.kind {
            ExpressionKind::Function(id) => (*id, 0),
            ExpressionKind::Apply { function: callee, arguments } => match callee.kind {
                ExpressionKind::Function(id) => (id, arguments.len()),
                _ => return vec![],
            },
            _ => return vec![],
        };
        let Some(callee) = self.functions.get(id.0 as usize).and_then(Option::as_ref) else {
            return vec![];
        };
        callee.parameters.iter().skip(given).map(|parameter| parameter.name.clone()).collect()
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
                && let Some(template) =
                    chosen_lambda_parameter(&function.body, self.monotypes).cloned()
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
        self.map_choices(expression, monotype, &mut |simplifier, chosen| {
            let ExpressionKind::Lambda { mut parameters, body } = chosen.kind else {
                unreachable!("invariant violated: only chosen lambdas take the parameter")
            };
            let first = parameters.remove(0);
            let body = substitute(*body, first.id, &parameter.expression(), simplifier.monotypes);
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
            ExpressionKind::If { condition, then, otherwise } => {
                let then = self.map_choices(*then, monotype, chosen);
                let otherwise = self.map_choices(*otherwise, monotype, chosen);
                if then == otherwise && is_discardable(&condition) {
                    return then;
                }
                if let Some(joined) =
                    self.joined_comparisons(&condition, &then, &otherwise, monotype)
                {
                    return joined;
                }
                if shares_branch_with_next(&condition, &then, &otherwise) {
                    return self.boolean_choice(*condition, then, otherwise, monotype);
                }
                let (then, otherwise) = (Box::new(then), Box::new(otherwise));
                ExpressionKind::If { condition, then, otherwise }
            }
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
                        Alternative {
                            patterns: alternative.patterns,
                            body,
                            position: alternative.position,
                        }
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
                let name = self.monotypes.value_name(argument.monotype);
                let template = Local { id: LocalId(0), name, monotype: argument.monotype };
                let local = self.fresh(&template);
                let reference = local.expression();
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
        let position = expression.position;
        let binds = matches!(expression.kind, ExpressionKind::Let { .. });
        let mut simplified = self.simplified(expression);
        if self.is_action(&simplified) && self.keeps_own_position(&simplified, position, binds) {
            return simplified;
        }
        self.locate_action_body(&mut simplified, position);
        simplified.replacing(position)
    }

    fn keeps_own_position(
        &self,
        simplified: &Expression,
        position: Option<SourcePosition>,
        binds: bool,
    ) -> bool {
        let ranks = &self.source_ranks;
        let continues = binds
            && simplified.position.is_some()
            && ranks.rank(simplified.position) >= ranks.rank(position);
        ranks.outranks(simplified.position, position) || (continues && ranks.ranks_any())
    }

    fn locate_action_body(&self, expression: &mut Expression, position: Option<SourcePosition>) {
        match &mut expression.kind {
            ExpressionKind::Lambda { body, .. }
                if self.is_action(body) && self.source_ranks.outranks(position, body.position) =>
            {
                body.position = position;
            }
            ExpressionKind::Coerce(inner) | ExpressionKind::Let { body: inner, .. } => {
                self.locate_action_body(inner, position)
            }
            _ => {}
        }
    }

    fn is_action(&self, expression: &Expression) -> bool {
        self.monotypes.effect_result(expression.monotype).is_some()
    }

    fn keeping_ranked_position(
        &self,
        mut action: Expression,
        position: Option<SourcePosition>,
    ) -> Expression {
        if self.source_ranks.outranks(position, action.position) {
            action.position = position;
        }
        action
    }

    fn simplified(&mut self, expression: Expression) -> Expression {
        let monotype = expression.monotype;
        let position = expression.position;
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
                    let mut body = function.body.clone();
                    self.rename(&mut body, &mut FxHashMap::default());
                    return self.expression(body);
                }
                ExpressionKind::Function(id)
            }
            ExpressionKind::Array(elements) => ExpressionKind::Array(
                elements
                    .into_iter()
                    .map(|element| {
                        // An element is stored, not taken apart: a builder called for one stays a call.
                        self.stores_built = matches!(element.kind, ExpressionKind::Apply { .. });
                        let element = self.expression(element);
                        self.stores_built = false;
                        element
                    })
                    .collect(),
            ),
            ExpressionKind::Closure { tag, captures } => ExpressionKind::Closure {
                tag,
                captures: captures.into_iter().map(|capture| self.expression(capture)).collect(),
            },
            ExpressionKind::Record(fields) => ExpressionKind::Record(
                fields.into_iter().map(|(label, value)| (label, self.expression(value))).collect(),
            ),
            ExpressionKind::Access { record, label } => {
                let record = self.expression(*record);
                return self.field_of(record, label, monotype);
            }
            ExpressionKind::Update { record, updates } => {
                let record = self.expression(*record);
                let updates = self.updates(updates);
                return self.updated_record(record, updates, monotype);
            }
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
                let iteration = match foreign {
                    Foreign::Call { boundary, .. } | Foreign::Perform { boundary, .. } => {
                        boundary.iteration
                    }
                    _ => None,
                };
                let iterates = iteration.is_some();
                let binds = iteration == Some(crate::foreign::Iteration::Bind);
                let arguments: Vec<Expression> = arguments
                    .into_iter()
                    .map(|argument| {
                        let argument = self.expression(argument);
                        if iterates { self.saturated_callback(argument, binds) } else { argument }
                    })
                    .collect();
                let arguments = match self.viewed_object_operation(foreign, arguments, monotype) {
                    Ok(read) => return read,
                    Err(arguments) => arguments,
                };
                return self.foreign(foreign, arguments, monotype);
            }
            ExpressionKind::Reuse { .. }
            | ExpressionKind::UniqueEdge { .. }
            | ExpressionKind::UniqueEdges { .. } => {
                unreachable!("invariant violated: cells are reused only after simplification")
            }
            ExpressionKind::Apply { function, arguments } => {
                let function = self.expression(*function);
                let arguments: Vec<Expression> =
                    arguments.into_iter().map(|argument| self.expression(argument)).collect();
                return self.apply(function, arguments, monotype);
            }
            ExpressionKind::Lambda { mut parameters, body } => {
                let mut body = self.expression(*body);
                while !matches!(body.kind, ExpressionKind::Lambda { .. })
                    && let Some(template) = chosen_lambda_parameter(&body, self.monotypes).cloned()
                {
                    let parameter = self.fresh(&template);
                    body = self.apply_chosen_lambdas(body, &parameter);
                    parameters.push(parameter);
                }
                if matches!(body.kind, ExpressionKind::Apply { .. })
                    && awaits_action(body.monotype, self.monotypes)
                    && is_deferrable(&body)
                    && let Some((argument, result)) = self.monotypes.function_parts(body.monotype)
                {
                    let name = self.monotypes.value_name(argument);
                    let parameter = self.fresh(&Local { id: LocalId(0), name, monotype: argument });
                    body = self.apply(body, vec![parameter.expression()], result);
                    parameters.push(parameter);
                }
                ExpressionKind::Lambda { parameters, body: Box::new(body) }
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
                let recursive =
                    bindings.iter().any(|binding| mentions_any(&binding.value, &bindings));
                let mut bindings = bindings;
                for binding in &mut bindings {
                    self.remember_record_order(binding);
                    self.remember_unsafely_effectful(binding);
                    if !recursive && occurrences_up_to(&body, binding.local.id, 2).total > 1 {
                        let placeholder =
                            Expression::new(ExpressionKind::Unit, binding.value.monotype);
                        let value = std::mem::replace(&mut binding.value, placeholder);
                        binding.value = self.shared_view(value);
                        self.remember_record_view(binding);
                    }
                }
                let body = self.expression(*body);
                return self.let_bindings(bindings, body);
            }
            ExpressionKind::If { condition, then, otherwise } => {
                let condition = self.expression(*condition);
                if let ExpressionKind::Literal(Literal::Boolean(value)) = condition.kind {
                    return self.expression(if value { *then } else { *otherwise });
                }
                let mut then = self.expression(*then);
                let mut otherwise = self.expression(*otherwise);
                if is_discardable(&condition) {
                    settle(&mut then, &condition, true);
                    settle(&mut otherwise, &condition, false);
                }
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
                        PatternKind::Variable(local)
                            if !self
                                .monotypes
                                .same_without_causes(local.monotype, value.monotype) =>
                        {
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
                    return choice_at_case(distributed, position);
                }
                if let [scrutinee] = scrutinees.as_slice()
                    && (self.is_constant_path(scrutinee) || is_built_record(scrutinee))
                    && let Some(fields) = destructured_fields(&alternatives)
                {
                    let bindings = fields
                        .into_iter()
                        .map(|(label, local)| Binding {
                            value: Expression::new(
                                ExpressionKind::Access {
                                    record: Box::new(scrutinee.clone()),
                                    label,
                                },
                                local.monotype,
                            ),
                            local,
                        })
                        .collect();
                    let Some(Alternative { body: Guarded::Unconditional(body), .. }) =
                        alternatives.into_iter().next()
                    else {
                        unreachable!("invariant violated: the one alternative was just matched")
                    };
                    let kind = ExpressionKind::Let { bindings, body: Box::new(body) };
                    return self.expression(Expression::new(kind, monotype));
                }
                let (bindings, scrutinees, alternatives) =
                    self.eliminate_columns(scrutinees, alternatives);
                let alternatives: Vec<Alternative> = reachable(alternatives)
                    .into_iter()
                    .map(|alternative| Alternative {
                        patterns: alternative.patterns,
                        body: self.guarded(alternative.body),
                        position: alternative.position,
                    })
                    .collect();
                // Guards decided by folding may leave an alternative that shadows the rest.
                let alternatives = reachable(alternatives);
                if let [scrutinee] = scrutinees.as_slice()
                    && let Some(chosen) = self.three_way_case(scrutinee, &alternatives, monotype)
                {
                    return self.let_bindings(bindings, chosen);
                }
                if let Some(found) = self.found_element(&scrutinees, &alternatives, monotype) {
                    return self.let_bindings(bindings, found);
                }
                if let Some(chosen) = self.enumeration_case(&scrutinees, &alternatives, monotype) {
                    return self.let_bindings(bindings, chosen);
                }
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
                if matches!(action.kind, ExpressionKind::Foreign { foreign, .. } if *foreign == crate::foreign::APPENDER)
                {
                    self.appenders.insert(local.id);
                }
                let body = self.expression(*body);
                if self.appenders.contains(&local.id)
                    && occurrences_up_to(&body, local.id, 1).total == 0
                {
                    return body;
                }
                return self.effect_bind(action, local, body, monotype);
            }
            ExpressionKind::EffectEach { array, element, body, results } => {
                let array = self.expression(*array);
                let body = self.expression(*body);
                if results == Results::Discarded && self.runs_each_of_literal(&array, &body) {
                    return self.each_of_literal(array, element, body, monotype);
                }
                ExpressionKind::EffectEach {
                    array: Box::new(array),
                    element,
                    body: Box::new(body),
                    results,
                }
            }
        };
        Expression::new(kind, monotype)
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
            Guarded::Guards(branches) => {
                let branches = branches
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
                    .collect();
                decided_guards(branches)
            }
        }
    }

    fn apply(
        &mut self,
        function: Expression,
        mut arguments: Vec<Expression>,
        monotype: crate::monotype::MonotypeId,
    ) -> Expression {
        let stored = std::mem::take(&mut self.stores_built);
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
            ExpressionKind::Foreign { foreign: Foreign::RunEffect, arguments: ref performed }
                if matches!(self.monotypes.get(monotype), Monotype::Effect(_))
                    && let [allocated] = performed.as_slice()
                    && let ExpressionKind::EffectBind { action, local, body } = &allocated.kind
                    && matches!(action.kind, ExpressionKind::Foreign { foreign, .. } if *foreign == crate::foreign::APPENDER)
                    && let ExpressionKind::EffectPure(value) = &body.kind =>
            {
                let (action, local) = ((**action).clone(), local.clone());
                let applied = self.apply((**value).clone(), arguments, monotype);
                self.effect_bind(action, local, applied, monotype)
            }
            ExpressionKind::Function(id) if self.fuel > 0 => {
                // A partial application inlines too: `beta` binds the given
                // arguments outside the lambda over the missing parameters.
                let inlined = self.inlinable(id).and_then(|function| {
                    (!function.parameters.is_empty()
                        && !self.keeps_table_call(id, function, &arguments))
                    .then(|| (function.parameters.clone(), function.body.clone()))
                });
                let inlined = match stored {
                    true => inlined,
                    false => inlined.or_else(|| self.evaluated_call(id, &arguments)),
                };
                let Some((parameters, body)) = inlined else {
                    if let Some(value) = self.evaluated_constant(id, &arguments, monotype) {
                        return value;
                    }
                    let arguments = match self.specialized_call(id, arguments, monotype) {
                        Ok(call) => return call,
                        Err(arguments) => arguments,
                    };
                    let arguments = match self.call_pattern_call(id, arguments, monotype) {
                        Ok(call) => return call,
                        Err(arguments) => arguments,
                    };
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
                let mut body = body;
                self.rename(&mut body, &mut renaming);
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
        for binding in &bindings {
            self.remember_record_order(binding);
            self.remember_unsafely_effectful(binding);
            self.pass_on_thunk_parameter(binding);
        }
        let (bindings, body) = self.substituted_constant_arrays(bindings, body);
        let body = self.expression(body);
        let result = self.let_bindings(bindings, body);
        self.apply(result, rest, monotype)
    }

    fn let_bindings(&mut self, bindings: Vec<Binding>, body: Expression) -> Expression {
        let mut body = body;
        let mut kept = vec![];
        let recursive = bindings.iter().any(|binding| mentions_any(&binding.value, &bindings));
        if !recursive
            && let Some(position) = bindings
                .iter()
                .position(|binding| matches!(binding.value.kind, ExpressionKind::Let { .. }))
        {
            return self.float_let(bindings, position, body);
        }
        if recursive {
            let (bindings, body) = self.specialize_local_calls(bindings, body);
            let (bindings, body) = self.specialize_call_patterns(bindings, body);
            let monotype = body.monotype;
            return Expression::new(
                ExpressionKind::Let { bindings, body: Box::new(body) },
                monotype,
            );
        }
        for binding in bindings.into_iter().rev() {
            // A cell helper's two uses are told from more.
            let helper = self.is_cell_helper(&binding.value);
            body = self.count_lengths_at_source(&binding, body);
            let uses = occurrences_up_to(&body, binding.local.id, if helper { 3 } else { 2 });
            // A record of trivial fields, such as a rank-N value's
            // specializations, is copied so that its field accesses resolve.
            let trivial_record = matches!(&binding.value.kind, ExpressionKind::Record(fields)
                if fields.iter().all(|(_, value)| is_trivial(value)));
            let substitutable = is_trivial(&binding.value)
                || matches!(binding.value.kind, ExpressionKind::Fail(_))
                || matches!(&binding.value.kind, ExpressionKind::EffectPure(value) if is_trivial(value))
                || trivial_record
                || self.is_constant_path(&binding.value)
                || self.is_coerced_record_read(&binding, &body)
                || constants::is_consumed_literal_array(&binding, &body, &self.sizes)
                || uses.total == 0
                || (uses.total == 1
                    && (uses.under_lambda == 0 || self.does_no_work(&binding.value)))
                || (helper && uses.total == 2 && uses.applied == 2);
            let named_choice = self.is_named_choice(&binding, &body);
            let materialized_at_each_use =
                (uses.total > 1 || uses.under_lambda > 0) && self.is_viewed_record(&binding.value);
            let view_field = uses.total > 0 && self.view_fields.contains(&binding.local.id);
            let substitutable =
                substitutable && !named_choice && !materialized_at_each_use && !view_field;
            let built_in_place = uses.total == 1
                && matches!(&body.kind, ExpressionKind::EffectBind { action, .. }
                    if matches!(action.kind, ExpressionKind::Local(id) if id == binding.local.id));
            if self.is_small_applied_lambda(&binding, &body)
                || self.is_coerced_helper(&binding, &body)
                || (self.is_closed_tiny_lambda(&binding.value)
                    && passed_whole_at_most_once(&body, binding.local.id))
            {
                body = self.inline_applied(body, &binding);
                body = self.expression(body);
            } else if substitutable && (built_in_place || !runs_effect(self, &binding.value)) {
                if uses.total > 0 {
                    self.substituting_alias(&binding.local, &binding.value);
                    body = substitute(body, binding.local.id, &binding.value, self.monotypes);
                    body = self.expression(body);
                }
            } else if unpack::unpackable(&binding, &body, self.monotypes) {
                body = self.unpack(binding, body);
            } else if views::viewable(&binding, &body) {
                body = self.view(binding, body);
            } else {
                // A lambda whose every call was evaluated is no longer needed.
                let called = occurrences_up_to(&body, binding.local.id, 1).total > 0;
                body = self.evaluated_local_calls(&binding, body);
                if !called || occurrences_up_to(&body, binding.local.id, 1).total > 0 {
                    kept.push(binding);
                }
            }
        }
        if kept.is_empty() {
            return body;
        }
        kept.reverse();
        let monotype = body.monotype;
        Expression::new(ExpressionKind::Let { bindings: kept, body: Box::new(body) }, monotype)
    }

    fn field_of(&mut self, record: Expression, label: SmolStr, monotype: MonotypeId) -> Expression {
        let record = match self.field_of_call(record, &label, monotype) {
            Ok(field) => return field,
            Err(record) => record,
        };
        if let Some(value) = self.constant_field(&record, &label)
            && (value.monotype == monotype || self.monotypes.function_parts(monotype).is_none())
        {
            return self.coerce(value, monotype);
        }
        let record = match self.read_through_coercion(record, &label, monotype) {
            Ok(read) => return read,
            Err(record) => record,
        };
        let record = match self.field_of_viewed_object(record, &label, monotype) {
            Ok(read) => return read,
            Err(record) => record,
        };
        project(record, label, monotype)
    }

    fn constant_field(&self, record: &Expression, label: &str) -> Option<Expression> {
        let ExpressionKind::Record(fields) = &self.constant_value(record)?.kind else {
            return None;
        };
        let (_, value) = fields.iter().find(|(field, _)| field == label)?;
        let value = self.constant_value(value)?;
        is_trivial(value).then(|| value.clone())
    }

    fn constant_value<'e>(&'e self, expression: &'e Expression) -> Option<&'e Expression> {
        match &expression.kind {
            ExpressionKind::Function(id) => {
                let function = self.functions[id.0 as usize].as_ref()?;
                if !function.parameters.is_empty() || self.recursive[id.0 as usize] {
                    return Some(expression);
                }
                self.constant_value(&function.body).or(Some(expression))
            }
            ExpressionKind::Coerce(value) => self.constant_value(value),
            ExpressionKind::Access { record, label } => {
                let ExpressionKind::Record(fields) = &self.constant_value(record)?.kind else {
                    return None;
                };
                let (_, value) = fields.iter().find(|(field, _)| field == label)?;
                self.constant_value(value)
            }
            ExpressionKind::Record(_) => Some(expression),
            _ if is_trivial(expression) => Some(expression),
            _ => None,
        }
    }

    fn is_constant_path(&self, expression: &Expression) -> bool {
        match &expression.kind {
            ExpressionKind::Access { record, .. } | ExpressionKind::Coerce(record) => {
                self.is_constant_path(record)
            }
            ExpressionKind::Function(id) => self.functions[id.0 as usize]
                .as_ref()
                .is_some_and(|function| function.parameters.is_empty()),
            _ => false,
        }
    }

    /// Whether a binding names an `if` or a `case` that its body uses once, other than as what
    /// it chooses on: Go assigns the choice to a variable either way, and the binding's name
    /// says what it holds, `discount` rather than `result`.
    fn is_named_choice(&self, binding: &Binding, body: &Expression) -> bool {
        let choice =
            matches!(binding.value.kind, ExpressionKind::If { .. } | ExpressionKind::Case { .. });
        choice
            && !is_vague(&binding.local.name)
            && !self.is_made_up(&binding.local.name, binding.local.monotype)
            && !matches!(self.monotypes.get(binding.local.monotype), Monotype::Unit)
            && !chooses_on(body, binding.local.id)
    }

    /// A small local function over a mutable array of its surroundings, such as a `where`
    /// helper that peeks with a default, is inlined at each of its calls when it is only ever
    /// called. Its accesses are then seen where it is called, next to the caller's own, so that
    /// accesses of the same indices share their bounds tests (emit/guards.rs). So is a tiny
    /// helper, `meanOf totals = totals.sum / totals.count`, which costs less copied than called
    /// with its arguments built for it. Any other helper stays one function.
    fn is_small_applied_lambda(&self, binding: &Binding, body: &Expression) -> bool {
        let ExpressionKind::Lambda { parameters, .. } = &binding.value.kind else { return false };
        let mutable = |monotype: &Monotype| matches!(monotype, Monotype::MutableArray(_));
        // The array may as well be passed, `peekOr0 index array`, when the helper only reads
        // it: a helper that writes a passed array stays a function over its slice.
        let passed_array =
            parameters.iter().any(|parameter| mutable(self.monotypes.get(parameter.monotype)));
        let over_mutable_array = captures_free(&binding.value, self.monotypes, mutable)
            || (passed_array && only_reads_arrays(&binding.value));
        let tiny = is_within_size(&binding.value, TINY_HELPER) && only_computes(&binding.value);
        let worth_copying = over_mutable_array || tiny;
        self.fuel > 0
            && is_within_size(&binding.value, INLINE_SIZE)
            && worth_copying
            && !can_fail(&binding.value)
            && !runs_any_effect(&binding.value)
            && only_called(body, binding.local.id, parameters.len())
    }

    /// A tiny lambda that captures nothing, such as a `where` helper `square n = n * n`, is
    /// copied wherever it is used, also where it is passed on: a function that takes it then
    /// sees which function it is, and is specialized for it.
    fn is_closed_tiny_lambda(&self, value: &Expression) -> bool {
        matches!(value.kind, ExpressionKind::Lambda { .. })
            && self.fuel > 0
            && is_within_size(value, TINY_HELPER)
            && only_computes(value)
            && !can_fail(value)
            && !runs_any_effect(value)
            && arguments::free_locals(value).is_empty()
    }

    /// The body with each call of the binding's lambda given a copy of the lambda with fresh
    /// binders.
    fn inline_applied(&mut self, mut body: Expression, binding: &Binding) -> Expression {
        if let ExpressionKind::Local(id) = body.kind
            && id == binding.local.id
        {
            let mut copy = binding.value.clone();
            self.rename(&mut copy, &mut FxHashMap::default());
            return copy;
        }
        for_each_child_mut(&mut body, &mut |child| {
            let taken =
                std::mem::replace(child, Expression::new(ExpressionKind::Unit, child.monotype));
            *child = self.inline_applied(taken, binding);
        });
        body
    }

    /// A small lambda that reads or writes a reference cell of its
    /// surroundings, which is inlined where it is called (never passed) at
    /// both of two uses. Inlined, it leaves the cell in one Go function, where
    /// the cell can stay a plain local (emit/references.rs); lifted, it would
    /// take the cell as a parameter and keep it in memory. A lambda passed as
    /// a value would become two closures that `unsafeRefEq` tells apart, and
    /// one that performs effects through `unsafePerformEffect` keeps them
    /// where JavaScript runs them.
    fn is_cell_helper(&self, value: &Expression) -> bool {
        matches!(value.kind, ExpressionKind::Lambda { .. })
            && is_within_size(value, INLINE_SIZE)
            && captures_reference(value, self.monotypes)
            && !can_fail(value)
            && !runs_any_effect(value)
    }

    /// A field of a record coerced to another record type is the field of the
    /// original, coerced. A coercion converts an erased field when it reads
    /// it, and `Data.Variant` reads a payload at a type only after checking
    /// the label that promises it.
    fn read_through_coercion(
        &mut self,
        record: Expression,
        label: &SmolStr,
        monotype: MonotypeId,
    ) -> Result<Expression, Expression> {
        let ExpressionKind::Coerce(source) = &record.kind else { return Err(record) };
        let (Monotype::Record(from), Monotype::Record(_)) =
            (self.monotypes.get(source.monotype), self.monotypes.get(record.monotype))
        else {
            return Err(record);
        };
        let Some(field) = from.iter().find(|field| field.label == *label) else {
            return Err(record);
        };
        let field_monotype = field.monotype;
        let ExpressionKind::Coerce(source) = record.kind else {
            unreachable!("invariant violated: the record was just matched as a coercion")
        };
        let read = project(*source, label.clone(), field_monotype);
        Ok(self.coerce(read, monotype))
    }

    /// A binding of a trivial record coerced to another record type, whose
    /// every use reads a field: each read converts only its own field.
    fn is_coerced_record_read(&self, binding: &Binding, body: &Expression) -> bool {
        let ExpressionKind::Coerce(source) = &binding.value.kind else { return false };
        is_trivial(source)
            && matches!(self.monotypes.get(source.monotype), Monotype::Record(_))
            && matches!(self.monotypes.get(binding.value.monotype), Monotype::Record(_))
            && unpack::only_read(binding, body, self.monotypes)
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
}

/// The first parameter of the lambdas that an expression chooses between, when
/// it does nothing else: its conditions, scrutinees and bindings are cheap and
/// cannot fail, so every application may repeat them instead of sharing the
/// chosen lambda.
fn chosen_lambda_parameter<'e>(
    expression: &'e Expression,
    monotypes: &Monotypes,
) -> Option<&'e Local> {
    match &expression.kind {
        ExpressionKind::Lambda { parameters, .. } => parameters.first(),
        ExpressionKind::Let { bindings, body } => {
            let one_shot = awaits_action(expression.monotype, monotypes);
            let repeatable = |value: &Expression| {
                is_cheap(value)
                    || matches!(value.kind, ExpressionKind::Lambda { .. })
                    || (one_shot && (is_deferrable(value) || builds_action(value, monotypes)))
            };
            bindings.iter().all(|binding| repeatable(&binding.value)).then_some(())?;
            chosen_lambda_parameter(body, monotypes)
        }
        ExpressionKind::If { condition, then, otherwise } => {
            is_cheap(condition).then_some(())?;
            chosen_lambda_parameter(otherwise, monotypes)?;
            chosen_lambda_parameter(then, monotypes)
        }
        ExpressionKind::Case { scrutinees, alternatives } => {
            scrutinees.iter().all(is_cheap).then_some(())?;
            let mut chosen = None;
            for alternative in alternatives {
                match &alternative.body {
                    Guarded::Unconditional(body) => {
                        chosen = chosen.or(Some(chosen_lambda_parameter(body, monotypes)?));
                    }
                    Guarded::Guards(branches) => {
                        for branch in branches {
                            let cheap = branch.guards.iter().all(|guard| is_cheap(guard.value()));
                            cheap.then_some(())?;
                            let lambda = chosen_lambda_parameter(&branch.body, monotypes)?;
                            chosen = chosen.or(Some(lambda));
                        }
                    }
                }
            }
            chosen
        }
        _ => None,
    }
}

fn destructured_fields(alternatives: &[Alternative]) -> Option<Vec<(SmolStr, Local)>> {
    let [Alternative { patterns, body: Guarded::Unconditional(_), .. }] = alternatives else {
        return None;
    };
    let [Pattern { kind: PatternKind::Record(fields), .. }] = patterns.as_slice() else {
        return None;
    };
    let mut bound = vec![];
    for (label, pattern) in fields {
        match &pattern.kind {
            PatternKind::Variable(local) => bound.push((label.clone(), local.clone())),
            PatternKind::Wildcard => {}
            _ => return None,
        }
    }
    Some(bound)
}

fn builds_action(value: &Expression, monotypes: &Monotypes) -> bool {
    matches!(monotypes.get(value.monotype), Monotype::Effect(_)) && !runs_any_effect(value)
}

fn awaits_action(monotype: MonotypeId, monotypes: &Monotypes) -> bool {
    monotypes
        .function_parts(monotype)
        .is_some_and(|(_, result)| matches!(monotypes.get(result), Monotype::Effect(_)))
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

impl KnownFunctions for Simplifier<'_> {
    fn known(&self, id: FunctionId) -> Option<&Function> {
        self.functions[id.0 as usize].as_ref()
    }

    fn is_recursive(&self, id: FunctionId) -> bool {
        self.recursive[id.0 as usize]
    }

    fn runs_effect_when_applied(&self, local: LocalId) -> bool {
        self.unsafely_effectful_locals.contains(&local)
    }
}

fn substitute(
    expression: Expression,
    local: LocalId,
    value: &Expression,
    monotypes: &Monotypes,
) -> Expression {
    let mut expression = expression;
    substitute_in_place(&mut expression, local, value, monotypes);
    expression
}

fn substitute_in_place(
    expression: &mut Expression,
    local: LocalId,
    value: &Expression,
    monotypes: &Monotypes,
) {
    if let ExpressionKind::Local(id) = expression.kind
        && id == local
    {
        // The reference may expect another representation of the same value,
        // as a newtype constructor's result does a recursive newtype.
        let monotype = expression.monotype;
        *expression = value.clone();
        if !monotypes.same_without_causes(expression.monotype, monotype) {
            let coerced =
                std::mem::replace(expression, Expression::new(ExpressionKind::Unit, monotype));
            expression.kind = ExpressionKind::Coerce(Box::new(coerced));
        }
        return;
    }
    for_each_child_mut(expression, &mut |child| {
        substitute_in_place(child, local, value, monotypes)
    });
}

/// Whether the local is passed on whole, not called, at most once. unsafeRefEq tells two copies
/// of a lambda apart, so a lambda passed on twice, `[ kitchen, garden, kitchen ]`, stays one
/// function that both places share.
fn passed_whole_at_most_once(body: &Expression, local: LocalId) -> bool {
    let uses = occurrences_up_to(body, local, usize::MAX);
    uses.total - uses.applied <= 1
}

/// Whether the expression only computes a value: it neither builds nor runs an action, nor
/// throws, so that a copy of it adds no effect and no failure.
fn only_computes(expression: &Expression) -> bool {
    let mut computes = true;
    visit(expression, &mut |node| {
        computes &= !matches!(
            node.kind,
            ExpressionKind::Foreign {
                foreign: Foreign::Throw | Foreign::Crash | Foreign::Perform { .. },
                ..
            } | ExpressionKind::EffectPure(_)
                | ExpressionKind::EffectBind { .. }
                | ExpressionKind::EffectEach { .. }
                | ExpressionKind::Fail(_)
        );
    });
    computes
}

/// Whether the expression runs a loop whose body it holds, more than `sum`'s `+` or `elem`'s
/// `==`: a copy of it repeats that body at every call. A loop over a callback it is passed or a
/// known function, or with a body of a few nodes, is copied so that it fuses where it is used.
fn runs_own_loop(expression: &Expression) -> bool {
    let holds_body = |body: &Expression| !is_within_size(body, COPIED_LOOP_BODY);
    let mut loops = false;
    visit(expression, &mut |node| {
        loops |= match &node.kind {
            ExpressionKind::Foreign {
                foreign: Foreign::Call { boundary: Boundary { iteration: Some(_), .. }, .. },
                arguments,
            } => arguments.first().is_some_and(|callback| {
                matches!(&callback.kind, ExpressionKind::Lambda { body, .. } if holds_body(body))
            }),
            ExpressionKind::EffectEach { body, .. } => holds_body(body),
            _ => false,
        };
    });
    loops
}

/// Whether every action the expression performs on a mutable array reads it.
fn only_reads_arrays(expression: &Expression) -> bool {
    let mut reads_only = true;
    visit(expression, &mut |node| {
        if let ExpressionKind::Foreign { foreign: Foreign::Perform { function, .. }, .. } =
            &node.kind
        {
            reads_only &=
                function.name.starts_with("Peek") || matches!(function.name, "Within" | "Length");
        }
    });
    reads_only
}

/// Whether `expression` chooses on `local`: an `if` on it, or a `case` of it.
fn chooses_on(expression: &Expression, local: LocalId) -> bool {
    let mut found = false;
    visit(expression, &mut |node| match &node.kind {
        ExpressionKind::If { condition, .. } => {
            found |= matches!(condition.kind, ExpressionKind::Local(id) if id == local)
        }
        ExpressionKind::Case { scrutinees, .. } => {
            found |= scrutinees
                .iter()
                .any(|scrutinee| matches!(scrutinee.kind, ExpressionKind::Local(id) if id == local))
        }
        // An enumeration's value compared with a constructor, as its derived `eq` is.
        ExpressionKind::Foreign {
            foreign:
                Foreign::Operator(crate::foreign::Operator::Compare(
                    crate::foreign::Comparison::Equal | crate::foreign::Comparison::NotEqual,
                )),
            arguments,
        } => {
            let is_local = |argument: &Expression| matches!(argument.kind, ExpressionKind::Local(id) if id == local);
            let is_constructor = |argument: &Expression| matches!(&argument.kind, ExpressionKind::Construct { arguments, .. } if arguments.is_empty());
            found |= matches!(arguments.as_slice(), [left, right]
                if is_local(left) && is_constructor(right) || is_constructor(left) && is_local(right));
        }
        _ => {}
    });
    found
}

/// Each test of `condition` within a branch that `condition` being `truth` leads to, as the
/// branch that `truth` takes: a discardable condition reads values that never change.
fn settle(expression: &mut Expression, condition: &Expression, truth: bool) {
    if let ExpressionKind::If { condition: tested, then, otherwise } = &mut expression.kind
        && **tested == *condition
    {
        let chosen = if truth { then } else { otherwise };
        let unit = Expression::new(ExpressionKind::Unit, chosen.monotype);
        *expression = std::mem::replace(chosen.as_mut(), unit);
        return settle(expression, condition, truth);
    }
    for_each_child_mut(expression, &mut |child| settle(child, condition, truth));
}

fn prune(functions: Vec<Function>, entry: FunctionId) -> Program {
    prune_unreachable(functions, entry).0
}

/// The case distributed into its scrutinee's choice, the choice under the lets the distribution
/// binds written where the case is, as the lets are: `index xs (length xs - 1)`'s bounds test is the
/// test of `case Array.last xs of`.
fn choice_at_case(mut distributed: Expression, position: Option<SourcePosition>) -> Expression {
    let mut choice = &mut distributed;
    while let ExpressionKind::Let { body, .. } = &mut choice.kind {
        choice = body;
    }
    choice.position = choice.position.or(position);
    distributed
}

/// A record literal whose fields can be read one by one: a case that takes it apart reads each
/// field it binds from the literal, and the others are dropped.
fn is_built_record(expression: &Expression) -> bool {
    matches!(&expression.kind, ExpressionKind::Record(fields)
        if fields.iter().all(|(_, value)| is_discardable(value)))
}

impl Simplifier<'_> {
    /// Whether calls of the function stay calls: it is neither copied into its callers nor
    /// specialised to their arguments.
    pub(super) fn keeps_calls(&self, id: FunctionId) -> bool {
        self.calls_kept.contains(&id)
    }
}
