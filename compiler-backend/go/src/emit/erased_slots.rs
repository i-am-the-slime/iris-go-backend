use rustc_hash::{FxHashMap, FxHashSet};

use super::{Emitter, is_untyped_constant};
use crate::error::GoResult;
use crate::monomorphic::traversal::for_each_child;
use crate::monomorphic::{Expression, ExpressionKind, Program};
use crate::monotype::{Monotype, MonotypeId};
use crate::syntax::GoExpression;

#[derive(Default)]
struct Crossings {
    entering: FxHashMap<MonotypeId, Vec<MonotypeId>>,
    leaving: FxHashMap<MonotypeId, Vec<MonotypeId>>,
    shared: FxHashSet<MonotypeId>,
}

#[derive(Clone, Copy)]
enum Side {
    Slot(MonotypeId),
    Erased,
    Typed,
}

impl<'q, Q> Emitter<'_, '_, 'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn find_typed_slots(
        &mut self,
        program: &Program,
    ) -> GoResult<FxHashSet<MonotypeId>> {
        let mut crossings = Crossings::default();
        for function in &program.functions {
            self.count_crossings_in(&function.body, &mut crossings)?;
        }
        let Crossings { entering, leaving, shared } = crossings;
        let slots: FxHashSet<MonotypeId> = entering.keys().chain(leaving.keys()).copied().collect();
        let mut kept = FxHashSet::default();
        for slot in slots {
            if shared.contains(&slot) {
                continue;
            }
            let entering = entering.get(&slot).map_or(&[][..], Vec::as_slice);
            let leaving = leaving.get(&slot).map_or(&[][..], Vec::as_slice);
            if self.agree(entering, leaving) {
                kept.insert(slot);
            }
        }
        Ok(kept)
    }

    fn agree(&self, entering: &[MonotypeId], leaving: &[MonotypeId]) -> bool {
        let Some(&asked) = leaving.first() else { return true };
        entering
            .iter()
            .chain(leaving)
            .all(|&typed| self.monotypes.same_without_causes(typed, asked))
    }

    fn count_crossings_in(
        &mut self,
        expression: &Expression,
        crossings: &mut Crossings,
    ) -> GoResult<()> {
        match &expression.kind {
            ExpressionKind::Coerce(value) => {
                let mut visited = FxHashSet::default();
                self.count_crossing(value.monotype, expression.monotype, crossings, &mut visited)?;
            }
            ExpressionKind::Foreign { arguments, .. } => {
                for argument in arguments {
                    self.share_slots_within(argument.monotype, crossings)?;
                }
                self.share_slots_within(expression.monotype, crossings)?;
            }
            _ => {}
        }
        let mut result = Ok(());
        for_each_child(expression, &mut |child| {
            if result.is_ok() {
                result = self.count_crossings_in(child, crossings);
            }
        });
        result
    }

    fn count_crossing(
        &mut self,
        from: MonotypeId,
        to: MonotypeId,
        crossings: &mut Crossings,
        visited: &mut FxHashSet<(MonotypeId, MonotypeId)>,
    ) -> GoResult<()> {
        if self.monotypes.same_without_causes(from, to) || !visited.insert((from, to)) {
            return Ok(());
        }
        match (self.side(from)?, self.side(to)?) {
            (Side::Typed, Side::Slot(slot)) => {
                crossings.entering.entry(slot).or_default().push(from);
                Ok(())
            }
            (Side::Slot(slot), Side::Typed) => {
                crossings.leaving.entry(slot).or_default().push(to);
                Ok(())
            }
            (Side::Typed, Side::Typed) => self.count_typed_crossing(from, to, crossings, visited),
            _ => {
                self.share_slots_within(from, crossings)?;
                self.share_slots_within(to, crossings)
            }
        }
    }

    fn count_typed_crossing(
        &mut self,
        from: MonotypeId,
        to: MonotypeId,
        crossings: &mut Crossings,
        visited: &mut FxHashSet<(MonotypeId, MonotypeId)>,
    ) -> GoResult<()> {
        match (self.monotypes.get(from).clone(), self.monotypes.get(to).clone()) {
            (
                Monotype::Function(from_argument, from_result),
                Monotype::Function(to_argument, to_result),
            ) => {
                self.count_crossing(to_argument, from_argument, crossings, visited)?;
                self.count_crossing(from_result, to_result, crossings, visited)
            }
            (Monotype::Record(from_fields), Monotype::Record(to_fields))
                if to_fields.iter().all(|to_field| {
                    from_fields.iter().any(|from_field| from_field.label == to_field.label)
                }) =>
            {
                for to_field in to_fields.iter() {
                    let from_field = from_fields
                        .iter()
                        .find(|from_field| from_field.label == to_field.label)
                        .expect("invariant violated: the source has every field just checked");
                    self.count_crossing(
                        from_field.monotype,
                        to_field.monotype,
                        crossings,
                        visited,
                    )?;
                }
                Ok(())
            }
            (from_monotype, to_monotype)
                if std::mem::discriminant(&from_monotype)
                    == std::mem::discriminant(&to_monotype)
                    && let (Some(from_element), Some(to_element)) =
                        (from_monotype.element(), to_monotype.element()) =>
            {
                self.count_crossing(from_element, to_element, crossings, visited)
            }
            _ => {
                self.share_slots_within(from, crossings)?;
                self.share_slots_within(to, crossings)
            }
        }
    }

    fn side(&mut self, monotype: MonotypeId) -> GoResult<Side> {
        match self.monotypes.get(monotype).clone() {
            Monotype::Opaque | Monotype::Erased(_) => Ok(Side::Erased),
            Monotype::Recursive(data) if self.is_uninhabited(&data)? => Ok(Side::Slot(monotype)),
            _ => Ok(Side::Typed),
        }
    }

    fn share_slots_within(
        &mut self,
        monotype: MonotypeId,
        crossings: &mut Crossings,
    ) -> GoResult<()> {
        let mut visited = FxHashSet::default();
        let mut pending = vec![monotype];
        while let Some(monotype) = pending.pop() {
            if !visited.insert(monotype) {
                continue;
            }
            match self.monotypes.get(monotype).clone() {
                Monotype::Function(argument, result) => pending.extend([argument, result]),
                Monotype::Record(fields) => {
                    pending.extend(fields.iter().map(|field| field.monotype));
                }
                Monotype::Recursive(data) if self.is_uninhabited(&data)? => {
                    crossings.shared.insert(monotype);
                }
                Monotype::Recursive(data) => pending.push(self.unfold(&data)?),
                Monotype::Data(data) => {
                    let constructors = self
                        .monotypes
                        .constructors(&mut self.context, &data)
                        .map_err(crate::monotype::Failure::in_code_generation)?;
                    for constructor in constructors.iter() {
                        pending.extend(constructor.fields.iter().copied());
                    }
                }
                other => pending.extend(other.element()),
            }
        }
        Ok(())
    }
}

impl<'q, Q> Emitter<'_, '_, 'q, Q>
where
    Q: checking::ExternalQueries,
{
    pub(super) fn held_as_it_is(
        &mut self,
        value: GoExpression,
        from: MonotypeId,
        to: MonotypeId,
    ) -> GoResult<Result<GoExpression, GoExpression>> {
        if self.typed_slots.contains(&to) && matches!(self.side(from)?, Side::Typed) {
            if is_untyped_constant(&value) {
                let type_ = self.go_type(from)?;
                return Ok(Ok(GoExpression::Conversion { type_, value: Box::new(value) }));
            }
            return Ok(Ok(value));
        }
        if self.typed_slots.contains(&from) && matches!(self.side(to)?, Side::Typed) {
            let type_ = self.go_type(to)?;
            return Ok(Ok(GoExpression::TypeAssertion { value: Box::new(value), type_ }));
        }
        Ok(Err(value))
    }
}
