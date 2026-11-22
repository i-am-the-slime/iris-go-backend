//! Rank-N values specialized at their instantiations.
//!
//! A value of a rank-N type is specialized into one function per instantiation
//! of its quantifiers, held in a record of them. Used at one instantiation it
//! is that function itself, a Go function type named after its newtype
//! (`type Count func(…)`), built from a function literal and called directly.
//! Used at several, it is a struct with a field per instantiation, named for
//! what tells the instantiations apart: `ForPosition` and `ForSurfaceAnim`
//! rather than the whole answer type spelled out in each.

use smol_str::SmolStr;

use super::{Emitter, field, field_name};
use crate::error::GoResult;
use crate::monotype::{Monotype, MonotypeId};
use crate::syntax::{GoExpression, GoType, StructField};

impl<Q> Emitter<'_, '_, '_, Q>
where
    Q: checking::ExternalQueries,
{
    /// The function a rank-N record holds when it has one instantiation.
    pub(super) fn single_instantiation(&self, record: MonotypeId) -> Option<MonotypeId> {
        if !self.monotypes.is_instantiated_record(record) {
            return None;
        }
        match self.monotypes.get(record) {
            Monotype::Record(fields) if fields.len() == 1 => Some(fields[0].monotype),
            _ => None,
        }
    }

    /// A record's Go type: its struct, or the named function type of its one
    /// instantiation.
    pub(super) fn record_go_type(&mut self, record: MonotypeId) -> GoResult<GoType> {
        match self.single_instantiation(record) {
            Some(instantiation) if !self.is_plain_function(instantiation) => {
                self.go_type(instantiation)
            }
            _ => Ok(GoType::Named(self.record_name(record)?)),
        }
    }

    /// What a record's type declaration declares: a function type for one
    /// instantiation, else a struct of the fields, ordered as a data type's slots
    /// are: pointers first and no padding between fields.
    pub(super) fn record_declaration(&mut self, record: MonotypeId) -> GoResult<GoType> {
        if let Some(instantiation) = self.single_instantiation(record) {
            return self.go_type(instantiation);
        }
        let Monotype::Record(fields) = self.monotypes.get(record).clone() else {
            unreachable!("invariant violated: a record declaration for a non-record")
        };
        let mut go_fields = Vec::with_capacity(fields.len());
        for record_field in fields.iter() {
            let name = self.record_field_name(record, &record_field.label);
            let label = crate::naming::renamed_label(&record_field.label, &name);
            let label = label.filter(|_| !self.monotypes.is_instantiated_record(record));
            let shape = self.value_shape(record_field.monotype)?;
            let type_ = self.go_type(record_field.monotype)?;
            go_fields.push((shape, StructField { name, type_, label }));
        }
        go_fields.sort_by_key(|(shape, _)| shape.declaration_rank());
        Ok(GoType::Struct(go_fields.into_iter().map(|(_, field)| field).collect()))
    }

    /// The Go field that holds a label of a record.
    /// Fields are [`crate::naming::go_fields`] of the record's labels, so that two labels with the
    /// same Go spelling, such as `"content-type"` and `content_type`, stay apart.
    pub(super) fn record_field_name(&self, record: MonotypeId, label: &str) -> String {
        let Monotype::Record(fields) = self.monotypes.get(record) else {
            return field_name(label);
        };
        let labels: Vec<&str> = fields.iter().map(|field| field.label.as_str()).collect();
        let position = labels.iter().position(|&known| known == label);
        let position = position.expect("invariant violated: a record's label exists");
        if self.monotypes.is_instantiated_record(record) {
            return instantiation_field_names(&labels).swap_remove(position);
        }
        crate::naming::go_fields(&labels).swap_remove(position)
    }

    /// The field `label` of a record value.
    pub(super) fn read_field(
        &self,
        value: GoExpression,
        record: MonotypeId,
        label: &str,
    ) -> GoExpression {
        if self.single_instantiation(record).is_some() {
            return value;
        }
        field(value, &self.record_field_name(record, label))
    }

    /// A record value of the given fields, in the record's order.
    pub(super) fn record_value(
        &mut self,
        record: MonotypeId,
        values: Vec<(SmolStr, GoExpression)>,
    ) -> GoResult<GoExpression> {
        if self.single_instantiation(record).is_some() {
            let (_, value) = values.into_iter().next().expect("invariant violated: one field");
            return Ok(value);
        }
        let type_ = GoType::Named(self.record_name(record)?);
        let fields = values
            .into_iter()
            .map(|(label, value)| (Some(self.record_field_name(record, &label)), value))
            .collect();
        Ok(GoExpression::Composite { type_, fields })
    }

    /// Whether a function type is a Go function type rather than a cell.
    fn is_plain_function(&mut self, monotype: MonotypeId) -> bool {
        matches!(self.monotypes.get(monotype), Monotype::Function(..))
            && !self.has_closure_set(monotype)
    }
}

/// Each instantiation's field: `For` and the words of its label that the
/// labels do not all begin with, so that `RunParserStringPosition` beside
/// `RunParserStringChar` is `ForPosition`.
fn instantiation_field_names(labels: &[&str]) -> Vec<String> {
    let words: Vec<Vec<&str>> = labels.iter().map(|label| label_words(label)).collect();
    let shortest = words.iter().map(Vec::len).min().unwrap_or(0);
    let shared = (0..shortest)
        .take_while(|&index| words.iter().all(|label| label[index] == words[0][index]));
    // Every name keeps at least one word of its own.
    let shared = shared.count().min(shortest.saturating_sub(1));
    let shared = if labels.len() == 1 { 0 } else { shared };
    words.iter().map(|words| format!("For{}", field_name(&words[shared..].concat()))).collect()
}

/// A label's words: each starts at a capital letter, digits belonging to the
/// word before.
fn label_words(label: &str) -> Vec<&str> {
    let mut words = vec![];
    let mut start = 0;
    for (index, character) in label.char_indices() {
        if index > start && character.is_uppercase() {
            words.push(&label[start..index]);
            start = index;
        }
    }
    if start < label.len() {
        words.push(&label[start..]);
    }
    words
}

#[cfg(test)]
mod tests {
    use super::instantiation_field_names;

    #[test]
    fn instantiations_are_named_by_what_tells_them_apart() {
        let labels = ["RunParserStringStateTIdentityPosition", "RunParserStringStateTIdentityChar"];
        assert_eq!(instantiation_field_names(&labels), ["ForPosition", "ForChar"]);
    }

    #[test]
    fn a_label_that_begins_another_keeps_a_word() {
        assert_eq!(
            instantiation_field_names(&["StepInt", "StepIntArray"]),
            ["ForInt", "ForIntArray"]
        );
    }

    #[test]
    fn labels_without_shared_words_are_named_whole() {
        assert_eq!(
            instantiation_field_names(&["Boolean", "StepInt"]),
            ["ForBoolean", "ForStepInt"]
        );
    }
}
