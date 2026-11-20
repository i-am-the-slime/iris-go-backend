//! Go names for the records, data types and specializations a program
//! declares.
//!
//! A name is as short as it can be, and grows only to tell it apart from
//! another. A record is called after the synonym or newtype that declares it,
//! else after where it is used: the parameter or field it is passed in, the
//! constructor that wraps it, or the function that returns it. Data types and
//! specializations spell the records among their type arguments by those names.
//! Every name comes with a ladder of longer candidates, and only names that
//! collide climb theirs, so that a new type elsewhere renames nothing it does
//! not collide with.

use std::collections::BTreeSet;

use rustc_hash::{FxHashMap, FxHashSet};
use smol_str::SmolStr;

use indexing::IndexedTypeItemKind;

use super::packages::{SpelledPart, Spelling};
use super::{Emitter, identifier};
use crate::error::GoResult;
use crate::modules::Modules;
use crate::mono::FunctionSpelling;
use crate::monotype::{Monotype, MonotypeId, RecordField, supported};
use crate::naming::{capitalise, is_vague, ladder};

/// A piece of a name that spells types.
#[derive(Debug, Clone)]
pub(super) enum NamePart {
    Text(String),
    /// A record, spelled by its labels in the name's longest form.
    Record {
        monotype: MonotypeId,
        labels: String,
    },
    Stutter(String),
}

/// How a global is to be spelled once every record has its name.
#[derive(Debug, Clone)]
pub(super) enum PendingSpelling {
    Record(MonotypeId),
    Parts(Vec<NamePart>),
}

/// Where a record's name comes from, strongest first.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Source {
    /// A synonym or newtype whose right-hand side is the record itself.
    Declared,
    /// A synonym or newtype for another synonym of the record.
    Alias,
    /// A parameter or a record field of the record's type.
    Used,
    /// A data constructor whose one field the record is.
    Wrapped,
    /// A function that returns the record.
    Returned,
}

#[derive(Debug, Clone)]
struct Hint {
    source: Source,
    name: String,
    /// What the name is qualified by when it collides: the declaring module,
    /// or the function, record or data type it is used in.
    qualifier: Option<String>,
    /// A parameterised synonym's or newtype's name followed by its arguments,
    /// which tells its instantiations apart.
    instantiated: Option<Vec<NamePart>>,
}

/// A parameter's or field's name as a record's name, unless it is too vague
/// to say what the record is.
fn use_name(name: &str) -> Option<String> {
    let name = identifier(name);
    (!is_vague(&name)).then(|| capitalise(&name))
}

fn labels_name(fields: &[RecordField]) -> String {
    if fields.is_empty() {
        return "Empty".into();
    }
    fields.iter().map(|field| crate::naming::go_field(&field.label)).collect()
}

/// The hint a record takes its name from: the strongest, and among uses the
/// most frequent name, the first met on a tie.
fn chosen_hint<'h>(hints: &'h [Hint], labels: &str) -> Option<&'h Hint> {
    // A name from use replaces the labels only where it is shorter; a
    // declared name always does, being the program's own name for the type.
    let usable = |hint: &&Hint| hint.source <= Source::Alias || hint.name.len() < labels.len();
    let strongest = hints.iter().filter(usable).map(|hint| hint.source).min()?;
    let mut counts: Vec<(&Hint, usize)> = vec![];
    for hint in hints.iter().filter(|hint| hint.source == strongest).filter(usable) {
        match counts.iter_mut().find(|(counted, _)| counted.name == hint.name) {
            Some((_, count)) => *count += 1,
            None => counts.push((hint, 1)),
        }
    }
    let most = counts.iter().map(|&(_, count)| count).max()?;
    counts.into_iter().find(|&(_, count)| count == most).map(|(hint, _)| hint)
}

/// Up to two labels of a record that the other records wanting its name lack,
/// those most others lack first.
fn distinguishing_labels(own: &[RecordField], others: &[&[RecordField]]) -> Vec<String> {
    let mut lacking: Vec<(usize, &SmolStr)> = own
        .iter()
        .map(|field| {
            let lacking = others
                .iter()
                .filter(|other| !other.iter().any(|theirs| theirs.label == field.label))
                .count();
            (lacking, &field.label)
        })
        .filter(|&(lacking, _)| lacking > 0)
        .collect();
    lacking.sort_by(|left, right| right.0.cmp(&left.0).then_with(|| left.1.cmp(right.1)));
    lacking.into_iter().take(2).map(|(_, label)| crate::naming::go_field(label)).collect()
}

/// The types of up to `limit` fields that a record shares by label with
/// another record wanting its name, but not by type, in label order.
fn distinguishing_types(
    limit: usize,
    index: usize,
    others: &[usize],
    fields: &[std::sync::Arc<[RecordField]>],
    field_types: &[Vec<String>],
) -> Option<String> {
    let differing: Vec<&str> = fields[index]
        .iter()
        .zip(&field_types[index])
        .filter(|(field, type_name)| {
            others.iter().any(|&other| {
                fields[other].iter().zip(&field_types[other]).any(|(theirs, their_type)| {
                    theirs.label == field.label && their_type != *type_name
                })
            })
        })
        .map(|(_, type_name)| type_name.as_str())
        .take(limit)
        .collect();
    (!differing.is_empty()).then(|| differing.concat())
}

/// Parts spelled with records by `short`, or by their labels where it has none.
fn spell_parts(parts: &[NamePart], short: &FxHashMap<MonotypeId, String>) -> String {
    let spelled: String = parts
        .iter()
        .map(|part| match part {
            NamePart::Text(text) | NamePart::Stutter(text) => text.as_str(),
            NamePart::Record { monotype, labels } => short.get(monotype).unwrap_or(labels).as_str(),
        })
        .collect();
    identifier(&spelled)
}

impl<Q> Emitter<'_, '_, '_, Q>
where
    Q: checking::ExternalQueries,
{
    /// A fresh global whose spelling waits for the names of records.
    pub(super) fn pending_global(&mut self, full: String, pending: PendingSpelling) -> String {
        let name = self.global_name(Spelling::Base(full));
        self.pending_spellings.push((name.clone(), pending));
        name
    }

    /// The parts of a function's name, with its types' records as records.
    pub(super) fn function_parts(&mut self, name: &str) -> GoResult<Option<Vec<NamePart>>> {
        let Some(spelling) = self.monotypes.function_spellings.get(name).cloned() else {
            let Some(function) = name.strip_suffix(super::reuse::REUSING) else { return Ok(None) };
            let Some(mut parts) = self.function_parts(function)? else { return Ok(None) };
            parts.push(NamePart::Text(super::reuse::REUSING.into()));
            return Ok(Some(parts));
        };
        Ok(Some(match spelling {
            FunctionSpelling::Specialized { name, types } => {
                let mut parts = vec![NamePart::Text(name.to_string())];
                for &type_id in types.iter() {
                    self.type_parts(type_id, &mut parts)?;
                }
                parts
            }
            FunctionSpelling::Dispatch { closure } => {
                let mut parts = vec![NamePart::Text("run".into())];
                parts.extend(self.closure_parts(closure)?);
                parts
            }
            FunctionSpelling::Lifted { parent, local } => {
                let mut parts = match self.function_parts(&parent)? {
                    Some(parts) => parts,
                    None => vec![NamePart::Text(parent.to_string())],
                };
                parts.push(NamePart::Text(capitalise(&local)));
                parts
            }
        }))
    }

    /// The parts of a closed function type's name, as `closures` spells it:
    /// its newtype's, or its arrows' (`Int -> String` is `IntToString`).
    pub(super) fn closure_parts(&mut self, monotype: MonotypeId) -> GoResult<Vec<NamePart>> {
        if let Some(newtype) = self.monotypes.function_newtype(monotype).cloned() {
            return self.data_parts(&newtype);
        }
        let arity = self.arity(monotype);
        let (arguments, result) = self.leading_arrows(monotype, arity);
        let mut parts = vec![];
        for argument in arguments {
            if !self.is_unit(argument) {
                self.monotype_parts(argument, &mut parts)?;
            }
        }
        parts.push(NamePart::Text("To".into()));
        self.monotype_parts(result, &mut parts)?;
        Ok(parts)
    }

    fn monotype_parts(&mut self, monotype: MonotypeId, parts: &mut Vec<NamePart>) -> GoResult<()> {
        let text = |parts: &mut Vec<NamePart>, text: &str| parts.push(NamePart::Text(text.into()));
        match self.monotypes.get(monotype).clone() {
            Monotype::Int => text(parts, "Int"),
            Monotype::Number => text(parts, "Number"),
            Monotype::Boolean => text(parts, "Boolean"),
            Monotype::Char => text(parts, "Char"),
            Monotype::String => text(parts, "String"),
            Monotype::Unit => text(parts, "Unit"),
            Monotype::Array(element) => {
                text(parts, "Array");
                self.monotype_parts(element, parts)?;
            }
            Monotype::Effect(result) => {
                text(parts, "Effect");
                self.monotype_parts(result, parts)?;
            }
            Monotype::Lazy(value) => {
                text(parts, "Lazy");
                self.monotype_parts(value, parts)?;
            }
            Monotype::ConsList(element) => {
                text(parts, "ConsList");
                self.monotype_parts(element, parts)?;
            }
            Monotype::Record(fields) => {
                parts.push(NamePart::Record { monotype, labels: labels_name(&fields) });
            }
            Monotype::Data(data) | Monotype::Recursive(data) => {
                parts.extend(self.data_parts(&data)?)
            }
            Monotype::Function(..) => text(parts, "Function"),
            _ => text(parts, "Value"),
        }
        Ok(())
    }

    /// The parts of a data type's name: its own, then its arguments'.
    pub(super) fn data_parts(
        &mut self,
        data: &crate::monotype::DataType,
    ) -> GoResult<Vec<NamePart>> {
        let name = self.context.type_name(data.file_id, data.item)?.to_string();
        let mut parts = vec![NamePart::Text(name)];
        for &argument in data.arguments.iter() {
            self.type_parts(argument, &mut parts)?;
        }
        Ok(parts)
    }

    /// The parts of a type's spelling within a name, as `Context::type_suffix`
    /// spells it, but with each closed row as its record.
    pub(super) fn type_parts(
        &mut self,
        type_id: checking::TypeId,
        parts: &mut Vec<NamePart>,
    ) -> GoResult<()> {
        use checking::core::Type;
        let type_id = self.context.types.strip_annotations(type_id);
        match self.context.types.lookup(type_id).clone() {
            Type::Application(function, argument) => {
                self.type_parts(function, parts)?;
                if let Some(labels) = self.context.variant_labels(function, argument)? {
                    parts.push(NamePart::Text(labels));
                    return Ok(());
                }
                self.type_parts(argument, parts)?;
            }
            Type::Function(argument, result) => {
                parts.push(NamePart::Text("Fn".into()));
                self.type_parts(argument, parts)?;
                self.type_parts(result, parts)?;
            }
            Type::Row(_) => {
                let mut labels = String::new();
                self.context.type_suffix(type_id, &mut labels)?;
                match supported(self.monotypes.record(&mut self.context, type_id))? {
                    Some(monotype) => parts.push(NamePart::Record { monotype, labels }),
                    None => parts.push(NamePart::Text(labels)),
                }
            }
            _ => {
                let mut spelled = String::new();
                self.context.type_suffix(type_id, &mut spelled)?;
                parts.push(NamePart::Text(spelled));
            }
        }
        Ok(())
    }

    /// Spells every pending global among `declared`: a record by its ladder,
    /// and a name that mentions records by its parts, which each package
    /// spells with the names it gives those records.
    pub(super) fn spell_pending(
        &mut self,
        modules: &Modules,
        declared: &FxHashSet<String>,
    ) -> GoResult<()> {
        let pending: Vec<(String, PendingSpelling)> = std::mem::take(&mut self.pending_spellings)
            .into_iter()
            .filter(|(name, _)| declared.contains(name))
            .collect();
        let mut records: BTreeSet<MonotypeId> = BTreeSet::new();
        for (_, spelling) in &pending {
            match spelling {
                PendingSpelling::Record(monotype) => {
                    records.insert(*monotype);
                }
                PendingSpelling::Parts(parts) => {
                    records.extend(parts.iter().filter_map(|part| match part {
                        NamePart::Record { monotype, .. } => Some(*monotype),
                        NamePart::Text(_) | NamePart::Stutter(_) => None,
                    }));
                }
            }
        }
        let ladders = self.record_ladders(&records, modules)?;
        let record_ladders: FxHashMap<MonotypeId, Vec<String>> =
            records.into_iter().zip(ladders).collect();
        for (name, spelling) in pending {
            let spelling = match spelling {
                PendingSpelling::Record(monotype) => {
                    Spelling::Ladder(record_ladders[&monotype].clone())
                }
                PendingSpelling::Parts(parts) => {
                    let full = spell_parts(&parts, &FxHashMap::default());
                    let parts = parts
                        .into_iter()
                        .map(|part| match part {
                            NamePart::Text(text) => SpelledPart::Text(text),
                            NamePart::Stutter(text) => SpelledPart::Stutter(text),
                            NamePart::Record { monotype, .. } => SpelledPart::Record {
                                global: self.record_names.get(&monotype).cloned(),
                                name: record_ladders[&monotype][0].clone(),
                            },
                        })
                        .collect();
                    Spelling::Composed { parts, full }
                }
            };
            self.spellings.insert(name, spelling);
        }
        Ok(())
    }

    /// Each record's ladder: its name; a parameterised synonym's name with its
    /// arguments; the name qualified; the name with the labels, then with the
    /// field types, that set it apart from the records wanting the same name;
    /// its labels; and its labels with their types.
    fn record_ladders(
        &mut self,
        records: &BTreeSet<MonotypeId>,
        modules: &Modules,
    ) -> GoResult<Vec<Vec<String>>> {
        let hints = self.record_hints(records, modules)?;
        let fields: Vec<std::sync::Arc<[RecordField]>> = records
            .iter()
            .map(|&monotype| match self.monotypes.get(monotype) {
                Monotype::Record(fields) => fields.clone(),
                _ => unreachable!("invariant violated: a record name for a non-record"),
            })
            .collect();
        let chosen: Vec<Option<Hint>> = records
            .iter()
            .zip(&fields)
            .map(|(monotype, fields)| {
                let labels = labels_name(fields);
                hints.get(monotype).and_then(|hints| chosen_hint(hints, &labels)).cloned()
            })
            .collect();
        let (field_types, typed) = self.spelled_fields(records, &fields, &chosen)?;
        let first: Vec<String> = chosen
            .iter()
            .zip(&fields)
            .map(|(hint, fields)| match hint {
                Some(hint) => hint.name.clone(),
                None => labels_name(fields),
            })
            .collect();
        let short: FxHashMap<MonotypeId, String> =
            records.iter().copied().zip(first.iter().cloned()).collect();
        let mut wanting: FxHashMap<&str, Vec<usize>> = FxHashMap::default();
        for (index, name) in first.iter().enumerate() {
            wanting.entry(name.as_str()).or_default().push(index);
        }
        let mut ladders = vec![];
        for (index, hint) in chosen.iter().enumerate() {
            let others: Vec<usize> = wanting[first[index].as_str()]
                .iter()
                .copied()
                .filter(|&other| other != index)
                .collect();
            let other_fields: Vec<&[RecordField]> =
                others.iter().map(|&other| &*fields[other]).collect();
            let typed = typed[index].clone();
            let of_types = |limit: usize| {
                distinguishing_types(limit, index, &others, &fields, &field_types)
                    .map(|types| format!("{}Of{types}", first[index]))
            };
            let (of_two_types, of_types) = (of_types(2), of_types(usize::MAX));
            let labels = labels_name(&fields[index]);
            let candidates = match hint {
                Some(hint) => {
                    // A qualifier every record wanting the name shares tells none apart.
                    let qualifier = |other: usize| {
                        chosen[other].as_ref().and_then(|other| other.qualifier.as_ref())
                    };
                    let distinguishes =
                        others.iter().any(|&other| qualifier(other) != hint.qualifier.as_ref());
                    let qualified = hint
                        .qualifier
                        .as_ref()
                        .filter(|_| distinguishes)
                        .map(|qualifier| format!("{qualifier}{}", hint.name));
                    let with_labels = match distinguishing_labels(&fields[index], &other_fields)[..]
                    {
                        [] => None,
                        ref labels => Some(format!("{}With{}", hint.name, labels.concat())),
                    };
                    let instantiated =
                        hint.instantiated.as_ref().map(|parts| spell_parts(parts, &short));
                    vec![
                        Some(hint.name.clone()),
                        instantiated,
                        qualified,
                        with_labels,
                        of_two_types,
                        of_types,
                        Some(labels),
                        Some(typed),
                    ]
                }
                None => vec![Some(labels), of_two_types, of_types, Some(typed)],
            };
            let built = ladder(candidates.into_iter().flatten());
            ladders.push(built);
        }
        Ok(ladders)
    }

    /// Each record's field types, spelling records by their chosen names, and
    /// its labels each followed by its field's type.
    fn spelled_fields(
        &mut self,
        records: &BTreeSet<MonotypeId>,
        fields: &[std::sync::Arc<[RecordField]>],
        chosen: &[Option<Hint>],
    ) -> GoResult<(Vec<Vec<String>>, Vec<String>)> {
        let short: FxHashMap<MonotypeId, String> = records
            .iter()
            .zip(chosen.iter().zip(fields))
            .map(|(&monotype, (hint, fields))| match hint {
                Some(hint) => (monotype, hint.name.clone()),
                None => (monotype, labels_name(fields)),
            })
            .collect();
        let mut field_types = vec![];
        let mut typed = vec![];
        for fields in fields {
            let mut types = vec![];
            let mut spelled = String::new();
            for field in fields.iter() {
                let type_name = self.field_type_name(field.monotype, &short, 3)?;
                spelled.push_str(&crate::naming::go_field(&field.label));
                spelled.push_str(&type_name);
                types.push(type_name);
            }
            field_types.push(types);
            typed.push(spelled);
        }
        Ok((field_types, typed))
    }

    /// A field's type within a record's name, spelling records by `short`.
    fn field_type_name(
        &mut self,
        monotype: MonotypeId,
        short: &FxHashMap<MonotypeId, String>,
        depth: usize,
    ) -> GoResult<String> {
        if depth == 0 {
            return Ok(String::new());
        }
        let inner = |emitter: &mut Self, prefix: &str, inner: MonotypeId| -> GoResult<String> {
            Ok(format!("{prefix}{}", emitter.field_type_name(inner, short, depth - 1)?))
        };
        Ok(match self.monotypes.get(monotype).clone() {
            Monotype::Int => "Int".into(),
            Monotype::Number => "Number".into(),
            Monotype::Boolean => "Boolean".into(),
            Monotype::Char => "Char".into(),
            Monotype::String => "String".into(),
            Monotype::Unit => "Unit".into(),
            Monotype::Array(element) => inner(self, "Array", element)?,
            Monotype::Effect(result) => inner(self, "Effect", result)?,
            Monotype::Nullable(element) => inner(self, "Nullable", element)?,
            Monotype::Lazy(value) => inner(self, "Lazy", value)?,
            Monotype::ConsList(element) => inner(self, "ConsList", element)?,
            Monotype::Reference(value) => inner(self, "Ref", value)?,
            Monotype::Record(fields) => match short.get(&monotype) {
                Some(name) => name.clone(),
                None => labels_name(&fields),
            },
            Monotype::Function(argument, result) => {
                let argument = self.field_type_name(argument, short, depth - 1)?;
                let result = self.field_type_name(result, short, depth - 1)?;
                format!("Fn{argument}{result}")
            }
            Monotype::Data(data) | Monotype::Recursive(data) | Monotype::ForeignData(data) => {
                let mut parts = vec![NamePart::Text(
                    self.context.type_name(data.file_id, data.item)?.to_string(),
                )];
                for &argument in data.arguments.iter() {
                    self.type_parts(argument, &mut parts)?;
                }
                spell_parts(&parts, short)
            }
            _ => "Value".into(),
        })
    }

    /// What each record could be called, in the order met: declarations by
    /// module name, then uses in function order, then fields and constructors.
    fn record_hints(
        &mut self,
        records: &BTreeSet<MonotypeId>,
        modules: &Modules,
    ) -> GoResult<FxHashMap<MonotypeId, Vec<Hint>>> {
        let mut hints: FxHashMap<MonotypeId, Vec<Hint>> = FxHashMap::default();
        self.declared_hints(records, modules, &mut hints)?;
        let mut hint_record = |monotype: MonotypeId, hint: Hint| {
            if records.contains(&monotype) {
                hints.entry(monotype).or_default().push(hint);
            }
        };
        for function in &self.program.functions {
            let owner = match self.monotypes.function_spellings.get(&function.name) {
                Some(FunctionSpelling::Specialized { name, .. }) => name.to_string(),
                _ => function.name.to_string(),
            };
            let owner = identifier(&capitalise(&owner));
            for parameter in &function.parameters {
                if let Some(name) = use_name(&parameter.name) {
                    let qualifier = Some(owner.clone());
                    hint_record(
                        parameter.monotype,
                        Hint { source: Source::Used, name, qualifier, instantiated: None },
                    );
                }
            }
            let mut binders = FxHashMap::default();
            crate::lift::collect_binders(&function.body, &mut binders);
            let mut binders: Vec<_> = binders.into_values().collect();
            binders.sort_by_key(|binder| binder.id);
            for binder in binders {
                if let Some(name) = use_name(&binder.name) {
                    let qualifier = Some(owner.clone());
                    let hint = Hint { source: Source::Used, name, qualifier, instantiated: None };
                    hint_record(binder.monotype, hint);
                }
            }
            let result = self.monotypes.effect_result(function.result).unwrap_or(function.result);
            let name = format!("{owner}Result");
            hint_record(
                result,
                Hint { source: Source::Returned, name, qualifier: None, instantiated: None },
            );
        }
        let mut field_hints = vec![];
        for &record in records {
            let Monotype::Record(fields) = self.monotypes.get(record) else { continue };
            for field in fields.iter() {
                if let Some(name) = use_name(&field.label) {
                    field_hints.push((field.monotype, name, record));
                }
            }
        }
        for (monotype, name, record) in field_hints {
            let qualifier = hints.get(&record).and_then(|hints| {
                hints.iter().find(|hint| hint.source <= Source::Alias).map(|hint| hint.name.clone())
            });
            if records.contains(&monotype) {
                let hint = Hint { source: Source::Used, name, qualifier, instantiated: None };
                hints.entry(monotype).or_default().push(hint);
            }
        }
        let mut data: Vec<crate::monotype::DataType> = self.data_layouts.keys().cloned().collect();
        data.sort_by_key(|data| self.data_layouts[data].name.clone());
        // A constructor of a type generic over its field, such as `Just`, says
        // nothing about the record it holds.
        data.retain(|data| data.arguments.is_empty());
        for data in data {
            let Some(constructors) =
                supported(self.monotypes.constructors(&mut self.context, &data))?
            else {
                continue;
            };
            let type_name =
                capitalise(&identifier(&self.context.type_name(data.file_id, data.item)?));
            for constructor in constructors.iter() {
                if let [field] = constructor.fields[..]
                    && records.contains(&field)
                {
                    let name = crate::naming::go_field(&constructor.name);
                    let qualifier = Some(type_name.clone());
                    hints.entry(field).or_default().push(Hint {
                        source: Source::Wrapped,
                        name,
                        qualifier,
                        instantiated: None,
                    });
                }
            }
        }
        Ok(hints)
    }

    /// The synonyms and newtypes of the program's modules that stand for one
    /// of the records, by module name.
    fn declared_hints(
        &mut self,
        records: &BTreeSet<MonotypeId>,
        modules: &Modules,
        hints: &mut FxHashMap<MonotypeId, Vec<Hint>>,
    ) -> GoResult<()> {
        use checking::core::Type;
        let label_sets: FxHashSet<Vec<SmolStr>> = records
            .iter()
            .filter_map(|&monotype| match self.monotypes.get(monotype) {
                Monotype::Record(fields) => {
                    Some(fields.iter().map(|field| field.label.clone()).collect())
                }
                _ => None,
            })
            .collect();
        let mut erased_newtypes = std::mem::take(&mut self.monotypes.erased_newtypes);
        erased_newtypes.extend(std::mem::take(&mut self.context.erased_newtypes));
        for erased in erased_newtypes {
            let Some(record) = self.declared_record(erased.erased, &label_sets)? else { continue };
            let spelling = (erased.file_id, erased.item, erased.arguments);
            let spellings = self.monotypes.record_spellings.entry(record).or_default();
            if !spellings.contains(&spelling) {
                spellings.push(spelling);
            }
        }
        let mut ordered: Vec<_> = modules.indices().collect();
        ordered.sort_by(|left, right| modules.name(*left).cmp(modules.name(*right)));
        for module_index in ordered {
            let file_id = modules.file(module_index);
            let module = self.context.module(file_id)?;
            let qualifier =
                module.name.rsplit('.').next().map(|last| capitalise(&identifier(last)));
            let mut declared: Vec<(String, checking::TypeId, bool)> = vec![];
            for (item, indexed) in module.indexed.items.iter_types() {
                let Some(name) = indexed.name.as_ref() else { continue };
                match &indexed.kind {
                    IndexedTypeItemKind::Synonym { .. } => {
                        let Some(synonym) = module.checked.lookup_synonym(item) else { continue };
                        if !synonym.parameters.is_empty() {
                            continue;
                        }
                        let direct = self.is_record_type(synonym.expansion);
                        declared.push((name.to_string(), synonym.expansion, direct));
                    }
                    IndexedTypeItemKind::Newtype { .. } => {
                        let parameters = module.checked.lookup_data_declaration(item);
                        if parameters.is_none_or(|data| !data.type_parameters.is_empty()) {
                            continue;
                        }
                        let newtype =
                            self.context.queries.intern_type(Type::Constructor(file_id, item));
                        declared.push((name.to_string(), newtype, true));
                    }
                    _ => {}
                }
            }
            declared.sort_by(|left, right| left.0.cmp(&right.0));
            let applied = records.iter().flat_map(|&record| {
                let spellings = self.monotypes.record_spellings.get(&record);
                let spellings = spellings.into_iter().flatten();
                spellings
                    .filter(|(file, ..)| *file == file_id)
                    .map(move |(_, item, arguments)| (record, *item, arguments.clone()))
            });
            let applied: Vec<_> = applied.collect();
            for (record, item, arguments) in applied {
                let Some(name) = module.indexed.items[item].name.as_ref() else { continue };
                let source = match module.checked.lookup_synonym(item) {
                    Some(synonym) if !self.is_record_type(synonym.expansion) => Source::Alias,
                    _ => Source::Declared,
                };
                let name = capitalise(&identifier(name));
                let instantiated = if arguments.is_empty() {
                    None
                } else {
                    let mut instantiated = vec![NamePart::Text(name.clone())];
                    for &argument in arguments.iter() {
                        self.type_parts(argument, &mut instantiated)?;
                    }
                    Some(instantiated)
                };
                let hint = Hint { source, name, qualifier: qualifier.clone(), instantiated };
                hints.entry(record).or_default().push(hint);
            }
            for (name, expansion, direct) in declared {
                let Some(monotype) = self.declared_record(expansion, &label_sets)? else {
                    continue;
                };
                if !records.contains(&monotype) {
                    continue;
                }
                let source = if direct { Source::Declared } else { Source::Alias };
                let name = capitalise(&identifier(&name));
                let hint = Hint { source, name, qualifier: qualifier.clone(), instantiated: None };
                hints.entry(monotype).or_default().push(hint);
            }
        }
        Ok(())
    }

    /// Whether a type is spelled as a record, `{ … }` or `Record ( … )`.
    fn is_record_type(&mut self, type_id: checking::TypeId) -> bool {
        use checking::core::Type;
        let (head, _) = self.context.types.spine(type_id);
        let Type::Constructor(file_id, item) = self.context.types.lookup(head).clone() else {
            return false;
        };
        file_id == self.context.queries.prim_id()
            && self.context.type_name(file_id, item).is_ok_and(|name| name == "Record")
    }

    /// The record a declared type stands for, when its labels are those of
    /// a record being named; other declarations are not converted at all.
    fn declared_record(
        &mut self,
        type_id: checking::TypeId,
        label_sets: &FxHashSet<Vec<SmolStr>>,
    ) -> GoResult<Option<MonotypeId>> {
        use checking::core::Type;
        let expanded = crate::monotype::expand_synonyms(&mut self.context, type_id)?;
        let (head, arguments) = self.context.types.spine(expanded);
        let is_record = match self.context.types.lookup(head).clone() {
            Type::Constructor(file_id, item) => {
                file_id == self.context.queries.prim_id()
                    && self.context.type_name(file_id, item)? == "Record"
            }
            _ => false,
        };
        let labels: Option<Vec<SmolStr>> = match (is_record, arguments.first()) {
            (true, Some(&row)) => {
                let row = self.context.types.strip_annotations(row);
                match self.context.types.lookup(row).clone() {
                    Type::Row(row) => {
                        let row = self.context.queries.lookup_row_type(row).clone();
                        let mut labels: Vec<SmolStr> =
                            row.fields.iter().map(|field| field.label.clone()).collect();
                        labels.sort();
                        Some(labels)
                    }
                    _ => None,
                }
            }
            _ => None,
        };
        let newtype =
            matches!(self.context.types.lookup(head), Type::Constructor(..)) && !is_record;
        if !newtype && labels.is_none_or(|labels| !label_sets.contains(&labels)) {
            return Ok(None);
        }
        let converted = supported(self.monotypes.monotype(&mut self.context, type_id))?;
        Ok(converted
            .filter(|&monotype| matches!(self.monotypes.get(monotype), Monotype::Record(_))))
    }
}
