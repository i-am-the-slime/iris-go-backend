//! Batch type dump: the type oracle consumed by purs-backend-go.
//!
//! Loads a Spago workspace the way `iris watch` does, checks every module, and
//! writes a JSON map of `module -> [entry]`. A span entry is
//! `{ s: [line, col], e: [line, col], t: rendered, ty: tree }` for each
//! expression and binder the checker typed; positions are 1-based and columns
//! count code points, matching the source spans `purs` writes into CoreFn. An
//! alias entry is `{ newtype: [name, params, underlying] }` for each locally
//! declared newtype or synonym. The backend joins span entries onto CoreFn by
//! span to drive whole-program monomorphization.

use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;

use building::QueryEngine;
use checking::core::pretty::Pretty;
use checking::core::{Name, Type, TypeId};
use checking::{CheckedModule, PrettyQueries};
use files::FileId;
use indexing::{IndexedTermItemKind, IndexedTypeItemKind};
use iris_build::{BuildSession, BuildSessionConfig, ProjectConfig};
use line_index::{LineIndex, TextSize};
use serde_json::{Value, json};

pub struct DumpConfig {
    pub package: Option<String>,
    /// Where the Iris build writes JavaScript. Defaults to a temporary directory
    /// so the dump never overwrites the `purs` output the backend reads CoreFn from.
    pub build_output: Option<PathBuf>,
    pub destination: PathBuf,
    pub version: String,
}

pub fn run(config: DumpConfig) -> Result<(), String> {
    let scratch = tempfile::tempdir().map_err(|error| error.to_string())?;
    let build_output = config.build_output.unwrap_or_else(|| scratch.path().join("output"));
    let project = ProjectConfig { package: config.package, output: Some(build_output), quiet: true };
    let project = iris_build::prepare_project(project).map_err(|error| error.to_string())?;
    let project = iris_build::initialize_project(project).map_err(|error| error.to_string())?;
    let session_config =
        BuildSessionConfig { color: false, diagnostics: false, version: config.version };
    let session = BuildSession::new(project, session_config).map_err(|error| error.to_string())?;
    let snapshot = session.snapshot();
    let engine = &snapshot.engine;

    let module_names = module_names(engine, snapshot.files.keys().copied());
    eprintln!("dump-types: loaded {} files", snapshot.files.len());

    let mut output = serde_json::Map::new();
    let mut total = 0usize;
    for (&file_id, module_name) in &module_names {
        let Some(entries) = module_entries(engine, &module_names, file_id) else { continue };
        total += entries.len();
        output.insert(module_name.clone(), Value::Array(entries));
    }

    let modules = output.len();
    let json = serde_json::to_string(&Value::Object(output)).map_err(|error| error.to_string())?;
    fs::write(&config.destination, json).map_err(|error| error.to_string())?;
    eprintln!(
        "dump-types: wrote {modules} modules, {total} typed expression nodes -> {}",
        config.destination.display()
    );
    Ok(())
}

fn module_names(
    engine: &QueryEngine,
    files: impl Iterator<Item = FileId>,
) -> HashMap<FileId, String> {
    files
        .filter_map(|file_id| {
            let content = engine.content(file_id).ok()?;
            let (parsed, _) = engine.parsed(file_id).ok()?;
            Some((file_id, parsed.module_name(&content)?.to_string()))
        })
        .collect()
}

fn module_entries(
    engine: &QueryEngine,
    module_names: &HashMap<FileId, String>,
    file_id: FileId,
) -> Option<Vec<Value>> {
    let stabilized = engine.stabilized(file_id).ok()?;
    let checked = engine.checked(file_id).ok()?;
    let content = engine.content(file_id).ok()?;
    let lines = engine.line_index(file_id).ok()?;
    let types = TypeJson { engine, checked: &checked, module_names };
    let positions = Positions { content: &content, lines: &lines };

    let expressions = checked.node_types.expressions.iter().filter_map(|(id, &type_id)| {
        Some((stabilized.syntax_ptr(*id)?.text_range(), type_id))
    });
    // Binders matter as much as expressions: CoreFn lowers `f (Just x) = …` to a
    // lambda over a synthetic scrutinee with no source span, so the pattern is
    // the only type source for that match. Binder and expression spans never
    // collide, so both share one span map.
    let binders = checked.node_types.binders.iter().filter_map(|(id, &type_id)| {
        Some((stabilized.syntax_ptr(*id)?.text_range(), type_id))
    });

    let mut entries: Vec<Value> = expressions
        .chain(binders)
        .filter_map(|(range, type_id)| {
            let (start, end) =
                positions.span(u32::from(range.start()), u32::from(range.end()))?;
            let rendered = Pretty::new(engine, &checked).render(type_id).ok()?;
            Some(json!({ "s": start, "e": end, "t": rendered.as_str(), "ty": types.tree(type_id) }))
        })
        .collect();

    if let Ok(indexed) = engine.indexed(file_id) {
        entries.extend(newtype_aliases(engine, &types, &indexed, file_id));
        entries.extend(synonym_aliases(&types, &indexed));
    }
    Some(entries)
}

/// One alias entry per locally declared newtype. Monomorphization erases a
/// newtype to its underlying type, but docs.json carries that type only when the
/// constructor is exported; the constructor's checked type
/// `forall vars. Underlying -> Head args` always does.
fn newtype_aliases(
    engine: &QueryEngine,
    types: &TypeJson,
    indexed: &indexing::IndexedModule,
    file_id: FileId,
) -> Vec<Value> {
    indexed
        .items
        .iter_terms()
        .filter_map(|(term_id, item)| {
            let IndexedTermItemKind::Constructor { .. } = &item.kind else { return None };
            let constructor = types.checked.lookup_term_item_type(term_id)?;
            let Type::Function(underlying, result) = *engine.lookup_type(peel(engine, constructor))
            else {
                return None;
            };
            let (head, arguments) = head_arguments(engine, result);
            let Type::Constructor(head_file, head_item) = *engine.lookup_type(head) else {
                return None;
            };
            let head_item = &indexed.items[head_item];
            if head_file != file_id || !matches!(head_item.kind, IndexedTypeItemKind::Newtype { .. })
            {
                return None;
            }
            let parameters: Vec<String> =
                arguments.iter().map(|&argument| types.parameter_name(argument)).collect();
            Some(json!({
                "newtype": [head_item.name.as_ref()?.as_str(), parameters, types.tree(underlying)]
            }))
        })
        .collect()
}

/// One alias entry per locally declared synonym, shaped like a newtype entry. A
/// non-exported synonym is absent from docs.json, so without this the backend
/// cannot expand it during specialization.
fn synonym_aliases(types: &TypeJson, indexed: &indexing::IndexedModule) -> Vec<Value> {
    indexed
        .items
        .iter_types()
        .filter_map(|(type_id, item)| {
            let IndexedTypeItemKind::Synonym { .. } = &item.kind else { return None };
            let synonym = types.checked.lookup_synonym(type_id)?;
            let parameters: Vec<String> =
                synonym.parameters.iter().map(|binder| types.name_text(binder.name)).collect();
            Some(json!({
                "newtype": [item.name.as_ref()?.as_str(), parameters, types.tree(synonym.expansion)]
            }))
        })
        .collect()
}

/// Strips quantifiers, constraints and kind annotations off a constructor type.
fn peel(engine: &QueryEngine, mut type_id: TypeId) -> TypeId {
    loop {
        match *engine.lookup_type(type_id) {
            Type::Forall(_, inner)
            | Type::Constrained(_, inner)
            | Type::ConstraintOrigin(inner, _)
            | Type::Kinded(inner, _) => type_id = inner,
            _ => return type_id,
        }
    }
}

/// Splits `Head a b c` into its head and the arguments applied to it. The
/// arguments, not the constructor's foralls, are the type parameters: foralls
/// also bind kinds (`ReaderT`'s leading `k`), which would break the alias arity.
fn head_arguments(engine: &QueryEngine, mut type_id: TypeId) -> (TypeId, Vec<TypeId>) {
    let mut arguments = vec![];
    loop {
        match *engine.lookup_type(type_id) {
            Type::Application(function, argument) => {
                arguments.push(argument);
                type_id = function;
            }
            Type::Kinded(inner, _) | Type::KindApplication(inner, _) => type_id = inner,
            _ => break,
        }
    }
    arguments.reverse();
    (type_id, arguments)
}

struct Positions<'a> {
    content: &'a str,
    lines: &'a LineIndex,
}

impl Positions<'_> {
    /// A 1-based `[line, column]` pair per end, with columns in code points. CST
    /// ranges include leading trivia, so the start skips whitespace to land on
    /// the token `purs` records in CoreFn; ends already agree.
    fn span(&self, start: u32, end: u32) -> Option<([u32; 2], [u32; 2])> {
        let start = self.skip_whitespace(start, end);
        Some((self.position(start)?, self.position(end)?))
    }

    fn skip_whitespace(&self, mut start: u32, end: u32) -> u32 {
        let bytes = self.content.as_bytes();
        while start < end && matches!(bytes.get(start as usize), Some(b' ' | b'\t' | b'\n' | b'\r'))
        {
            start += 1;
        }
        start
    }

    fn position(&self, offset: u32) -> Option<[u32; 2]> {
        let line_col = self.lines.line_col(TextSize::new(offset));
        let line = &self.content[self.lines.line(line_col.line)?];
        let column = line.get(..line_col.col as usize)?.chars().count() as u32;
        Some([line_col.line + 1, column + 1])
    }
}

struct TypeJson<'a> {
    engine: &'a QueryEngine,
    checked: &'a CheckedModule,
    module_names: &'a HashMap<FileId, String>,
}

impl TypeJson<'_> {
    /// A tagged JSON tree the backend parses into its `PsType`. Kinds are
    /// dropped and constraints unwrapped; only shapes that carry to Go types are
    /// modelled precisely.
    fn tree(&self, type_id: TypeId) -> Value {
        match *self.engine.lookup_type(type_id) {
            Type::Application(function, argument) => {
                json!({ "app": [self.tree(function), self.tree(argument)] })
            }
            Type::Function(argument, result) => {
                json!({ "fn": [self.tree(argument), self.tree(result)] })
            }
            Type::Forall(binder, inner) => {
                let binder = self.engine.lookup_forall_binder(binder);
                json!({ "forall": [self.name_text(binder.name), self.tree(inner)] })
            }
            Type::Constrained(_, inner) | Type::Kinded(inner, _) => self.tree(inner),
            Type::ConstraintOrigin(constraint, _) => self.tree(constraint),
            Type::KindApplication(function, _) => self.tree(function),
            Type::Constructor(file_id, item) | Type::Synonym(file_id, item) => {
                json!({ "ctor": [self.module_name(file_id), self.item_name(file_id, item)] })
            }
            Type::Integer(value) => json!({ "int": value }),
            Type::String(_, literal) => {
                let text = self.engine.lookup_string_literal(literal).to_utf8().unwrap_or_default();
                json!({ "str": text })
            }
            Type::Row(row) => self.row(row),
            Type::Rigid(name, _, _) => json!({ "var": self.name_text(name) }),
            // A unification variable still unsolved after zonking is a position
            // nothing constrains — a parameter a generic body never had to name.
            // Generalising it to a synthetic variable lets the backend treat it as
            // parametric rather than as unresolved residue.
            Type::Unification(id) => json!({ "var": format!("u{id}") }),
            Type::Free(text) => json!({ "free": self.engine.lookup_smol_str(text).as_str() }),
            Type::Unknown(text) => json!({ "unknown": self.engine.lookup_smol_str(text).as_str() }),
        }
    }

    /// A closed row dumps its label-sorted fields so the backend can rebuild a
    /// record shape; an open row names no single shape.
    fn row(&self, row: checking::core::RowTypeId) -> Value {
        let row = self.engine.lookup_row_type(row);
        if row.tail.is_some() {
            return json!({ "row": true });
        }
        let fields: Vec<Value> =
            row.fields.iter().map(|field| json!([field.label.as_str(), self.tree(field.id)])).collect();
        json!({ "row": fields })
    }

    fn parameter_name(&self, type_id: TypeId) -> String {
        match *self.engine.lookup_type(type_id) {
            Type::Rigid(name, _, _) => self.name_text(name),
            _ => Pretty::new(self.engine, self.checked)
                .render(type_id)
                .map(|rendered| rendered.to_string())
                .unwrap_or_default(),
        }
    }

    /// A type variable's source text, falling back to its raw identity.
    fn name_text(&self, name: Name) -> String {
        match self.checked.lookup_name(name) {
            Some(text) => self.engine.lookup_smol_str(text).to_string(),
            None => name.as_text().to_string(),
        }
    }

    fn module_name(&self, file_id: FileId) -> String {
        self.module_names.get(&file_id).cloned().unwrap_or_default()
    }

    fn item_name(&self, file_id: FileId, item: indexing::TypeItemId) -> String {
        self.engine
            .indexed(file_id)
            .ok()
            .and_then(|indexed| indexed.items[item].name.as_ref().map(|name| name.to_string()))
            .unwrap_or_default()
    }
}
