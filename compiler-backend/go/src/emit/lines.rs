//! `//line` directives, so that Go's stack traces, debuggers and profiles name the PureScript a
//! piece of generated code comes from. The emitter puts a directive in front of the statements
//! each expression with a known position becomes, where they call a function or can fail: only
//! such code shows up in a trace or a profile, and the passes after emission see through fewer
//! directives. The printer leaves out the ones that repeat the line before and names the
//! enclosing line again after a nested block that named another. [`LineCoverage::Every`] names
//! every statement instead, for tools that map each Go line to its source.

use std::sync::Arc;

use files::FileId;
use indexing::{IndexedTermItemKind, IndexedTypeItemKind};
use std::collections::VecDeque;

use rustc_hash::{FxHashMap, FxHashSet};

use super::Emitter;
use crate::error::GoResult;
use crate::foreign::LineCoverage;
use crate::mono::SourcePosition;
use crate::monotype::{DataConstructor, DataType};
use crate::syntax::{GoDeclaration, GoExpression, GoStatement, SourceLine};
use crate::walk::{self, Walk};

/// The sources positions are resolved in, by file: none for a file the program's messages do not
/// show, such as a built-in module's.
#[derive(Default)]
pub(super) struct SourceLines {
    files: FxHashMap<FileId, Option<SourceFile>>,
}

#[derive(Default)]
pub(super) struct Spans {
    enclosing: Option<SourceLine>,
    by_text: FxHashMap<String, Vec<Span>>,
}

struct Span {
    enclosing: SourceLine,
    line: SourceLine,
}

struct SourceFile {
    path: Arc<str>,
    content: Arc<str>,
    /// The offset each line starts at.
    line_starts: Vec<u32>,
}

impl<Q> Emitter<'_, '_, '_, Q>
where
    Q: checking::ExternalQueries,
{
    /// Attributes the statements `out` gained from `start` on to where `position` is written,
    /// unless they begin with a directive of their own; with [`LineCoverage::Every`], each of
    /// them and of the blocks in them that no more specific position names already.
    pub(super) fn attribute(
        &mut self,
        position: Option<SourcePosition>,
        start: usize,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        let Some(directives) = &self.foreign_packages.line_directives else { return Ok(()) };
        let every = directives.coverage == LineCoverage::Every;
        let Some(position) = position else { return Ok(()) };
        if every {
            if let Some(line) = self.source_line(position)? {
                attribute_every(&line, &mut out[start..]);
                attribute_unnamed(&line, start, out);
            }
            return Ok(());
        }
        if out.get(start).is_none_or(|first| matches!(first, GoStatement::Line(_)))
            || !does_work(&mut out[start..])
        {
            return Ok(());
        }
        if let Some(line) = self.source_line(position)? {
            out.insert(start, GoStatement::Line(line));
        }
        Ok(())
    }

    pub(super) fn name_definition(
        &mut self,
        position: Option<SourcePosition>,
        body: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        let Some(directives) = &self.foreign_packages.line_directives else { return Ok(()) };
        if directives.coverage != LineCoverage::Every {
            return Ok(());
        }
        let Some(position) = position else { return Ok(()) };
        if let Some(line) = self.source_line(position)? {
            body.insert(0, GoStatement::Line(line));
        }
        Ok(())
    }

    pub(super) fn span_line(
        &mut self,
        position: Option<SourcePosition>,
    ) -> GoResult<Option<SourceLine>> {
        let Some(directives) = &self.foreign_packages.line_directives else { return Ok(None) };
        if directives.coverage != LineCoverage::Every {
            return Ok(None);
        }
        let Some(position) = position else { return Ok(None) };
        self.source_line(position)
    }

    pub(super) fn branch_line(
        &mut self,
        position: Option<SourcePosition>,
    ) -> GoResult<Option<SourceLine>> {
        let Some(line) = self.span_line(position)? else { return Ok(None) };
        let enclosing = match &self.spans.enclosing {
            Some(enclosing) => Some(enclosing.clone()),
            None => {
                let function = self.current.map(|id| self.program.function(id));
                let position =
                    function.and_then(|function| function.body.position.or(function.position));
                self.span_line(position)?
            }
        };
        Ok(enclosing.filter(|enclosing| enclosing.path == line.path).map(|_| line))
    }

    pub(super) fn data_line(&mut self, data: &DataType) -> GoResult<Option<SourceLine>> {
        let Some(directives) = &self.foreign_packages.line_directives else { return Ok(None) };
        if directives.coverage != LineCoverage::Every {
            return Ok(None);
        }
        let module = self.context.module(data.file_id)?;
        let pointer = match &module.indexed.items[data.item].kind {
            IndexedTypeItemKind::Data { equation: Some(equation), .. } => {
                module.stabilized.syntax_ptr(*equation)
            }
            IndexedTypeItemKind::Newtype { equation: Some(equation), .. } => {
                module.stabilized.syntax_ptr(*equation)
            }
            _ => None,
        };
        let Some(pointer) = pointer else { return Ok(None) };
        let offset = u32::from(pointer.text_range().start());
        self.source_line(SourcePosition { file: data.file_id, offset })
    }

    pub(super) fn nullary_line(
        &mut self,
        data: &DataType,
        constructor: usize,
    ) -> GoResult<Option<SourceLine>> {
        let Some(directives) = &self.foreign_packages.line_directives else { return Ok(None) };
        if directives.coverage != LineCoverage::Every {
            return Ok(None);
        }
        let name = self.data_layout(data)?.name;
        let constructors = self
            .monotypes
            .constructors(&mut self.context, data)
            .map_err(|failure| failure.at(&name))?;
        self.constructor_line(data, &constructors[constructor])
    }

    pub(super) fn constructor_line(
        &mut self,
        data: &DataType,
        constructor: &DataConstructor,
    ) -> GoResult<Option<SourceLine>> {
        let Some(directives) = &self.foreign_packages.line_directives else { return Ok(None) };
        if directives.coverage != LineCoverage::Every {
            return Ok(None);
        }
        let Some(term) = constructor.term else { return Ok(None) };
        let module = self.context.module(data.file_id)?;
        let IndexedTermItemKind::Constructor { id, .. } = module.indexed.items[term].kind else {
            return Ok(None);
        };
        let Some(pointer) = module.stabilized.syntax_ptr(id) else { return Ok(None) };
        let offset = u32::from(pointer.text_range().start());
        self.source_line(SourcePosition { file: data.file_id, offset })
    }

    fn source_line(&mut self, position: SourcePosition) -> GoResult<Option<SourceLine>> {
        if !self.source_lines.files.contains_key(&position.file) {
            let file = self.source_file(position.file)?;
            self.source_lines.files.insert(position.file, file);
        }
        let Some(Some(file)) = self.source_lines.files.get(&position.file) else { return Ok(None) };
        Ok(Some(file.line(position.offset)))
    }

    fn source_file(&mut self, file_id: FileId) -> GoResult<Option<SourceFile>> {
        let Some(directives) = &self.foreign_packages.line_directives else { return Ok(None) };
        let Some((_, path)) = directives.sources.iter().find(|(id, _)| *id == file_id) else {
            return Ok(None);
        };
        let path = Arc::from(path.as_str());
        let content = self.context.queries.content(file_id)?;
        let line_starts = std::iter::once(0)
            .chain(content.match_indices('\n').map(|(at, _)| at as u32 + 1))
            .collect();
        Ok(Some(SourceFile { path, content, line_starts }))
    }
}

impl SourceFile {
    /// The line and byte column, from 1, of the first character at or after `offset`: a syntax
    /// node starts at the whitespace in front of it.
    fn line(&self, offset: u32) -> SourceLine {
        let start = (offset as usize).min(self.content.len());
        let rest = &self.content[start..];
        let offset = (start + rest.len() - rest.trim_start().len()) as u32;
        let index = self.line_starts.partition_point(|&line_start| line_start <= offset) - 1;
        let column = offset - self.line_starts[index] + 1;
        SourceLine { path: Arc::clone(&self.path), line: index as u32 + 1, column }
    }
}

impl Spans {
    pub(super) fn enter(&mut self, line: Option<SourceLine>) -> Option<SourceLine> {
        match line {
            Some(line) => self.enclosing.replace(line),
            None => self.enclosing.clone(),
        }
    }

    pub(super) fn enclosing(&self) -> Option<&SourceLine> {
        self.enclosing.as_ref()
    }

    pub(super) fn leave(&mut self, enclosing: Option<SourceLine>) {
        self.enclosing = enclosing;
    }

    pub(super) fn record(&mut self, value: &GoExpression, line: SourceLine) {
        let Some(enclosing) = &self.enclosing else { return };
        if same_line(enclosing, &line) || contains_function(value) {
            return;
        }
        let span = Span { enclosing: enclosing.clone(), line };
        self.by_text.entry(format!("{value:?}")).or_default().push(span);
    }

    fn recorded(&self, text: &str, attribution: &SourceLine) -> usize {
        self.by_text.get(text).map_or(0, |spans| {
            spans.iter().filter(|span| same_line(&span.enclosing, attribution)).count()
        })
    }

    fn take_line(&mut self, text: &str, attribution: &SourceLine) -> Option<SourceLine> {
        let spans = self.by_text.get_mut(text)?;
        let index = spans.iter().position(|span| same_line(&span.enclosing, attribution))?;
        Some(spans.remove(index).line)
    }
}

type Occurrence = (String, Arc<str>, u32);

pub(super) fn attribute_spans(declarations: &mut [GoDeclaration], spans: Spans) {
    struct Attribute {
        spans: Spans,
        attribution: Option<SourceLine>,
        counting: bool,
        occurrences: FxHashMap<Occurrence, usize>,
        ambiguous: FxHashSet<Occurrence>,
    }
    impl Attribute {
        fn line_of(&mut self, value: &GoExpression) -> Option<SourceLine> {
            let attribution = self.attribution.as_ref()?;
            if contains_function(value) {
                return None;
            }
            let text = format!("{value:?}");
            if !self.spans.by_text.contains_key(&text) {
                return None;
            }
            let occurrence = (text, Arc::clone(&attribution.path), attribution.line);
            if self.counting {
                *self.occurrences.entry(occurrence).or_default() += 1;
                return None;
            }
            if self.ambiguous.contains(&occurrence) {
                return None;
            }
            self.spans.take_line(&occurrence.0, attribution)
        }

        fn settle_ambiguity(&mut self) {
            let occurrences = std::mem::take(&mut self.occurrences);
            for (occurrence, count) in occurrences {
                let (text, path, line) = &occurrence;
                let attribution = SourceLine { path: Arc::clone(path), line: *line, column: 0 };
                if count > self.spans.recorded(text, &attribution) {
                    self.ambiguous.insert(occurrence);
                }
            }
            self.counting = false;
        }
    }
    impl Walk for Attribute {
        fn block(&mut self, body: &mut Vec<GoStatement>) {
            let enclosing = self.attribution.clone();
            for statement in body.iter_mut() {
                match statement {
                    GoStatement::Line(line) => self.attribution = Some(line.clone()),
                    statement => self.statement(statement),
                }
            }
            self.attribution = enclosing;
        }

        fn statement(&mut self, statement: &mut GoStatement) {
            match statement {
                GoStatement::Assign { values, .. } => {
                    values.iter_mut().for_each(|value| self.expression(value))
                }
                statement => walk::statement(self, statement),
            }
        }

        fn expression(&mut self, value: &mut GoExpression) {
            let line = self.line_of(value);
            walk::expression(self, value);
            if let Some(line) = line {
                let attributed = std::mem::replace(value, GoExpression::Boolean(false));
                *value = GoExpression::Attributed { line, value: Box::new(attributed) };
            }
        }
    }
    if spans.by_text.is_empty() {
        return;
    }
    let mut attribute = Attribute {
        spans,
        attribution: None,
        counting: true,
        occurrences: FxHashMap::default(),
        ambiguous: FxHashSet::default(),
    };
    for counting in [true, false] {
        if !counting {
            attribute.settle_ambiguity();
        }
        for declaration in declarations.iter_mut() {
            if let GoDeclaration::Function { body, .. } = declaration {
                attribute.block(body);
            }
        }
    }
}

fn same_line(left: &SourceLine, right: &SourceLine) -> bool {
    left.path == right.path && left.line == right.line
}

fn contains_function(value: &GoExpression) -> bool {
    struct Functions(bool);
    impl Walk for Functions {
        fn expression(&mut self, value: &mut GoExpression) {
            match value {
                GoExpression::Function { .. } => self.0 = true,
                value => walk::expression(self, value),
            }
        }
    }
    let mut functions = Functions(false);
    functions.expression(&mut value.clone());
    functions.0
}

/// Whether running the statements calls a function or indexes, which can fail; the bodies of
/// function literals do not run where the literal is written.
fn does_work(statements: &mut [GoStatement]) -> bool {
    struct Work(bool);
    impl Walk for Work {
        fn expression(&mut self, value: &mut GoExpression) {
            match value {
                GoExpression::Function { .. } => {}
                GoExpression::Call { .. }
                | GoExpression::Index { .. }
                | GoExpression::TypeAssertion { .. } => self.0 = true,
                _ => walk::expression(self, value),
            }
        }
    }
    let mut work = Work(false);
    statements.iter_mut().for_each(|statement| work.statement(statement));
    work.0
}

/// Names `line` in front of each statement in `statements` that no directive names, the
/// statements of the blocks nested in them and of function literals included: what the
/// expressions written inside an expression become names their own lines first, so the rest
/// comes from the expression itself.
fn attribute_every(line: &SourceLine, statements: &mut [GoStatement]) {
    struct Blocks<'a>(&'a SourceLine);
    impl Walk for Blocks<'_> {
        fn block(&mut self, body: &mut Vec<GoStatement>) {
            body.iter_mut().for_each(|statement| self.statement(statement));
            attribute_unnamed(self.0, 0, body);
        }
    }
    let mut blocks = Blocks(line);
    statements.iter_mut().for_each(|statement| blocks.statement(statement));
}

pub(super) fn attribute_branch(
    line: Option<&SourceLine>,
    start: usize,
    out: &mut Vec<GoStatement>,
) {
    let Some(line) = line else { return };
    attribute_every(line, &mut out[start..]);
    attribute_unnamed(line, start, out);
}

fn open_at(line: Option<SourceLine>, block: &mut Vec<GoStatement>) {
    let Some(line) = line else { return };
    if let Some(GoStatement::Line(first)) = block.first()
        && same_line(first, &line)
    {
        return;
    }
    block.insert(0, GoStatement::Line(line));
}

pub(super) fn open_otherwise_at(line: Option<SourceLine>, otherwise: &mut Vec<GoStatement>) {
    let mut statements =
        otherwise.iter().filter(|statement| !matches!(statement, GoStatement::Line(_)));
    match (statements.next(), statements.next()) {
        (None, _) | (Some(GoStatement::If { .. }), None) => {}
        _ => open_at(line, otherwise),
    }
}

pub(super) fn push_at(
    line: Option<SourceLine>,
    statement: GoStatement,
    out: &mut Vec<GoStatement>,
) {
    out.extend(line.map(GoStatement::Line));
    out.push(statement);
}

/// Puts a directive naming `line` in front of each statement of `body` from `start` on that does
/// not follow one.
fn attribute_unnamed(line: &SourceLine, start: usize, body: &mut Vec<GoStatement>) {
    let mut at = start;
    let mut named = false;
    while at < body.len() {
        let is_line = matches!(body[at], GoStatement::Line(_));
        if !is_line && !named {
            body.insert(at, GoStatement::Line(line.clone()));
            at += 1;
        }
        named = is_line;
        at += 1;
    }
}

/// The directives [`LineCoverage::Every`] puts in front of each statement, set aside while the
/// passes after emission rewrite the Go, so that they see the same statements as without
/// directives.
#[derive(Default)]
pub(super) struct SetAside {
    /// Each function's statements in order, outer ones before the blocks in them, each by what
    /// it is apart from those blocks and with the line it named.
    statements: FxHashMap<String, Vec<(String, Vec<SourceLine>)>>,
    definitions: FxHashMap<String, SourceLine>,
}

/// Takes the directives out of the declarations.
pub(super) fn set_aside(declarations: &mut [GoDeclaration]) -> SetAside {
    struct Record(Vec<(String, Vec<SourceLine>)>);
    impl Walk for Record {
        fn block(&mut self, body: &mut Vec<GoStatement>) {
            let mut named = vec![];
            for statement in body.iter_mut() {
                match statement {
                    GoStatement::Line(line) => named.push(line.clone()),
                    statement => {
                        self.0.push((head(statement), std::mem::take(&mut named)));
                        walk::statement(self, statement);
                    }
                }
            }
            body.retain(|statement| !matches!(statement, GoStatement::Line(_)));
        }
    }
    let mut aside = SetAside::default();
    for declaration in declarations.iter_mut() {
        let Some(name) = declaration.name().map(str::to_string) else { continue };
        if let GoDeclaration::Function { body, .. } = declaration
            && let [GoStatement::Line(definition), GoStatement::Line(_), ..] = body.as_slice()
        {
            aside.definitions.insert(name.clone(), definition.clone());
            body.remove(0);
        }
        let mut record = Record(vec![]);
        walk::declaration(&mut record, declaration);
        aside.statements.insert(name, record.0);
    }
    aside
}

/// Puts the directives set aside back in front of the statements the passes kept, and in front
/// of the statements a pass made in place of others the lines of those, in order; any other
/// statement a pass made names no line, so it shows the one before it.
pub(super) fn restore(declarations: &mut [GoDeclaration], mut aside: SetAside) {
    struct Heads(Vec<String>);
    impl Walk for Heads {
        fn block(&mut self, body: &mut Vec<GoStatement>) {
            for statement in body.iter_mut() {
                self.0.push(head(statement));
                walk::statement(self, statement);
            }
        }
    }
    struct Insert(std::vec::IntoIter<Vec<SourceLine>>);
    impl Walk for Insert {
        fn block(&mut self, body: &mut Vec<GoStatement>) {
            let statements = std::mem::take(body);
            for mut statement in statements {
                let lines = self.0.next().unwrap_or_default();
                walk::statement(self, &mut statement);
                body.extend(lines.into_iter().map(GoStatement::Line));
                body.push(statement);
            }
        }
    }
    for declaration in declarations.iter_mut() {
        let Some(before) = declaration.name().and_then(|name| aside.statements.remove(name)) else {
            continue;
        };
        let mut heads = Heads(vec![]);
        walk::declaration(&mut heads, declaration);
        let lines = align(&before, &heads.0);
        walk::declaration(&mut Insert(lines.into_iter()), declaration);
        if let GoDeclaration::Function { name, body, .. } = declaration
            && let Some(definition) = aside.definitions.remove(name.as_str())
        {
            body.insert(0, GoStatement::Line(definition));
        }
    }
}

/// The line for each statement of `after`: the line of the same statement in `before`, matched
/// in order, and between two matched statements the line of an unmatched one in `before` of the
/// same kind, or of the first one.
fn align(before: &[(String, Vec<SourceLine>)], after: &[String]) -> Vec<Vec<SourceLine>> {
    let mut positions: FxHashMap<&str, VecDeque<usize>> = FxHashMap::default();
    for (at, (head, _)) in before.iter().enumerate() {
        positions.entry(head).or_default().push_back(at);
    }
    // The statement of `before` each statement of `after` is, in increasing order.
    let mut matched: Vec<Option<usize>> = Vec::with_capacity(after.len());
    let mut next = 0;
    for head in after {
        let found = positions.get_mut(head.as_str()).and_then(|queue| {
            while queue.front().is_some_and(|&at| at < next) {
                queue.pop_front();
            }
            queue.pop_front()
        });
        if let Some(at) = found {
            next = at + 1;
        }
        matched.push(found);
    }
    let mut lines = Vec::with_capacity(after.len());
    let mut gap_start = 0;
    let mut at = 0;
    while at < after.len() {
        if let Some(found) = matched[at] {
            lines.push(before[found].1.clone());
            gap_start = found + 1;
            at += 1;
            continue;
        }
        let end = (at..after.len()).find(|&index| matched[index].is_some()).unwrap_or(after.len());
        let gap_end = matched.get(end).copied().flatten().unwrap_or(before.len());
        let replaced = &before[gap_start..gap_end];
        // A statement a pass rewrote is mostly still the same kind of statement.
        let mut cursor = 0;
        for head in &after[at..end] {
            let same_kind = |candidate: &usize| kind(&replaced[*candidate].0) == kind(head);
            let same_names = |candidate: &usize| {
                defined_names(head)
                    .is_some_and(|names| defined_names(&replaced[*candidate].0) == Some(names))
            };
            let same_kind = (cursor..replaced.len())
                .find(|candidate| same_kind(candidate) && same_names(candidate))
                .or_else(|| (cursor..replaced.len()).find(same_kind));
            let line = match same_kind {
                Some(candidate) => {
                    cursor = candidate + 1;
                    replaced[candidate].1.clone()
                }
                None => replaced
                    .get(cursor.min(replaced.len().saturating_sub(1)))
                    .map(|(_, lines)| lines.clone())
                    .unwrap_or_default(),
            };
            lines.push(line);
        }
        at = end;
    }
    lines
}
fn defined_names(head: &str) -> Option<&str> {
    let names = head.strip_prefix("Define { names: ")?;
    Some(names.split_once(", values: ")?.0)
}

/// The kind of statement a [`head`] is: `If`, `Assign`, `Define` and so on.
fn kind(head: &str) -> &str {
    head.split(|character: char| !character.is_alphanumeric()).next().unwrap_or(head)
}

/// The statement apart from the blocks in it, function literals' bodies included.
fn head(statement: &GoStatement) -> String {
    struct Empty;
    impl Walk for Empty {
        fn block(&mut self, body: &mut Vec<GoStatement>) {
            body.clear();
        }
    }
    let mut head = statement.clone();
    Empty.statement(&mut head);
    format!("{head:?}")
}
