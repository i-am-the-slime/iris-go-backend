//! `//line` directives, so that Go's stack traces, debuggers and profiles name the PureScript a
//! piece of generated code comes from. The emitter puts a directive in front of the statements
//! each expression with a known position becomes, where they call a function or can fail: only
//! such code shows up in a trace or a profile, and the passes after emission see through fewer
//! directives. The printer leaves out the ones that repeat the line before and names the
//! enclosing line again after a nested block that named another.

use std::sync::Arc;

use files::FileId;
use rustc_hash::FxHashMap;

use super::Emitter;
use crate::error::GoResult;
use crate::mono::SourcePosition;
use crate::syntax::{GoExpression, GoStatement, SourceLine};
use crate::walk::{self, Walk};

/// The sources positions are resolved in, by file: none for a file the program's messages do not
/// show, such as a built-in module's.
#[derive(Default)]
pub(super) struct SourceLines {
    files: FxHashMap<FileId, Option<SourceFile>>,
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
    /// unless they begin with a directive of their own.
    pub(super) fn attribute(
        &mut self,
        position: Option<SourcePosition>,
        start: usize,
        out: &mut Vec<GoStatement>,
    ) -> GoResult<()> {
        if self.foreign_packages.line_directives.is_none() {
            return Ok(());
        }
        let Some(position) = position else { return Ok(()) };
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
