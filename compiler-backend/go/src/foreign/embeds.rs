//! Files a foreign Go file embeds with `//go:embed`, which travel with it into the program's
//! package so that the embed works unchanged. Patterns follow Go's rules: relative to the Go
//! file's directory, matched element by element as `path.Match` does, a directory standing for
//! every file below it except those whose names start with `.` or `_`, unless the pattern starts
//! with `all:`. Unlike Go, a symbolic link is followed, since the copy is a regular file.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::{fs, io};

use thiserror::Error;

#[derive(Debug, Error)]
pub enum EmbedError {
    #[error(
        "{file}: //go:embed {pattern}: the pattern leaves the directory of the Go file; embed only files beside it or below it"
    )]
    LeavesDirectory { file: String, pattern: String },
    #[error("{file}: //go:embed {pattern}: invalid pattern syntax")]
    InvalidPattern { file: String, pattern: String },
    #[error("{file}: //go:embed: {line}: unterminated quoted pattern")]
    UnterminatedQuote { file: String, line: String },
    #[error("{file}: //go:embed {pattern}: no matching files found")]
    NoMatch { file: String, pattern: String },
    #[error(
        "{file}: //go:embed {pattern}: cannot embed directory {directory}: contains no embeddable files"
    )]
    EmptyDirectory { file: String, pattern: String, directory: String },
    #[error("{file}: //go:embed {pattern}: {error}")]
    Io { file: String, pattern: String, error: io::Error },
}

/// The files the Go file `file` with source `source` embeds, relative to its directory, in
/// order and each once.
pub fn embedded_files(file: &Path, source: &str) -> Result<Vec<PathBuf>, EmbedError> {
    let shown = file.display().to_string();
    let directory = file.parent().unwrap_or(Path::new(""));
    let mut files = BTreeSet::new();
    for pattern in embed_patterns(source)
        .map_err(|line| EmbedError::UnterminatedQuote { file: shown.clone(), line })?
    {
        files.extend(matching_files(directory, &pattern).map_err(|error| error.in_file(&shown))?);
    }
    Ok(files.into_iter().collect())
}

/// The patterns of every `//go:embed` directive, or the directive whose quote is unterminated.
fn embed_patterns(source: &str) -> Result<Vec<String>, String> {
    let mut patterns = vec![];
    for line in source.lines() {
        let Some(arguments) = line.trim_start().strip_prefix("//go:embed") else { continue };
        if !arguments.starts_with([' ', '\t']) {
            continue;
        }
        patterns.extend(directive_arguments(arguments).ok_or_else(|| line.trim().to_string())?);
    }
    Ok(patterns)
}

/// A directive's space-separated arguments, any of them a Go string literal: `"a b.txt"`, or
/// `` `a b.txt` ``.
fn directive_arguments(arguments: &str) -> Option<Vec<String>> {
    let mut parsed = vec![];
    let mut rest = arguments.trim_start();
    while !rest.is_empty() {
        let (argument, after) = match rest.chars().next()? {
            '`' => {
                let end = rest[1..].find('`')? + 1;
                (rest[1..end].to_string(), &rest[end + 1..])
            }
            '"' => interpreted_string(&rest[1..])?,
            _ => {
                let end = rest.find(char::is_whitespace).unwrap_or(rest.len());
                (rest[..end].to_string(), &rest[end..])
            }
        };
        parsed.push(argument);
        rest = after.trim_start();
    }
    Some(parsed)
}

/// The value of a double-quoted string after its opening quote, and what follows its closing one.
fn interpreted_string(text: &str) -> Option<(String, &str)> {
    let mut value = String::new();
    let mut characters = text.char_indices();
    while let Some((index, character)) = characters.next() {
        match character {
            '"' => return Some((value, &text[index + 1..])),
            '\\' => value.push(match characters.next()?.1 {
                'n' => '\n',
                't' => '\t',
                escaped => escaped,
            }),
            _ => value.push(character),
        }
    }
    None
}

/// What went wrong with a pattern, before the Go file it is in is known.
enum PatternError {
    LeavesDirectory(String),
    Invalid(String),
    NoMatch(String),
    EmptyDirectory(String, PathBuf),
    Io(String, io::Error),
}

impl PatternError {
    fn in_file(self, file: &str) -> EmbedError {
        let file = file.to_string();
        match self {
            PatternError::LeavesDirectory(pattern) => EmbedError::LeavesDirectory { file, pattern },
            PatternError::Invalid(pattern) => EmbedError::InvalidPattern { file, pattern },
            PatternError::NoMatch(pattern) => EmbedError::NoMatch { file, pattern },
            PatternError::EmptyDirectory(pattern, directory) => EmbedError::EmptyDirectory {
                file,
                pattern,
                directory: directory.display().to_string(),
            },
            PatternError::Io(pattern, error) => EmbedError::Io { file, pattern, error },
        }
    }
}

/// The files below `directory` that `pattern` embeds, relative to `directory`.
fn matching_files(directory: &Path, pattern: &str) -> Result<Vec<PathBuf>, PatternError> {
    let (all, glob) = match pattern.strip_prefix("all:") {
        Some(glob) => (true, glob),
        None => (false, pattern),
    };
    let elements: Vec<&str> = glob.split('/').collect();
    if glob.starts_with('/') || elements.contains(&"..") {
        return Err(PatternError::LeavesDirectory(pattern.to_string()));
    }
    let valid = |element: &&str| !element.is_empty() && *element != "." && valid_glob(element);
    if !elements.iter().all(valid) {
        return Err(PatternError::Invalid(pattern.to_string()));
    }
    let io_error = |error| PatternError::Io(pattern.to_string(), error);

    let mut matches = vec![PathBuf::new()];
    for element in elements {
        let mut next = vec![];
        for matched in matches.into_iter().filter(|path| is_directory(&directory.join(path))) {
            for name in names_in(&directory.join(&matched)).map_err(io_error)? {
                if glob_matches(element, &name) {
                    next.push(matched.join(name));
                }
            }
        }
        matches = next;
    }
    if matches.is_empty() {
        return Err(PatternError::NoMatch(pattern.to_string()));
    }

    let mut files = vec![];
    for matched in matches {
        if !is_directory(&directory.join(&matched)) {
            files.push(matched);
            continue;
        }
        let before = files.len();
        let mut visiting = vec![];
        walk(directory, &matched, all, &mut visiting, &mut files).map_err(io_error)?;
        if files.len() == before {
            return Err(PatternError::EmptyDirectory(pattern.to_string(), matched));
        }
    }
    Ok(files)
}

/// Adds the embeddable files below `relative` to `files`, following symbolic links but not into
/// a directory it is already inside, and leaving out other Go modules.
fn walk(
    root: &Path,
    relative: &Path,
    all: bool,
    visiting: &mut Vec<PathBuf>,
    files: &mut Vec<PathBuf>,
) -> io::Result<()> {
    let path = root.join(relative);
    let canonical = fs::canonicalize(&path)?;
    if visiting.contains(&canonical) {
        return Ok(());
    }
    visiting.push(canonical);
    for name in names_in(&path)? {
        if !all && (name.starts_with('.') || name.starts_with('_')) {
            continue;
        }
        let child = relative.join(&name);
        let full = root.join(&child);
        if !is_directory(&full) {
            if full.is_file() {
                files.push(child);
            }
        } else if !full.join("go.mod").exists() {
            walk(root, &child, all, visiting, files)?;
        }
    }
    visiting.pop();
    Ok(())
}

/// The names in a directory, in order.
fn names_in(directory: &Path) -> io::Result<Vec<String>> {
    let mut names = vec![];
    for entry in fs::read_dir(directory)? {
        if let Ok(name) = entry?.file_name().into_string() {
            names.push(name);
        }
    }
    names.sort();
    Ok(names)
}

/// Whether the path is a directory, through any symbolic links.
fn is_directory(path: &Path) -> bool {
    fs::metadata(path).is_ok_and(|metadata| metadata.is_dir())
}

/// Whether a pattern element is well-formed for `path.Match`: every class closed and every
/// escape followed by a character.
fn valid_glob(element: &str) -> bool {
    glob_match(element, "").is_some()
}

/// Whether `name` matches a pattern element, as Go's `path.Match` decides.
fn glob_matches(element: &str, name: &str) -> bool {
    glob_match(element, name).unwrap_or(false)
}

/// `path.Match` for one element: `*` any run of characters, `?` one character, `[a-z]` and
/// `[^a-z]` a class, `\` an escape. `None` when the pattern is malformed.
fn glob_match(pattern: &str, name: &str) -> Option<bool> {
    let pattern: Vec<char> = pattern.chars().collect();
    let name: Vec<char> = name.chars().collect();
    let mut wellformed = true;
    let matched = match_from(&pattern, &name, &mut wellformed);
    // A malformed class after the point where matching stopped still makes the pattern malformed.
    wellformed &= classes_close(&pattern);
    wellformed.then_some(matched)
}

fn match_from(pattern: &[char], name: &[char], wellformed: &mut bool) -> bool {
    let Some((&first, rest)) = pattern.split_first() else { return name.is_empty() };
    match first {
        '*' => (0..=name.len()).any(|skip| match_from(rest, &name[skip..], wellformed)),
        '?' => !name.is_empty() && match_from(rest, &name[1..], wellformed),
        '[' => {
            let Some((class_matches, after)) = class(rest, name.first().copied()) else {
                *wellformed = false;
                return false;
            };
            class_matches && match_from(after, &name[1..], wellformed)
        }
        '\\' => match rest.split_first() {
            Some((&escaped, rest)) => {
                name.first() == Some(&escaped) && match_from(rest, &name[1..], wellformed)
            }
            None => {
                *wellformed = false;
                false
            }
        },
        literal => name.first() == Some(&literal) && match_from(rest, &name[1..], wellformed),
    }
}

/// Whether `character` is in the class after its `[`, and what follows its `]`; `None` when the
/// class does not close.
fn class(pattern: &[char], character: Option<char>) -> Option<(bool, &[char])> {
    let (negated, mut rest) = match pattern.split_first() {
        Some(('^', rest)) => (true, rest),
        _ => (false, pattern),
    };
    let mut found = false;
    let mut first = true;
    loop {
        let (&next, after) = rest.split_first()?;
        if next == ']' && !first {
            let inside = character.is_some_and(|_| found != negated);
            return Some((inside, after));
        }
        first = false;
        let (low, after) = class_character(rest)?;
        let (high, after) = match after.split_first() {
            Some(('-', range)) => class_character(range)?,
            _ => (low, after),
        };
        found |= character.is_some_and(|character| low <= character && character <= high);
        rest = after;
    }
}

fn class_character(pattern: &[char]) -> Option<(char, &[char])> {
    match pattern.split_first()? {
        ('\\', rest) => rest.split_first().map(|(&escaped, rest)| (escaped, rest)),
        (&character, rest) if character != ']' && character != '-' => Some((character, rest)),
        _ => None,
    }
}

/// Whether every `[` in the pattern starts a class that closes.
fn classes_close(pattern: &[char]) -> bool {
    let mut rest = pattern;
    while let Some((&first, after)) = rest.split_first() {
        rest = match first {
            '\\' => match after.split_first() {
                Some((_, after)) => after,
                None => return false,
            },
            '[' => match class(after, None) {
                Some((_, after)) => after,
                None => return false,
            },
            _ => after,
        };
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_directive_lists_plain_and_quoted_patterns() {
        let source = "package ffi\n\nimport _ \"embed\"\n\n//go:embed greeting.txt fonts/*.ttf\n//go:embed \"with space.txt\" `raw name.txt` all:static\n// go:embed ignored.txt\n//go:embedded ignored.txt\nvar files embed.FS\n";
        assert_eq!(
            embed_patterns(source).unwrap(),
            ["greeting.txt", "fonts/*.ttf", "with space.txt", "raw name.txt", "all:static"]
        );
    }

    #[test]
    fn an_unterminated_quote_names_the_directive() {
        assert_eq!(embed_patterns("//go:embed \"open.txt\n").unwrap_err(), "//go:embed \"open.txt");
    }

    #[test]
    fn a_pattern_element_matches_as_go_path_match_does() {
        assert!(glob_matches("*.ttf", "Inter.ttf"));
        assert!(glob_matches("*", ".hidden"));
        assert!(!glob_matches("*.ttf", "Inter.otf"));
        assert!(glob_matches("font?.ttf", "font1.ttf"));
        assert!(glob_matches("[a-c]*", "bold"));
        assert!(!glob_matches("[^a-c]*", "bold"));
        assert!(glob_matches("\\*", "*"));
        assert!(!glob_matches("\\*", "x"));
        assert!(!valid_glob("[a-"));
        assert!(!valid_glob("x\\"));
        assert!(!valid_glob("a[]"));
    }

    #[test]
    fn a_pattern_cannot_leave_the_directory_or_be_malformed() {
        let directory = Path::new(".");
        assert!(matches!(
            matching_files(directory, "../shared/x.txt"),
            Err(PatternError::LeavesDirectory(_))
        ));
        assert!(matches!(
            matching_files(directory, "/etc/hosts"),
            Err(PatternError::LeavesDirectory(_))
        ));
        assert!(matches!(
            matching_files(directory, "all:../x"),
            Err(PatternError::LeavesDirectory(_))
        ));
        for pattern in ["./x", "a//b", "dir/", "[a-"] {
            assert!(matches!(matching_files(directory, pattern), Err(PatternError::Invalid(_))));
        }
    }
}
