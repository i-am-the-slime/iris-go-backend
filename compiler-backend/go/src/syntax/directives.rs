use std::fmt::Write;

/// The file's text with only the `//line` directives Go needs: Go counts lines on from the last
/// directive, so one that names the line Go counts to anyway is left out. A declaration that
/// follows PureScript code without naming any itself is attributed to the Go file again.
pub(super) fn settle_line_directives(text: &str, file_name: &str) -> String {
    let mut settled = String::with_capacity(text.len());
    // The file and line Go attributes the next line to, and the next line's number in the file.
    let mut counted: Option<(&str, u32)> = None;
    let mut written = 1;
    let mut previous_blank = false;
    for line in text.lines() {
        if let Some((path, number)) = directive(line) {
            if counted != Some((path, number)) {
                settled.push_str(line);
                settled.push('\n');
                written += 1;
                counted = Some((path, number));
            }
            previous_blank = false;
            continue;
        }
        let starts_declaration = previous_blank
            && line
                .starts_with(|first: char| !first.is_whitespace() && first != '}' && first != ')');
        if starts_declaration
            && let Some((path, number)) = counted
            && (path != file_name || number != written)
        {
            let _ = writeln!(settled, "//line {file_name}:{}", written + 1);
            written += 1;
            counted = None;
        }
        settled.push_str(line);
        settled.push('\n');
        written += 1;
        counted = counted.map(|(path, number)| (path, number + 1));
        previous_blank = line.is_empty();
    }
    settled
}

/// What the printer writes for a directive that names the Go file's own next line, whose number
/// is known only once the declarations are joined.
pub(super) const GO_LINE_PLACEHOLDER: &str = "//line \0\n";

pub(super) const INLINE_DIRECTIVE_MARK: char = '\u{1}';

/// The file's text with each placeholder directive naming the Go file's own next line.
pub(super) fn name_go_lines(text: &str, file_name: &str) -> String {
    let mut named = String::with_capacity(text.len());
    let placeholder = GO_LINE_PLACEHOLDER.trim_end_matches('\n');
    for (index, line) in text.lines().enumerate() {
        if line == placeholder {
            let _ = writeln!(named, "//line {file_name}:{}", index + 2);
        } else {
            name_inline_directives(&mut named, line, file_name, index + 1);
            named.push('\n');
        }
    }
    named
}

fn name_inline_directives(named: &mut String, line: &str, file_name: &str, number: usize) {
    let mut pieces = line.split(INLINE_DIRECTIVE_MARK);
    let mut written = pieces.next().unwrap_or_default().to_string();
    for piece in pieces {
        let Some((target, rest)) = piece.split_once("*/") else { continue };
        if rest.is_empty() {
            continue;
        }
        let directive = match target {
            "/*line " => format!("/*line {file_name}:{number}*/"),
            target => format!("{target}*/"),
        };
        place_inline_directive(&mut written, &directive, rest);
    }
    named.push_str(&written);
}

fn place_inline_directive(written: &mut String, directive: &str, rest: &str) {
    let rest = match rest.strip_prefix('.') {
        Some(selected) => {
            written.push('.');
            selected
        }
        None => rest,
    };
    let separated = written.ends_with(", ");
    if separated {
        written.truncate(written.len() - 2);
    }
    if !written.is_empty() && !written.ends_with(char::is_whitespace) {
        written.push(' ');
    }
    written.push_str(directive);
    if separated {
        written.push_str(", ");
    } else if !rest.starts_with([',', ')', ']', '}', ' ']) {
        written.push(' ');
    }
    written.push_str(rest);
}

/// The file and line a `//line file:line[:column]` directive names.
pub(super) fn directive(line: &str) -> Option<(&str, u32)> {
    let named = line.strip_prefix("//line ")?;
    let (rest, last) = named.rsplit_once(':')?;
    let last: u32 = last.parse().ok()?;
    match rest.rsplit_once(':') {
        Some((path, line)) if line.parse::<u32>().is_ok() => Some((path, line.parse().ok()?)),
        _ => Some((rest, last)),
    }
}
