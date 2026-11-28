use std::ops::Range;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenKind {
    Word,
    Literal,
    Symbol(&'static str),
    Comment,
}

#[derive(Debug, Clone, Copy)]
pub struct Token<'s> {
    pub kind: TokenKind,
    pub text: &'s str,
    pub offset: usize,
}

impl<'s> Token<'s> {
    fn new(kind: TokenKind, source: &'s str, range: Range<usize>) -> Token<'s> {
        Token { kind, text: &source[range.clone()], offset: range.start }
    }

    pub fn end(&self) -> usize {
        self.offset + self.text.len()
    }

    pub fn word(&self) -> Option<&'s str> {
        (self.kind == TokenKind::Word).then_some(self.text)
    }

    pub fn is_word(&self, word: &str) -> bool {
        self.word() == Some(word)
    }

    pub fn is(&self, symbol: &str) -> bool {
        matches!(self.kind, TokenKind::Symbol(own) if own == symbol)
    }

    pub fn is_comment(&self) -> bool {
        self.kind == TokenKind::Comment
    }

    pub fn is_opening(&self) -> bool {
        self.is("(") || self.is("[") || self.is("{")
    }

    pub fn is_closing(&self) -> bool {
        self.is(")") || self.is("]") || self.is("}")
    }
}

pub const KEYWORDS: &[&str] = &[
    "break",
    "case",
    "chan",
    "const",
    "continue",
    "default",
    "defer",
    "else",
    "fallthrough",
    "for",
    "func",
    "go",
    "goto",
    "if",
    "import",
    "interface",
    "map",
    "package",
    "range",
    "return",
    "select",
    "struct",
    "switch",
    "type",
    "var",
];

const STATEMENT_ENDING_KEYWORDS: &[&str] = &["break", "continue", "fallthrough", "return"];

const SYMBOLS: &[&str] = &[
    "<<=", ">>=", "&^=", "...", "&&", "||", "<-", "++", "--", "==", "!=", "<=", ">=", ":=", "+=",
    "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<", ">>", "&^", "+", "-", "*", "/", "%", "&", "|",
    "^", "<", ">", "=", "!", "(", ")", "[", "]", "{", "}", ",", ";", ".", ":", "~",
];

pub fn tokens(source: &str) -> Result<Vec<Token<'_>>, String> {
    let mut tokens = vec![];
    let mut position = 0;
    while let Some(character) = source[position..].chars().next() {
        let rest = &source[position..];
        if character == '\n' {
            end_line(&mut tokens, position);
            position += 1;
        } else if character.is_whitespace() {
            position += character.len_utf8();
        } else if rest.starts_with("//") {
            let end = rest.find('\n').map_or(source.len(), |length| position + length);
            tokens.push(Token::new(TokenKind::Comment, source, position..end));
            position = end;
        } else if let Some(comment) = rest.strip_prefix("/*") {
            let length = comment.find("*/").ok_or("an unterminated comment")? + 4;
            let end = position + length;
            tokens.push(Token::new(TokenKind::Comment, source, position..end));
            if source[position..end].contains('\n') {
                end_line(&mut tokens, end);
            }
            position = end;
        } else if matches!(character, '"' | '\'' | '`') {
            let end = literal_end(source, position)?;
            tokens.push(Token::new(TokenKind::Literal, source, position..end));
            position = end;
        } else if character.is_alphabetic() || character == '_' {
            let length = rest
                .find(|character: char| !(character.is_alphanumeric() || character == '_'))
                .unwrap_or(rest.len());
            tokens.push(Token::new(TokenKind::Word, source, position..position + length));
            position += length;
        } else if character.is_ascii_digit()
            || (character == '.' && rest[1..].starts_with(|next: char| next.is_ascii_digit()))
        {
            let end = number_end(source, position);
            tokens.push(Token::new(TokenKind::Literal, source, position..end));
            position = end;
        } else {
            let symbol = SYMBOLS.iter().find(|symbol| rest.starts_with(**symbol));
            let symbol = symbol.ok_or_else(|| format!("an unexpected `{character}`"))?;
            let end = position + symbol.len();
            tokens.push(Token::new(TokenKind::Symbol(symbol), source, position..end));
            position = end;
        }
    }
    end_line(&mut tokens, source.len());
    Ok(tokens)
}

fn end_line(tokens: &mut Vec<Token>, position: usize) {
    let Some(last) = tokens.iter().rev().find(|token| !token.is_comment()) else { return };
    let ends_statement = match last.kind {
        TokenKind::Word => {
            !KEYWORDS.contains(&last.text) || STATEMENT_ENDING_KEYWORDS.contains(&last.text)
        }
        TokenKind::Literal => true,
        TokenKind::Symbol(symbol) => [")", "]", "}", "++", "--"].contains(&symbol),
        TokenKind::Comment => false,
    };
    if ends_statement {
        tokens.push(Token { kind: TokenKind::Symbol(";"), text: "", offset: position });
    }
}

fn literal_end(source: &str, start: usize) -> Result<usize, String> {
    let quote = source.as_bytes()[start];
    let mut characters = source[start + 1..].char_indices();
    while let Some((offset, character)) = characters.next() {
        if character == quote as char {
            return Ok(start + 1 + offset + 1);
        }
        if quote != b'`' && character == '\n' {
            break;
        }
        if quote != b'`' && character == '\\' {
            characters.next();
        }
    }
    Err("an unterminated literal".to_string())
}

fn number_end(source: &str, start: usize) -> usize {
    let mut previous = None;
    for (offset, character) in source[start..].char_indices() {
        let after_exponent = matches!(previous, Some('e' | 'E' | 'p' | 'P'));
        let exponent_sign = after_exponent && matches!(character, '+' | '-');
        if !(character.is_alphanumeric() || matches!(character, '_' | '.') || exponent_sign) {
            return start + offset;
        }
        previous = Some(character);
    }
    source.len()
}

pub fn split_top<'t, 's>(tokens: &'t [Token<'s>], separator: &str) -> Vec<&'t [Token<'s>]> {
    let mut parts = vec![];
    let mut depth = 0usize;
    let mut start = 0;
    for (index, token) in tokens.iter().enumerate() {
        if token.is_opening() {
            depth += 1;
        } else if token.is_closing() {
            depth = depth.saturating_sub(1);
        } else if depth == 0 && token.is(separator) {
            parts.push(&tokens[start..index]);
            start = index + 1;
        }
    }
    parts.push(&tokens[start..]);
    parts.into_iter().filter(|part| !part.is_empty()).collect()
}

pub fn closing(tokens: &[Token], open: usize) -> Option<usize> {
    let mut depth = 0usize;
    for (index, token) in tokens.iter().enumerate().skip(open) {
        if token.is_opening() {
            depth += 1;
        } else if token.is_closing() {
            depth = depth.checked_sub(1)?;
            if depth == 0 {
                return Some(index);
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    fn spelled(source: &str) -> Vec<&str> {
        let tokens = tokens(source).unwrap();
        let code = tokens.into_iter().filter(|token| !token.is_comment());
        code.map(|token| if token.text.is_empty() { "⏎" } else { token.text }).collect()
    }

    #[test]
    fn comments_and_literals_hide_the_code_they_spell() {
        let source = "x := \"recover()\" // recover()\n/* type T struct{} */ y := `\nfunc F() {}`";
        assert_eq!(
            spelled(source),
            ["x", ":=", "\"recover()\"", "⏎", "y", ":=", "`\nfunc F() {}`", "⏎"]
        );
    }

    #[test]
    fn a_line_ends_a_statement_that_can_end_there() {
        assert_eq!(
            spelled("return\nx++\nf(a,\nb)\n"),
            ["return", "⏎", "x", "++", "⏎", "f", "(", "a", ",", "b", ")", "⏎"]
        );
        assert_eq!(spelled("x /* a\nb */ y"), ["x", "⏎", "y", "⏎"]);
    }

    #[test]
    fn escapes_do_not_end_a_literal() {
        assert_eq!(
            spelled(r#"a := "say \"hi\"" + '\''"#),
            ["a", ":=", r#""say \"hi\"""#, "+", r"'\''", "⏎"]
        );
    }

    #[test]
    fn numbers_keep_their_exponents_and_bases() {
        assert_eq!(spelled("1e+9 - 0x1p-2 + .5i"), ["1e+9", "-", "0x1p-2", "+", ".5i", "⏎"]);
    }

    #[test]
    fn unterminated_text_is_unreadable() {
        assert_eq!(tokens("x := \"open\n").unwrap_err(), "an unterminated literal");
        assert_eq!(tokens("/* open").unwrap_err(), "an unterminated comment");
        assert_eq!(tokens("x := #").unwrap_err(), "an unexpected `#`");
    }
}
