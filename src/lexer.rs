use crate::diag::{Diagnostic, Span};

#[derive(Debug, Clone, PartialEq)]
pub enum Tok {
    Int(i64),
    Float(f64),
    Str(String),
    /// A string containing `#{...}`. Code parts are lexed and parsed by the parser.
    Interp(Vec<RawPart>),
    Ident(String),
    /// `:name`, a symbol literal.
    Sym(String),
    Kw(&'static str),
    Op(&'static str),
    Newline,
    Eof,
}

#[derive(Debug, Clone, PartialEq)]
pub enum RawPart {
    Lit(String),
    /// Source text of the code and the byte offset of its first character.
    Code(String, u32),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub tok: Tok,
    pub span: Span,
}

const KEYWORDS: &[&str] = &[
    "def", "do", "end", "let", "mut", "if", "elsif", "else", "while", "for", "in", "loop", "break",
    "next", "return", "case", "then", "struct", "enum", "trait", "impl", "import", "move", "mdo",
    "self", "true", "false", "and", "or", "not", "type", "extern", "Self", "derive",
];

// Longest operators first so that `..` wins over `.` and `|>` over `|`.
const OPS: &[&str] = &[
    "...", ">>=", "|>", "==", "!=", "<=", ">=", "->", "+=", "-=", "*=", "/=", "..", "<<", ">>",
    "=>", "<-", "+", "-", "*", "/", "%", "<", ">", "=", "(", ")", "[", "]", "{", "}", ",", ":",
    ".", "&", "|", "^", "?", "@",
];

fn sp(s: usize, e: usize) -> Span {
    Span { start: s as u32, end: e as u32 }
}

/// Lexes a string literal starting at the opening quote. Returns the token and the index after
/// the closing quote. `#{...}` parts are captured as raw code with their byte offset.
fn lex_string(src: &str, start: usize) -> Result<(Tok, usize), Diagnostic> {
    let b = src.as_bytes();
    let mut i = start + 1;
    let mut parts: Vec<RawPart> = Vec::new();
    let mut s = String::new();
    loop {
        if i >= b.len() {
            return Err(Diagnostic::new(sp(start, i), "unterminated string"));
        }
        match b[i] {
            b'"' => {
                i += 1;
                break;
            }
            b'\\' => {
                let e = *b.get(i + 1).ok_or_else(|| Diagnostic::new(sp(start, i), "unterminated string"))?;
                s.push(match e {
                    b'n' => '\n',
                    b't' => '\t',
                    b'\\' => '\\',
                    b'"' => '"',
                    b'0' => '\0',
                    b'#' => '#',
                    _ => return Err(Diagnostic::new(sp(i, i + 2), "unknown escape")),
                });
                i += 2;
            }
            b'#' if i + 1 < b.len() && b[i + 1] == b'{' => {
                if !s.is_empty() {
                    parts.push(RawPart::Lit(std::mem::take(&mut s)));
                }
                let code_start = i + 2;
                let code_end = skip_code(src, code_start, start)?;
                parts.push(RawPart::Code(src[code_start..code_end].to_string(), code_start as u32));
                i = code_end + 1;
            }
            _ => {
                let ch = src[i..].chars().next().unwrap();
                s.push(ch);
                i += ch.len_utf8();
            }
        }
    }
    if parts.is_empty() {
        return Ok((Tok::Str(s), i));
    }
    if !s.is_empty() {
        parts.push(RawPart::Lit(s));
    }
    Ok((Tok::Interp(parts), i))
}

/// Given the index just after `#{`, returns the index of the matching `}`. Nested braces and
/// nested string literals (which may themselves interpolate) are skipped.
fn skip_code(src: &str, from: usize, str_start: usize) -> Result<usize, Diagnostic> {
    let b = src.as_bytes();
    let mut depth = 1usize;
    let mut i = from;
    while i < b.len() {
        match b[i] {
            b'{' => depth += 1,
            b'}' => {
                depth -= 1;
                if depth == 0 {
                    return Ok(i);
                }
            }
            b'"' => {
                let (_, end) = lex_string(src, i)?;
                i = end;
                continue;
            }
            _ => {}
        }
        i += 1;
    }
    Err(Diagnostic::new(sp(str_start, i), "unterminated interpolation in string"))
}

/// End of the identifier starting at `i`. `empty?` and `sort!` are identifiers; `x != y` is not.
fn ident_end(b: &[u8], mut i: usize) -> usize {
    while i < b.len() && (b[i].is_ascii_alphanumeric() || b[i] == b'_') {
        i += 1;
    }
    if i < b.len() && (b[i] == b'?' || b[i] == b'!') && !(i + 1 < b.len() && b[i + 1] == b'=') {
        i += 1;
    }
    i
}

pub fn lex(src: &str) -> Result<Vec<Token>, Diagnostic> {
    let b = src.as_bytes();
    let mut i = 0usize;
    let mut out: Vec<Token> = Vec::new();
    while i < b.len() {
        let c = b[i];
        match c {
            b' ' | b'\t' | b'\r' => i += 1,
            b'#' => {
                while i < b.len() && b[i] != b'\n' {
                    i += 1;
                }
            }
            b'\n' => {
                let continues = match out.last() {
                    None => true,
                    Some(t) => match &t.tok {
                        Tok::Newline => true,
                        Tok::Op(o) => !matches!(*o, ")" | "]" | "}" | "?"),
                        _ => false,
                    },
                };
                if !continues {
                    out.push(Token { tok: Tok::Newline, span: sp(i, i + 1) });
                }
                i += 1;
            }
            b'0'..=b'9' => {
                let start = i;
                if c == b'0' && i + 1 < b.len() && (b[i + 1] == b'x' || b[i + 1] == b'X') {
                    i += 2;
                    while i < b.len() && (b[i].is_ascii_hexdigit() || b[i] == b'_') {
                        i += 1;
                    }
                    let text: String = src[start + 2..i].chars().filter(|c| *c != '_').collect();
                    let v = i64::from_str_radix(&text, 16)
                        .map_err(|_| Diagnostic::new(sp(start, i), "integer literal out of range"))?;
                    out.push(Token { tok: Tok::Int(v), span: sp(start, i) });
                    continue;
                }
                while i < b.len() && (b[i].is_ascii_digit() || b[i] == b'_') {
                    i += 1;
                }
                let mut is_float = false;
                if i + 1 < b.len() && b[i] == b'.' && b[i + 1].is_ascii_digit() {
                    is_float = true;
                    i += 1;
                    while i < b.len() && (b[i].is_ascii_digit() || b[i] == b'_') {
                        i += 1;
                    }
                }
                let text: String = src[start..i].chars().filter(|c| *c != '_').collect();
                let tok = if is_float {
                    Tok::Float(text.parse().map_err(|_| Diagnostic::new(sp(start, i), "bad float literal"))?)
                } else {
                    Tok::Int(text.parse().map_err(|_| Diagnostic::new(sp(start, i), "integer literal out of range"))?)
                };
                out.push(Token { tok, span: sp(start, i) });
            }
            b'"' => {
                let start = i;
                let (tok, end) = lex_string(src, start)?;
                i = end;
                out.push(Token { tok, span: sp(start, i) });
            }
            // `:name` is a symbol unless the colon follows a name or a closing bracket (`x: Int`, `{ f:v }`).
            b':' if i + 1 < b.len()
                && (b[i + 1].is_ascii_alphabetic() || b[i + 1] == b'_')
                && !(i > 0 && (b[i - 1].is_ascii_alphanumeric() || matches!(b[i - 1], b'_' | b')' | b']' | b'?' | b'!'))) =>
            {
                let start = i;
                i = ident_end(b, i + 1);
                out.push(Token { tok: Tok::Sym(src[start + 1..i].to_string()), span: sp(start, i) });
            }
            c if c.is_ascii_alphabetic() || c == b'_' => {
                let start = i;
                i = ident_end(b, i);
                let word = &src[start..i];
                let tok = match KEYWORDS.iter().find(|k| **k == word) {
                    Some(k) => Tok::Kw(k),
                    None => Tok::Ident(word.to_string()),
                };
                out.push(Token { tok, span: sp(start, i) });
            }
            _ => {
                let rest = &src[i..];
                match OPS.iter().find(|op| rest.starts_with(**op)) {
                    Some(op) => {
                        out.push(Token { tok: Tok::Op(op), span: sp(i, i + op.len()) });
                        i += op.len();
                    }
                    None => {
                        let ch = rest.chars().next().unwrap();
                        return Err(Diagnostic::new(sp(i, i + ch.len_utf8()), format!("unexpected character {ch:?}")));
                    }
                }
            }
        }
    }
    if !matches!(out.last().map(|t| &t.tok), Some(Tok::Newline) | None) {
        out.push(Token { tok: Tok::Newline, span: sp(i, i) });
    }
    out.push(Token { tok: Tok::Eof, span: sp(i, i) });
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn toks(s: &str) -> Vec<Tok> {
        lex(s).unwrap().into_iter().map(|t| t.tok).collect()
    }

    #[test]
    fn lexes_def() {
        assert_eq!(
            toks("def add(a: Int) -> Int\n  a + 1\nend"),
            vec![
                Tok::Kw("def"), Tok::Ident("add".into()), Tok::Op("("), Tok::Ident("a".into()),
                Tok::Op(":"), Tok::Ident("Int".into()), Tok::Op(")"), Tok::Op("->"),
                Tok::Ident("Int".into()), Tok::Newline, Tok::Ident("a".into()), Tok::Op("+"),
                Tok::Int(1), Tok::Newline, Tok::Kw("end"), Tok::Newline, Tok::Eof
            ]
        );
    }

    #[test]
    fn continues_after_operator_and_collapses_blank_lines() {
        assert_eq!(
            toks("1 +\n 2\n\n\n3"),
            vec![Tok::Int(1), Tok::Op("+"), Tok::Int(2), Tok::Newline, Tok::Int(3), Tok::Newline, Tok::Eof]
        );
    }

    #[test]
    fn literals() {
        assert_eq!(
            toks("1_000 0xFF 2.5 \"a\\n\" empty? x != y # comment"),
            vec![
                Tok::Int(1000), Tok::Int(255), Tok::Float(2.5), Tok::Str("a\n".into()),
                Tok::Ident("empty?".into()), Tok::Ident("x".into()), Tok::Op("!="),
                Tok::Ident("y".into()), Tok::Newline, Tok::Eof
            ]
        );
    }

    #[test]
    fn range_is_not_float() {
        assert_eq!(toks("1..5"), vec![Tok::Int(1), Tok::Op(".."), Tok::Int(5), Tok::Newline, Tok::Eof]);
    }

    #[test]
    fn spans_are_byte_offsets() {
        let t = lex("ab cd").unwrap();
        assert_eq!(t[1].span, Span { start: 3, end: 5 });
    }

    #[test]
    fn unterminated_string_errors() {
        assert_eq!(lex("\"abc").unwrap_err().msg, "unterminated string");
    }

    #[test]
    fn unknown_char_errors() {
        assert_eq!(lex("a $ b").unwrap_err().msg, "unexpected character '$'");
    }

    #[test]
    fn interpolation_parts_with_offsets() {
        assert_eq!(
            toks("\"a #{x + 1} b #{\"in #{y}\"}\""),
            vec![
                Tok::Interp(vec![
                    RawPart::Lit("a ".into()),
                    RawPart::Code("x + 1".into(), 5),
                    RawPart::Lit(" b ".into()),
                    RawPart::Code("\"in #{y}\"".into(), 16),
                ]),
                Tok::Newline,
                Tok::Eof
            ]
        );
    }

    #[test]
    fn escaped_hash_is_literal() {
        assert_eq!(toks("\"\\#{x}\""), vec![Tok::Str("#{x}".into()), Tok::Newline, Tok::Eof]);
    }

    #[test]
    fn symbols_only_where_a_colon_cannot_be_punctuation() {
        assert_eq!(toks("f(:ok?)"), vec![Tok::Ident("f".into()), Tok::Op("("), Tok::Sym("ok?".into()), Tok::Op(")"), Tok::Newline, Tok::Eof]);
        assert_eq!(toks("x = :a_b"), vec![Tok::Ident("x".into()), Tok::Op("="), Tok::Sym("a_b".into()), Tok::Newline, Tok::Eof]);
        assert_eq!(toks("x: Int"), vec![Tok::Ident("x".into()), Tok::Op(":"), Tok::Ident("Int".into()), Tok::Newline, Tok::Eof]);
        assert_eq!(toks("{ f:v }"), vec![Tok::Op("{"), Tok::Ident("f".into()), Tok::Op(":"), Tok::Ident("v".into()), Tok::Op("}"), Tok::Newline, Tok::Eof]);
    }

    #[test]
    fn self_type_is_keyword() {
        assert_eq!(toks("Self self"), vec![Tok::Kw("Self"), Tok::Kw("self"), Tok::Newline, Tok::Eof]);
    }
}
