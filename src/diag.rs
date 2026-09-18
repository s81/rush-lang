#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub struct Span {
    pub start: u32,
    pub end: u32,
}

impl Span {
    pub fn to(self, other: Span) -> Span {
        Span { start: self.start, end: other.end }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Diagnostic {
    pub span: Span,
    pub msg: String,
    /// Secondary sites, such as where a value was moved or borrowed.
    pub notes: Vec<(Span, String)>,
}

impl Diagnostic {
    pub fn new(span: Span, msg: impl Into<String>) -> Self {
        Diagnostic { span, msg: msg.into(), notes: vec![] }
    }
    pub fn with_note(mut self, span: Span, msg: impl Into<String>) -> Self {
        self.notes.push((span, msg.into()));
        self
    }
}

/// Formats `path:line:col: error: msg`, the source line, and a caret underline, then the same
/// for each note.
pub fn render(path: &str, src: &str, d: &Diagnostic) -> String {
    let mut out = site(path, src, d.span, "error", &d.msg);
    for (span, msg) in &d.notes {
        out += &site(path, src, *span, "note", msg);
    }
    out
}

fn site(path: &str, src: &str, span: Span, kind: &str, msg: &str) -> String {
    let start = (span.start as usize).min(src.len());
    let line_start = src[..start].rfind('\n').map(|i| i + 1).unwrap_or(0);
    let line_end = src[start..].find('\n').map(|i| start + i).unwrap_or(src.len());
    let line_no = src[..start].matches('\n').count() + 1;
    let col = start - line_start + 1;
    let line = &src[line_start..line_end];
    let width = (span.end as usize).min(line_end).saturating_sub(start).max(1);
    format!("{path}:{line_no}:{col}: {kind}: {msg}\n  {line}\n  {}{}\n", " ".repeat(col - 1), "^".repeat(width))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn renders_line_and_caret() {
        let src = "def main\n  let x = 1 + true\nend\n";
        let d = Diagnostic::new(Span { start: 23, end: 27 }, "type mismatch");
        assert_eq!(
            render("a.rush", src, &d),
            format!("a.rush:2:15: error: type mismatch\n    let x = 1 + true\n{}^^^^\n", " ".repeat(16))
        );
    }

    #[test]
    fn renders_notes_after_the_error() {
        let src = "let a = 1\nlet b = a\n";
        let d = Diagnostic::new(Span { start: 18, end: 19 }, "bad").with_note(Span { start: 4, end: 5 }, "first here");
        assert_eq!(render("a.rush", src, &d), "a.rush:2:9: error: bad\n  let b = a\n          ^\na.rush:1:5: note: first here\n  let a = 1\n      ^\n");
    }
}
