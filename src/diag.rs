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
}

impl Diagnostic {
    pub fn new(span: Span, msg: impl Into<String>) -> Self {
        Diagnostic { span, msg: msg.into() }
    }
}

/// Formats `path:line:col: error: msg`, the source line, and a caret underline.
pub fn render(path: &str, src: &str, d: &Diagnostic) -> String {
    let start = (d.span.start as usize).min(src.len());
    let line_start = src[..start].rfind('\n').map(|i| i + 1).unwrap_or(0);
    let line_end = src[start..].find('\n').map(|i| start + i).unwrap_or(src.len());
    let line_no = src[..start].matches('\n').count() + 1;
    let col = start - line_start + 1;
    let line = &src[line_start..line_end];
    let width = (d.span.end as usize).min(line_end).saturating_sub(start).max(1);
    format!(
        "{path}:{line_no}:{col}: error: {}\n  {line}\n  {}{}\n",
        d.msg,
        " ".repeat(col - 1),
        "^".repeat(width)
    )
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
}
