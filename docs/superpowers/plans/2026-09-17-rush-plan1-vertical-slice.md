# Rush Plan 1: Vertical Slice Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** A `rush` binary that compiles and runs Rush programs using integers, floats, booleans, strings, functions, `let`/`let mut`, `if`/`elsif`/`else`, `while`, and calls to runtime primitives, through the full pipeline the spec describes.

**Architecture:** Lexer, recursive-descent parser, Hindley-Milner unification on the AST, lowering to a control-flow-graph MIR, C99 emission from the MIR, and a small C runtime embedded in the compiler. Every later plan extends these modules rather than replacing them: generics and traits extend `types.rs`, ownership adds `borrowck.rs` over the same MIR, and closures extend `mir.rs` and `cgen.rs`.

**Tech Stack:** Rust 1.98 stable (no crates), C99 runtime, system C compiler found at run time (`tcc` on this machine).

**Spec:** `docs/superpowers/specs/2026-09-17-rush-stage1-design.md`

## Stage 1 plan sequence

This is Plan 1 of five. Each later plan is written after the previous one ships and is checked against the spec.

| Plan | Delivers |
|---|---|
| 1 (this) | Pipeline end to end, primitives, functions, control flow, CLI, golden tests |
| 2 | `struct`, `enum`, `case`/`in` with exhaustiveness, generics with monomorphization, traits and HKT, string interpolation via `Show` |
| 3 | Ownership: moves, `Copy`, `&`/`&mut`, NLL borrow checker, drop insertion, `Gc[T]`, the GC in the runtime |
| 4 | Closures and blocks, `move`, currying and partial application, `\|>`, `?`, `>>=`, `mdo`, `for`, `loop`, ranges, symbols, `@field` |
| 5 | Stdlib (`List`, `Map`, `StringBuilder`, Functor/Applicative/Monad instances, IO), `import`, `rush test`, Linux/macOS verification |

## Global Constraints

- Rust edition 2021, no external crates. Cargo lives at `~/.cargo/bin`; in Git Bash run `export PATH="$HOME/.cargo/bin:$PATH"` before any `cargo` command.
- Generated C must be C99 and compile with `tcc -std=c99` on Windows. No GNU extensions, no `__builtin_*`.
- Every diagnostic is `path:line:col: error: message` followed by the source line and a caret underline (spec section 7).
- Naming inside generated C: Rush function `foo` becomes `rush_foo`, MIR local `n` becomes `_n`, `_0` is the return slot.
- Rush `extern "C" def name` binds to the C symbol `rush_name` in the runtime.
- Newline ends a statement unless the previous token is an operator, comma, or opening bracket.
- `let` bindings are immutable; assigning to one is a compile error.
- Tests are Rust unit tests inside each module plus golden tests in `tests/programs` (`.rush` + `.out`) and `tests/errors` (`.rush` + `.err`).
- Commit after every task with the message given in the task. Configure identity once: `git config user.name "Samer Alhaddadin"` and `git config user.email "samer.w.alhaddadin@gmail.com"` in the repo.

## File structure

| File | Responsibility |
|---|---|
| `Cargo.toml` | Crate `rush`, binary `rush` |
| `src/main.rs` | Module list, calls `driver::main` |
| `src/diag.rs` | `Span`, `Diagnostic`, `render` |
| `src/lexer.rs` | `lex(&str) -> Result<Vec<Token>, Diagnostic>` |
| `src/ast.rs` | AST types |
| `src/parser.rs` | `parse(Vec<Token>, &mut ExprId) -> Result<Program, Diagnostic>` |
| `src/types.rs` | `Type`, `check(&Program) -> Result<TypeInfo, Diagnostic>` |
| `src/mir.rs` | MIR types, `lower(&Program, &TypeInfo) -> Result<Vec<Body>, Diagnostic>`, `dump(&Body)` |
| `src/cgen.rs` | `gen(&[Body], &TypeInfo) -> String` |
| `src/driver.rs` | CLI, C compiler discovery, build directory |
| `runtime/rush_rt.h`, `runtime/rush_rt.c` | C runtime |
| `std/prelude.rush` | `extern "C"` declarations of runtime primitives |
| `tests/programs.rs` | Golden test runner |
| `tests/programs/*.rush`, `*.out` | Programs with expected stdout |
| `tests/errors/*.rush`, `*.err` | Programs with expected diagnostic substring |

---

### Task 1: Crate, diagnostics, lexer

**Files:**
- Create: `Cargo.toml`, `src/main.rs`, `src/diag.rs`, `src/lexer.rs`

**Interfaces:**
- Produces: `diag::Span { start: u32, end: u32 }` with `Span::to(self, Span) -> Span`; `diag::Diagnostic { span, msg }` with `Diagnostic::new(span, msg)`; `diag::render(path, src, &Diagnostic) -> String`; `lexer::Tok` enum, `lexer::Token { tok, span }`, `lexer::lex(&str) -> Result<Vec<Token>, Diagnostic>`.

- [ ] **Step 1: Create the crate**

`Cargo.toml`:

```toml
[package]
name = "rush"
version = "0.1.0"
edition = "2021"

[dependencies]

[[bin]]
name = "rush"
path = "src/main.rs"
```

`src/main.rs`:

```rust
mod diag;
mod lexer;

fn main() {
    println!("rush 0.1.0");
}
```

Run: `cargo build`
Expected: compiles with warnings about unused code, no errors.

- [ ] **Step 2: Write `src/diag.rs`**

```rust
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
```

- [ ] **Step 3: Write the failing lexer tests**

`src/lexer.rs`:

```rust
use crate::diag::{Diagnostic, Span};

#[derive(Debug, Clone, PartialEq)]
pub enum Tok {
    Int(i64),
    Float(f64),
    Str(String),
    Ident(String),
    Kw(&'static str),
    Op(&'static str),
    Newline,
    Eof,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub tok: Tok,
    pub span: Span,
}

pub fn lex(src: &str) -> Result<Vec<Token>, Diagnostic> {
    todo!()
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
}
```

- [ ] **Step 4: Run tests to verify they fail**

Run: `cargo test lexer`
Expected: FAIL, panics with `not yet implemented`.

- [ ] **Step 5: Implement `lex`**

Replace the `todo!()` function with:

```rust
const KEYWORDS: &[&str] = &[
    "def", "end", "let", "mut", "if", "elsif", "else", "while", "for", "in", "loop", "break",
    "next", "return", "case", "then", "struct", "enum", "trait", "impl", "import", "move", "mdo",
    "self", "true", "false", "and", "or", "not", "type", "extern",
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
                i += 1;
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
                                _ => return Err(Diagnostic::new(sp(i, i + 2), "unknown escape")),
                            });
                            i += 2;
                        }
                        _ => {
                            let ch = src[i..].chars().next().unwrap();
                            s.push(ch);
                            i += ch.len_utf8();
                        }
                    }
                }
                out.push(Token { tok: Tok::Str(s), span: sp(start, i) });
            }
            c if c.is_ascii_alphabetic() || c == b'_' => {
                let start = i;
                while i < b.len() && (b[i].is_ascii_alphanumeric() || b[i] == b'_') {
                    i += 1;
                }
                // `empty?` and `sort!` are identifiers; `x != y` is not.
                if i < b.len() && (b[i] == b'?' || b[i] == b'!') && !(i + 1 < b.len() && b[i + 1] == b'=') {
                    i += 1;
                }
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
```

- [ ] **Step 6: Run tests to verify they pass**

Run: `cargo test`
Expected: all lexer and diag tests PASS.

- [ ] **Step 7: Commit**

```bash
git add Cargo.toml src/main.rs src/diag.rs src/lexer.rs
git commit -m "feat: crate scaffold, diagnostics, lexer"
```

---

### Task 2: AST and parser

**Files:**
- Create: `src/ast.rs`, `src/parser.rs`
- Modify: `src/main.rs` (add `mod ast; mod parser;`)

**Interfaces:**
- Consumes: `lexer::{Tok, Token}`, `diag::{Span, Diagnostic}`.
- Produces: everything in `ast.rs` below, and `parser::parse(toks: Vec<Token>, next_id: &mut ExprId) -> Result<Program, Diagnostic>`. Every `Expr` has a unique `id` that later passes key on. `elsif` is desugared into a nested `If` inside the `els` block. `x += e` is desugared into `Assign(x, Binary(Add, x, e))`.

- [ ] **Step 1: Write `src/ast.rs`**

```rust
use crate::diag::Span;

pub type ExprId = u32;

#[derive(Debug, Clone, PartialEq)]
pub struct Program {
    pub items: Vec<Item>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Item {
    Def(Def),
    /// `extern "C" def ...` with no body. Binds to C symbol `rush_<name>`.
    Extern(Def),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Def {
    pub name: String,
    pub params: Vec<Param>,
    pub ret: Option<TypeExpr>,
    pub body: Block,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Param {
    pub name: String,
    pub ty: Option<TypeExpr>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeExpr {
    Name(String, Vec<TypeExpr>, Span),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    Let { name: String, mutable: bool, init: Expr, span: Span },
    Expr(Expr),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Expr {
    pub id: ExprId,
    pub kind: ExprKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ExprKind {
    Int(i64),
    Float(f64),
    Str(String),
    Bool(bool),
    Var(String),
    Unary(UnOp, Box<Expr>),
    Binary(BinOp, Box<Expr>, Box<Expr>),
    Call(Box<Expr>, Vec<Expr>),
    If { cond: Box<Expr>, then: Block, els: Option<Block> },
    While { cond: Box<Expr>, body: Block },
    Assign(Box<Expr>, Box<Expr>),
    Return(Option<Box<Expr>>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    Neg,
    Not,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add, Sub, Mul, Div, Rem,
    Eq, Ne, Lt, Le, Gt, Ge,
    And, Or,
}
```

- [ ] **Step 2: Write the failing parser tests**

`src/parser.rs` (stub plus tests):

```rust
use crate::ast::*;
use crate::diag::{Diagnostic, Span};
use crate::lexer::{Tok, Token};

pub fn parse(toks: Vec<Token>, next_id: &mut ExprId) -> Result<Program, Diagnostic> {
    todo!()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::lex;

    fn parse_src(s: &str) -> Result<Program, Diagnostic> {
        parse(lex(s).unwrap(), &mut 0)
    }

    fn only_def(p: &Program) -> &Def {
        match &p.items[0] {
            Item::Def(d) => d,
            other => panic!("expected def, got {other:?}"),
        }
    }

    #[test]
    fn parses_def_header() {
        let p = parse_src("def add(a: Int, b) -> Int\n  a + b\nend\n").unwrap();
        let d = only_def(&p);
        assert_eq!(d.name, "add");
        assert_eq!(d.params.len(), 2);
        assert_eq!(d.params[0].ty, Some(TypeExpr::Name("Int".into(), vec![], Span { start: 11, end: 14 })));
        assert_eq!(d.params[1].ty, None);
        assert!(matches!(d.ret, Some(TypeExpr::Name(ref n, _, _)) if n == "Int"));
        assert_eq!(d.body.stmts.len(), 1);
    }

    #[test]
    fn zero_param_def_without_parens() {
        let p = parse_src("def main\n  1\nend\n").unwrap();
        assert_eq!(only_def(&p).params.len(), 0);
    }

    #[test]
    fn precedence_and_associativity() {
        let p = parse_src("def main\n  1 + 2 * 3 - 4\nend\n").unwrap();
        let Stmt::Expr(e) = &only_def(&p).body.stmts[0] else { panic!() };
        // (1 + (2 * 3)) - 4
        let ExprKind::Binary(BinOp::Sub, l, r) = &e.kind else { panic!("{:?}", e.kind) };
        assert!(matches!(r.kind, ExprKind::Int(4)));
        let ExprKind::Binary(BinOp::Add, _, m) = &l.kind else { panic!() };
        assert!(matches!(m.kind, ExprKind::Binary(BinOp::Mul, _, _)));
    }

    #[test]
    fn comparison_binds_looser_than_arithmetic_and_tighter_than_and() {
        let p = parse_src("def main\n  a + 1 < b and c\nend\n").unwrap();
        let Stmt::Expr(e) = &only_def(&p).body.stmts[0] else { panic!() };
        let ExprKind::Binary(BinOp::And, l, _) = &e.kind else { panic!() };
        assert!(matches!(l.kind, ExprKind::Binary(BinOp::Lt, _, _)));
    }

    #[test]
    fn let_mut_and_compound_assign() {
        let p = parse_src("def main\n  let mut x = 1\n  x += 2\nend\n").unwrap();
        let d = only_def(&p);
        assert!(matches!(&d.body.stmts[0], Stmt::Let { name, mutable: true, .. } if name == "x"));
        let Stmt::Expr(e) = &d.body.stmts[1] else { panic!() };
        let ExprKind::Assign(lhs, rhs) = &e.kind else { panic!() };
        assert!(matches!(&lhs.kind, ExprKind::Var(n) if n == "x"));
        assert!(matches!(rhs.kind, ExprKind::Binary(BinOp::Add, _, _)));
    }

    #[test]
    fn if_elsif_else_desugars() {
        let p = parse_src("def main\n  if a\n    1\n  elsif b\n    2\n  else\n    3\n  end\nend\n").unwrap();
        let Stmt::Expr(e) = &only_def(&p).body.stmts[0] else { panic!() };
        let ExprKind::If { els: Some(els), .. } = &e.kind else { panic!() };
        let Stmt::Expr(inner) = &els.stmts[0] else { panic!() };
        let ExprKind::If { els: Some(inner_els), .. } = &inner.kind else { panic!() };
        assert!(matches!(&inner_els.stmts[0], Stmt::Expr(Expr { kind: ExprKind::Int(3), .. })));
    }

    #[test]
    fn while_call_and_return() {
        let p = parse_src("def main\n  while x < 3\n    f(x, 1)\n    return\n  end\n  return 5\nend\n").unwrap();
        let d = only_def(&p);
        let Stmt::Expr(w) = &d.body.stmts[0] else { panic!() };
        let ExprKind::While { body, .. } = &w.kind else { panic!() };
        let Stmt::Expr(c) = &body.stmts[0] else { panic!() };
        let ExprKind::Call(callee, args) = &c.kind else { panic!() };
        assert!(matches!(&callee.kind, ExprKind::Var(n) if n == "f"));
        assert_eq!(args.len(), 2);
        assert!(matches!(&body.stmts[1], Stmt::Expr(Expr { kind: ExprKind::Return(None), .. })));
        assert!(matches!(&d.body.stmts[1], Stmt::Expr(Expr { kind: ExprKind::Return(Some(_)), .. })));
    }

    #[test]
    fn extern_def() {
        let p = parse_src("extern \"C\" def puts(s: String) -> Unit\n").unwrap();
        assert!(matches!(&p.items[0], Item::Extern(d) if d.name == "puts" && d.body.stmts.is_empty()));
    }

    #[test]
    fn expr_ids_are_unique_and_continue_from_counter() {
        let mut id = 10;
        let p = parse(lex("def main\n  1 + 2\nend\n").unwrap(), &mut id).unwrap();
        let Stmt::Expr(e) = &only_def(&p).body.stmts[0] else { panic!() };
        let ExprKind::Binary(_, l, r) = &e.kind else { panic!() };
        assert_eq!((l.id, r.id, e.id), (10, 11, 12));
        assert_eq!(id, 13);
    }

    #[test]
    fn missing_end_is_an_error() {
        let err = parse_src("def main\n  1\n").unwrap_err();
        assert_eq!(err.msg, "expected `end`, found end of file");
    }

    #[test]
    fn two_expressions_on_one_line_is_an_error() {
        let err = parse_src("def main\n  1 2\nend\n").unwrap_err();
        assert_eq!(err.msg, "expected end of line, found `2`");
    }
}
```

- [ ] **Step 3: Run tests to verify they fail**

Run: `cargo test parser`
Expected: FAIL with `not yet implemented`.

- [ ] **Step 4: Implement the parser**

Replace the `todo!()` function with:

```rust
pub fn parse(toks: Vec<Token>, next_id: &mut ExprId) -> Result<Program, Diagnostic> {
    let mut p = Parser { toks, pos: 0, next_id: *next_id };
    let mut items = Vec::new();
    p.skip_newlines();
    while !p.at_eof() {
        items.push(p.item()?);
        p.skip_newlines();
    }
    *next_id = p.next_id;
    Ok(Program { items })
}

fn describe(t: &Tok) -> String {
    match t {
        Tok::Int(v) => format!("`{v}`"),
        Tok::Float(v) => format!("`{v}`"),
        Tok::Str(s) => format!("string {s:?}"),
        Tok::Ident(s) => format!("`{s}`"),
        Tok::Kw(k) => format!("`{k}`"),
        Tok::Op(o) => format!("`{o}`"),
        Tok::Newline => "end of line".to_string(),
        Tok::Eof => "end of file".to_string(),
    }
}

struct Parser {
    toks: Vec<Token>,
    pos: usize,
    next_id: ExprId,
}

impl Parser {
    fn peek(&self) -> &Tok {
        &self.toks[self.pos].tok
    }
    fn span(&self) -> Span {
        self.toks[self.pos].span
    }
    fn prev_span(&self) -> Span {
        self.toks[self.pos.saturating_sub(1)].span
    }
    fn at_eof(&self) -> bool {
        matches!(self.peek(), Tok::Eof)
    }
    fn bump(&mut self) -> Token {
        let t = self.toks[self.pos].clone();
        if !self.at_eof() {
            self.pos += 1;
        }
        t
    }
    fn skip_newlines(&mut self) {
        while matches!(self.peek(), Tok::Newline) {
            self.pos += 1;
        }
    }
    fn is_op(&self, op: &str) -> bool {
        matches!(self.peek(), Tok::Op(o) if *o == op)
    }
    fn is_kw(&self, kw: &str) -> bool {
        matches!(self.peek(), Tok::Kw(k) if *k == kw)
    }
    fn eat_op(&mut self, op: &str) -> bool {
        if self.is_op(op) {
            self.pos += 1;
            true
        } else {
            false
        }
    }
    fn eat_kw(&mut self, kw: &str) -> bool {
        if self.is_kw(kw) {
            self.pos += 1;
            true
        } else {
            false
        }
    }
    fn err(&self, what: &str) -> Diagnostic {
        Diagnostic::new(self.span(), format!("expected {what}, found {}", describe(self.peek())))
    }
    fn expect_op(&mut self, op: &str) -> Result<Span, Diagnostic> {
        if self.is_op(op) { Ok(self.bump().span) } else { Err(self.err(&format!("`{op}`"))) }
    }
    fn expect_kw(&mut self, kw: &str) -> Result<Span, Diagnostic> {
        if self.is_kw(kw) { Ok(self.bump().span) } else { Err(self.err(&format!("`{kw}`"))) }
    }
    fn expect_ident(&mut self) -> Result<(String, Span), Diagnostic> {
        match self.peek().clone() {
            Tok::Ident(s) => Ok((s, self.bump().span)),
            _ => Err(self.err("identifier")),
        }
    }
    fn expect_newline(&mut self) -> Result<(), Diagnostic> {
        if matches!(self.peek(), Tok::Newline) {
            self.skip_newlines();
            Ok(())
        } else if self.at_eof() {
            Ok(())
        } else {
            Err(self.err("end of line"))
        }
    }
    fn mk(&mut self, kind: ExprKind, span: Span) -> Expr {
        let id = self.next_id;
        self.next_id += 1;
        Expr { id, kind, span }
    }

    fn item(&mut self) -> Result<Item, Diagnostic> {
        if self.eat_kw("extern") {
            match self.peek() {
                Tok::Str(s) if s == "C" => { self.bump(); }
                _ => return Err(self.err("\"C\"")),
            }
            let def = self.def_header()?;
            self.expect_newline()?;
            return Ok(Item::Extern(def));
        }
        if self.is_kw("def") {
            return Ok(Item::Def(self.def()?));
        }
        Err(self.err("`def`"))
    }

    fn def_header(&mut self) -> Result<Def, Diagnostic> {
        let start = self.expect_kw("def")?;
        let (name, _) = self.expect_ident()?;
        let mut params = Vec::new();
        if self.eat_op("(") {
            self.skip_newlines();
            while !self.is_op(")") {
                let (pname, psp) = self.expect_ident()?;
                let ty = if self.eat_op(":") { Some(self.type_expr()?) } else { None };
                params.push(Param { name: pname, ty, span: psp });
                self.skip_newlines();
                if !self.eat_op(",") {
                    break;
                }
                self.skip_newlines();
            }
            self.expect_op(")")?;
        }
        let ret = if self.eat_op("->") { Some(self.type_expr()?) } else { None };
        Ok(Def { name, params, ret, body: Block { stmts: vec![], span: start }, span: start })
    }

    fn def(&mut self) -> Result<Def, Diagnostic> {
        let mut d = self.def_header()?;
        self.expect_newline()?;
        d.body = self.block_until(&["end"])?;
        let end = self.expect_kw("end")?;
        d.span = d.span.to(end);
        Ok(d)
    }

    fn type_expr(&mut self) -> Result<TypeExpr, Diagnostic> {
        let (name, sp) = self.expect_ident()?;
        let mut args = Vec::new();
        if self.eat_op("[") {
            loop {
                args.push(self.type_expr()?);
                if !self.eat_op(",") {
                    break;
                }
            }
            self.expect_op("]")?;
        }
        Ok(TypeExpr::Name(name, args, sp))
    }

    /// Parses statements until one of `terms` is the current keyword. Does not consume it.
    fn block_until(&mut self, terms: &[&str]) -> Result<Block, Diagnostic> {
        let start = self.span();
        let mut stmts = Vec::new();
        self.skip_newlines();
        while !terms.iter().any(|k| self.is_kw(k)) {
            if self.at_eof() {
                return Err(self.err(&format!("`{}`", terms.join("` or `"))));
            }
            stmts.push(self.stmt()?);
            self.expect_newline()?;
        }
        Ok(Block { stmts, span: start.to(self.prev_span()) })
    }

    fn stmt(&mut self) -> Result<Stmt, Diagnostic> {
        if self.is_kw("let") {
            let start = self.bump().span;
            let mutable = self.eat_kw("mut");
            let (name, _) = self.expect_ident()?;
            self.expect_op("=")?;
            let init = self.expr()?;
            let span = start.to(init.span);
            return Ok(Stmt::Let { name, mutable, init, span });
        }
        Ok(Stmt::Expr(self.expr()?))
    }

    fn expr(&mut self) -> Result<Expr, Diagnostic> {
        if self.is_kw("return") {
            let sp = self.bump().span;
            let val = if matches!(self.peek(), Tok::Newline | Tok::Eof) || self.is_kw("end") {
                None
            } else {
                Some(Box::new(self.expr()?))
            };
            let end = val.as_ref().map(|e| e.span).unwrap_or(sp);
            return Ok(self.mk(ExprKind::Return(val), sp.to(end)));
        }
        let lhs = self.binary(0)?;
        let compound: [(&str, Option<BinOp>); 5] = [
            ("=", None), ("+=", Some(BinOp::Add)), ("-=", Some(BinOp::Sub)),
            ("*=", Some(BinOp::Mul)), ("/=", Some(BinOp::Div)),
        ];
        for (op, bin) in compound {
            if self.is_op(op) {
                self.bump();
                let rhs = self.expr()?;
                let span = lhs.span.to(rhs.span);
                let rhs = match bin {
                    None => rhs,
                    Some(b) => {
                        let l = self.reid(&lhs)?;
                        self.mk(ExprKind::Binary(b, Box::new(l), Box::new(rhs)), span)
                    }
                };
                return Ok(self.mk(ExprKind::Assign(Box::new(lhs), Box::new(rhs)), span));
            }
        }
        Ok(lhs)
    }

    /// Fresh copy of an assignment target, for desugaring `x += e`.
    fn reid(&mut self, e: &Expr) -> Result<Expr, Diagnostic> {
        match &e.kind {
            ExprKind::Var(n) => Ok(self.mk(ExprKind::Var(n.clone()), e.span)),
            _ => Err(Diagnostic::new(e.span, "compound assignment target must be a variable")),
        }
    }

    fn binop_at(&self) -> Option<(BinOp, u8)> {
        match self.peek() {
            Tok::Kw("or") => Some((BinOp::Or, 1)),
            Tok::Kw("and") => Some((BinOp::And, 2)),
            Tok::Op(o) => match *o {
                "==" => Some((BinOp::Eq, 3)),
                "!=" => Some((BinOp::Ne, 3)),
                "<" => Some((BinOp::Lt, 3)),
                "<=" => Some((BinOp::Le, 3)),
                ">" => Some((BinOp::Gt, 3)),
                ">=" => Some((BinOp::Ge, 3)),
                "+" => Some((BinOp::Add, 4)),
                "-" => Some((BinOp::Sub, 4)),
                "*" => Some((BinOp::Mul, 5)),
                "/" => Some((BinOp::Div, 5)),
                "%" => Some((BinOp::Rem, 5)),
                _ => None,
            },
            _ => None,
        }
    }

    fn binary(&mut self, min_prec: u8) -> Result<Expr, Diagnostic> {
        let mut lhs = self.unary()?;
        while let Some((op, prec)) = self.binop_at() {
            if prec < min_prec {
                break;
            }
            self.bump();
            self.skip_newlines();
            let rhs = self.binary(prec + 1)?;
            let span = lhs.span.to(rhs.span);
            lhs = self.mk(ExprKind::Binary(op, Box::new(lhs), Box::new(rhs)), span);
        }
        Ok(lhs)
    }

    fn unary(&mut self) -> Result<Expr, Diagnostic> {
        if self.is_op("-") {
            let sp = self.bump().span;
            let e = self.unary()?;
            let span = sp.to(e.span);
            return Ok(self.mk(ExprKind::Unary(UnOp::Neg, Box::new(e)), span));
        }
        if self.is_kw("not") {
            let sp = self.bump().span;
            let e = self.unary()?;
            let span = sp.to(e.span);
            return Ok(self.mk(ExprKind::Unary(UnOp::Not, Box::new(e)), span));
        }
        self.postfix()
    }

    fn postfix(&mut self) -> Result<Expr, Diagnostic> {
        let mut e = self.primary()?;
        while self.is_op("(") {
            self.bump();
            self.skip_newlines();
            let mut args = Vec::new();
            while !self.is_op(")") {
                args.push(self.expr()?);
                self.skip_newlines();
                if !self.eat_op(",") {
                    break;
                }
                self.skip_newlines();
            }
            let end = self.expect_op(")")?;
            let span = e.span.to(end);
            e = self.mk(ExprKind::Call(Box::new(e), args), span);
        }
        Ok(e)
    }

    fn primary(&mut self) -> Result<Expr, Diagnostic> {
        let sp = self.span();
        match self.peek().clone() {
            Tok::Int(v) => { self.bump(); Ok(self.mk(ExprKind::Int(v), sp)) }
            Tok::Float(v) => { self.bump(); Ok(self.mk(ExprKind::Float(v), sp)) }
            Tok::Str(s) => { self.bump(); Ok(self.mk(ExprKind::Str(s), sp)) }
            Tok::Kw("true") => { self.bump(); Ok(self.mk(ExprKind::Bool(true), sp)) }
            Tok::Kw("false") => { self.bump(); Ok(self.mk(ExprKind::Bool(false), sp)) }
            Tok::Ident(n) => { self.bump(); Ok(self.mk(ExprKind::Var(n), sp)) }
            Tok::Op("(") => {
                self.bump();
                self.skip_newlines();
                let e = self.expr()?;
                self.skip_newlines();
                self.expect_op(")")?;
                Ok(e)
            }
            Tok::Kw("if") => self.if_expr(),
            Tok::Kw("while") => {
                self.bump();
                let cond = self.expr()?;
                self.expect_newline()?;
                let body = self.block_until(&["end"])?;
                let end = self.expect_kw("end")?;
                Ok(self.mk(ExprKind::While { cond: Box::new(cond), body }, sp.to(end)))
            }
            _ => Err(self.err("expression")),
        }
    }

    /// Current token is `if` or `elsif`. Consumes through the matching `end`.
    fn if_expr(&mut self) -> Result<Expr, Diagnostic> {
        let sp = self.bump().span;
        let cond = self.expr()?;
        self.expect_newline()?;
        let then = self.block_until(&["elsif", "else", "end"])?;
        let els = if self.is_kw("elsif") {
            let e = self.if_expr()?;
            let span = e.span;
            Some(Block { stmts: vec![Stmt::Expr(e)], span })
        } else if self.eat_kw("else") {
            self.expect_newline()?;
            let b = self.block_until(&["end"])?;
            self.expect_kw("end")?;
            Some(b)
        } else {
            self.expect_kw("end")?;
            None
        };
        let span = sp.to(self.prev_span());
        Ok(self.mk(ExprKind::If { cond: Box::new(cond), then, els }, span))
    }
}
```

Add `mod ast; mod parser;` to `src/main.rs`.

- [ ] **Step 5: Run tests to verify they pass**

Run: `cargo test`
Expected: all PASS.

- [ ] **Step 6: Commit**

```bash
git add src/ast.rs src/parser.rs src/main.rs
git commit -m "feat: AST and recursive-descent parser"
```

---

### Task 3: Types and inference

**Files:**
- Create: `src/types.rs`
- Modify: `src/main.rs` (add `mod types;`)

**Interfaces:**
- Consumes: `ast::*`, `diag::*`.
- Produces: `types::Type` (`Var(u32)`, `Con(String, Vec<Type>)`, `Fn(Box<Type>, Box<Type>)`), `Type::con(&str)`, `Type::unit()`, `Type::func(&[Type], Type)` (builds a curried chain), `Type::uncurry_n(&self, n) -> (Vec<Type>, Type)`, `impl Display for Type`; `types::Global { ty: Type, n_params: usize, is_extern: bool }`; `types::TypeInfo { expr_types: HashMap<ExprId, Type>, globals: HashMap<String, Global> }`; `types::check(&Program) -> Result<TypeInfo, Diagnostic>`.
- Invariants later passes rely on: every `Expr` id in a `Def` body has an entry in `expr_types` with no `Var` inside, except `Return` expressions, whose own type may stay a `Var`. Every `Global.ty` is ground. A zero-parameter def has `ty` equal to its return type and `n_params == 0`.

- [ ] **Step 1: Write the failing tests**

`src/types.rs` (stub plus tests):

```rust
use std::collections::HashMap;
use std::fmt;

use crate::ast::*;
use crate::diag::{Diagnostic, Span};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Var(u32),
    Con(String, Vec<Type>),
    Fn(Box<Type>, Box<Type>),
}

impl Type {
    pub fn con(n: &str) -> Type {
        Type::Con(n.to_string(), vec![])
    }
    pub fn unit() -> Type {
        Type::con("Unit")
    }
    /// `func(&[A, B], R)` is `A -> B -> R`. `func(&[], R)` is `R`.
    pub fn func(params: &[Type], ret: Type) -> Type {
        params.iter().rev().fold(ret, |acc, p| Type::Fn(Box::new(p.clone()), Box::new(acc)))
    }
    /// Peels exactly `n` parameters off a curried function type.
    pub fn uncurry_n(&self, n: usize) -> (Vec<Type>, Type) {
        let mut ps = Vec::new();
        let mut t = self;
        for _ in 0..n {
            match t {
                Type::Fn(a, b) => {
                    ps.push((**a).clone());
                    t = b;
                }
                _ => panic!("uncurry_n: not enough parameters in {self}"),
            }
        }
        (ps, t.clone())
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Type::Var(v) => write!(f, "?{v}"),
            Type::Con(n, args) if args.is_empty() => write!(f, "{n}"),
            Type::Con(n, args) => {
                write!(f, "{n}[")?;
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{a}")?;
                }
                write!(f, "]")
            }
            Type::Fn(a, b) => match **a {
                Type::Fn(..) => write!(f, "({a}) -> {b}"),
                _ => write!(f, "{a} -> {b}"),
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Global {
    pub ty: Type,
    pub n_params: usize,
    pub is_extern: bool,
}

#[derive(Debug, Default)]
pub struct TypeInfo {
    pub expr_types: HashMap<ExprId, Type>,
    pub globals: HashMap<String, Global>,
}

pub fn check(prog: &Program) -> Result<TypeInfo, Diagnostic> {
    todo!()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::lex;
    use crate::parser::parse;

    fn check_src(s: &str) -> Result<TypeInfo, Diagnostic> {
        let prelude = "extern \"C\" def puts(s: String) -> Unit\nextern \"C\" def int_to_s(v: Int) -> String\n";
        let mut id = 0;
        let mut p = parse(lex(prelude).unwrap(), &mut id).unwrap();
        p.items.extend(parse(lex(s).unwrap(), &mut id).unwrap().items);
        check(&p)
    }

    fn err(s: &str) -> String {
        check_src(s).unwrap_err().msg
    }

    #[test]
    fn display() {
        assert_eq!(Type::func(&[Type::con("Int"), Type::con("Bool")], Type::unit()).to_string(), "Int -> Bool -> Unit");
        let hof = Type::func(&[Type::func(&[Type::con("Int")], Type::con("Int"))], Type::con("Int"));
        assert_eq!(hof.to_string(), "(Int -> Int) -> Int");
        assert_eq!(Type::Con("List".into(), vec![Type::con("Int")]).to_string(), "List[Int]");
    }

    #[test]
    fn infers_recursive_function_with_annotations() {
        let info = check_src("def fib(n: Int) -> Int\n  if n < 2\n    n\n  else\n    fib(n - 1) + fib(n - 2)\n  end\nend\ndef main\n  puts(int_to_s(fib(5)))\nend\n").unwrap();
        assert_eq!(info.globals["fib"].ty.to_string(), "Int -> Int");
        assert_eq!(info.globals["fib"].n_params, 1);
        assert_eq!(info.globals["main"], Global { ty: Type::unit(), n_params: 0, is_extern: false });
        assert!(info.globals["puts"].is_extern);
    }

    #[test]
    fn infers_unannotated_parameters_from_use() {
        let info = check_src("def inc(x)\n  x + 1\nend\ndef main\n  inc(2)\n  ()\nend\n");
        let info = info.unwrap();
        assert_eq!(info.globals["inc"].ty.to_string(), "Int -> Int");
    }

    #[test]
    fn records_expression_types() {
        let info = check_src("def main\n  let x = 2.5 * 2.0\n  puts(\"a\")\nend\n").unwrap();
        let mut types: Vec<String> = info.expr_types.values().map(|t| t.to_string()).collect();
        types.sort();
        types.dedup();
        assert_eq!(types, vec!["Float", "String", "String -> Unit", "Unit"]);
    }

    #[test]
    fn mismatch_in_binary() {
        assert_eq!(err("def main\n  let x = 1 + true\nend\n"), "type mismatch: expected Int, found Bool");
    }

    #[test]
    fn if_branches_must_agree() {
        assert_eq!(err("def main\n  let x = if true\n    1\n  else\n    \"s\"\n  end\nend\n"), "type mismatch: expected Int, found String");
    }

    #[test]
    fn if_without_else_is_unit() {
        assert_eq!(err("def main\n  let x = if true\n    1\n  end\nend\n"), "type mismatch: expected Unit, found Int");
    }

    #[test]
    fn condition_must_be_bool() {
        assert_eq!(err("def main\n  if 1\n    ()\n  end\nend\n"), "type mismatch: expected Bool, found Int");
    }

    #[test]
    fn assign_to_immutable() {
        assert_eq!(err("def main\n  let x = 1\n  x = 2\nend\n"), "cannot assign twice to immutable variable `x`");
    }

    #[test]
    fn assign_to_mutable_ok() {
        check_src("def main\n  let mut x = 1\n  x = 2\nend\n").unwrap();
    }

    #[test]
    fn unknown_variable() {
        assert_eq!(err("def main\n  y\nend\n"), "unknown variable `y`");
    }

    #[test]
    fn too_many_arguments() {
        assert_eq!(err("def main\n  puts(\"a\", \"b\")\nend\n"), "too many arguments: `puts` takes 1");
    }

    #[test]
    fn return_type_checked() {
        assert_eq!(err("def f() -> Int\n  return \"s\"\nend\ndef main\n  f\nend\n"), "type mismatch: expected Int, found String");
    }

    #[test]
    fn missing_main() {
        assert_eq!(err("def f\n  1\nend\n"), "no `main` function defined");
    }

    #[test]
    fn unknown_type_name() {
        assert_eq!(err("def f(x: Strin) -> Int\n  1\nend\ndef main\n  ()\nend\n"), "unknown type `Strin`");
    }

    #[test]
    fn unconstrained_parameter_is_an_error() {
        assert_eq!(err("def f(x)\n  1\nend\ndef main\n  ()\nend\n"), "cannot infer the type of parameter `x`; add an annotation");
    }
}
```

Note: `()` as an expression is the unit literal. Add it to the parser in this task: in `Parser::primary`, before the parenthesised-expression case, handle `Tok::Op("(")` followed by `Tok::Op(")")` as `ExprKind::Unit`. Add `Unit` to `ExprKind` in `ast.rs`. Add this parser test:

```rust
    #[test]
    fn unit_literal() {
        let p = parse_src("def main\n  ()\nend\n").unwrap();
        assert!(matches!(&only_def(&p).body.stmts[0], Stmt::Expr(Expr { kind: ExprKind::Unit, .. })));
    }
```

Implement it in `primary` as:

```rust
            Tok::Op("(") => {
                self.bump();
                if self.is_op(")") {
                    let end = self.bump().span;
                    return Ok(self.mk(ExprKind::Unit, sp.to(end)));
                }
                self.skip_newlines();
                let e = self.expr()?;
                self.skip_newlines();
                self.expect_op(")")?;
                Ok(e)
            }
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test types`
Expected: FAIL with `not yet implemented`.

- [ ] **Step 3: Implement inference**

Replace the `todo!()` with:

```rust
struct Infer {
    subst: Vec<Option<Type>>,
}

fn occurs(v: u32, t: &Type) -> bool {
    match t {
        Type::Var(x) => *x == v,
        Type::Con(_, args) => args.iter().any(|a| occurs(v, a)),
        Type::Fn(a, b) => occurs(v, a) || occurs(v, b),
    }
}

impl Infer {
    fn fresh(&mut self) -> Type {
        self.subst.push(None);
        Type::Var(self.subst.len() as u32 - 1)
    }
    fn resolve(&self, t: &Type) -> Type {
        match t {
            Type::Var(v) => match &self.subst[*v as usize] {
                Some(t2) => self.resolve(t2),
                None => t.clone(),
            },
            Type::Con(n, args) => Type::Con(n.clone(), args.iter().map(|a| self.resolve(a)).collect()),
            Type::Fn(a, b) => Type::Fn(Box::new(self.resolve(a)), Box::new(self.resolve(b))),
        }
    }
    fn unify(&mut self, expected: &Type, found: &Type, span: Span) -> Result<(), Diagnostic> {
        let a = self.resolve(expected);
        let b = self.resolve(found);
        match (&a, &b) {
            (Type::Var(x), Type::Var(y)) if x == y => Ok(()),
            (Type::Var(v), t) | (t, Type::Var(v)) => {
                if occurs(*v, t) {
                    return Err(Diagnostic::new(span, format!("infinite type: ?{v} = {t}")));
                }
                self.subst[*v as usize] = Some(t.clone());
                Ok(())
            }
            (Type::Con(n1, a1), Type::Con(n2, a2)) if n1 == n2 && a1.len() == a2.len() => {
                for (x, y) in a1.iter().zip(a2) {
                    self.unify(x, y, span)?;
                }
                Ok(())
            }
            (Type::Fn(a1, r1), Type::Fn(a2, r2)) => {
                self.unify(a1, a2, span)?;
                self.unify(r1, r2, span)
            }
            _ => Err(Diagnostic::new(span, format!("type mismatch: expected {a}, found {b}"))),
        }
    }
}

struct Checker {
    inf: Infer,
    globals: HashMap<String, Global>,
    /// Innermost scope last. Value is (type, mutable).
    scopes: Vec<HashMap<String, (Type, bool)>>,
    expr_types: HashMap<ExprId, Type>,
    ret_ty: Type,
}

const BUILTIN_TYPES: &[&str] = &["Int", "Float", "Bool", "String", "Unit"];

fn is_ground(t: &Type) -> bool {
    match t {
        Type::Var(_) => false,
        Type::Con(_, args) => args.iter().all(is_ground),
        Type::Fn(a, b) => is_ground(a) && is_ground(b),
    }
}

impl Checker {
    fn from_ast(&self, t: &TypeExpr) -> Result<Type, Diagnostic> {
        let TypeExpr::Name(name, args, span) = t;
        let name = match name.as_str() {
            "i64" => "Int",
            "f64" => "Float",
            n => n,
        };
        if !BUILTIN_TYPES.contains(&name) {
            return Err(Diagnostic::new(*span, format!("unknown type `{name}`")));
        }
        if !args.is_empty() {
            return Err(Diagnostic::new(*span, format!("type `{name}` takes no type arguments")));
        }
        Ok(Type::con(name))
    }

    fn lookup(&self, name: &str) -> Option<(Type, bool)> {
        for s in self.scopes.iter().rev() {
            if let Some(v) = s.get(name) {
                return Some(v.clone());
            }
        }
        self.globals.get(name).map(|g| (g.ty.clone(), false))
    }

    fn record(&mut self, e: &Expr, t: Type) -> Type {
        self.expr_types.insert(e.id, t.clone());
        t
    }

    fn block(&mut self, b: &Block) -> Result<Type, Diagnostic> {
        self.scopes.push(HashMap::new());
        let mut last = Type::unit();
        for (i, s) in b.stmts.iter().enumerate() {
            match s {
                Stmt::Let { name, mutable, init, .. } => {
                    let t = self.expr(init)?;
                    self.scopes.last_mut().unwrap().insert(name.clone(), (t, *mutable));
                    last = Type::unit();
                }
                Stmt::Expr(e) => {
                    let t = self.expr(e)?;
                    last = if i + 1 == b.stmts.len() { t } else { Type::unit() };
                }
            }
        }
        self.scopes.pop();
        Ok(last)
    }

    /// Arithmetic operands must be Int or Float. An unresolved operand defaults to Int.
    fn numeric(&mut self, t: &Type, span: Span) -> Result<(), Diagnostic> {
        match self.inf.resolve(t) {
            Type::Var(_) => self.inf.unify(&Type::con("Int"), t, span),
            Type::Con(n, _) if n == "Int" || n == "Float" => Ok(()),
            other => Err(Diagnostic::new(span, format!("expected Int or Float, found {other}"))),
        }
    }

    fn expr(&mut self, e: &Expr) -> Result<Type, Diagnostic> {
        let t = match &e.kind {
            ExprKind::Int(_) => Type::con("Int"),
            ExprKind::Float(_) => Type::con("Float"),
            ExprKind::Str(_) => Type::con("String"),
            ExprKind::Bool(_) => Type::con("Bool"),
            ExprKind::Unit => Type::unit(),
            ExprKind::Var(n) => match self.lookup(n) {
                Some((t, _)) => t,
                None => return Err(Diagnostic::new(e.span, format!("unknown variable `{n}`"))),
            },
            ExprKind::Unary(UnOp::Neg, x) => {
                let t = self.expr(x)?;
                self.numeric(&t, x.span)?;
                t
            }
            ExprKind::Unary(UnOp::Not, x) => {
                let t = self.expr(x)?;
                self.inf.unify(&Type::con("Bool"), &t, x.span)?;
                Type::con("Bool")
            }
            ExprKind::Binary(op, a, b) => {
                let ta = self.expr(a)?;
                let tb = self.expr(b)?;
                match op {
                    BinOp::And | BinOp::Or => {
                        self.inf.unify(&Type::con("Bool"), &ta, a.span)?;
                        self.inf.unify(&Type::con("Bool"), &tb, b.span)?;
                        Type::con("Bool")
                    }
                    BinOp::Eq | BinOp::Ne => {
                        self.inf.unify(&ta, &tb, b.span)?;
                        Type::con("Bool")
                    }
                    BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                        self.inf.unify(&ta, &tb, b.span)?;
                        self.numeric(&ta, a.span)?;
                        Type::con("Bool")
                    }
                    _ => {
                        self.inf.unify(&ta, &tb, b.span)?;
                        self.numeric(&ta, a.span)?;
                        ta
                    }
                }
            }
            ExprKind::Call(f, args) => {
                let mut ft = self.expr(f)?;
                for (i, arg) in args.iter().enumerate() {
                    let at = self.expr(arg)?;
                    match self.inf.resolve(&ft) {
                        Type::Fn(p, r) => {
                            self.inf.unify(&p, &at, arg.span)?;
                            ft = *r;
                        }
                        Type::Var(_) => {
                            let r = self.inf.fresh();
                            self.inf.unify(&ft, &Type::Fn(Box::new(at), Box::new(r.clone())), arg.span)?;
                            ft = r;
                        }
                        _ => {
                            let name = match &f.kind {
                                ExprKind::Var(n) => n.clone(),
                                _ => "expression".to_string(),
                            };
                            return Err(Diagnostic::new(e.span, format!("too many arguments: `{name}` takes {i}")));
                        }
                    }
                }
                ft
            }
            ExprKind::If { cond, then, els } => {
                let ct = self.expr(cond)?;
                self.inf.unify(&Type::con("Bool"), &ct, cond.span)?;
                let tt = self.block(then)?;
                match els {
                    Some(b) => {
                        let et = self.block(b)?;
                        let span = b.stmts.last().map(|s| match s {
                            Stmt::Expr(e) => e.span,
                            Stmt::Let { span, .. } => *span,
                        }).unwrap_or(b.span);
                        self.inf.unify(&tt, &et, span)?;
                    }
                    None => {
                        let span = then.stmts.last().map(|s| match s {
                            Stmt::Expr(e) => e.span,
                            Stmt::Let { span, .. } => *span,
                        }).unwrap_or(then.span);
                        self.inf.unify(&Type::unit(), &tt, span)?;
                    }
                }
                tt
            }
            ExprKind::While { cond, body } => {
                let ct = self.expr(cond)?;
                self.inf.unify(&Type::con("Bool"), &ct, cond.span)?;
                self.block(body)?;
                Type::unit()
            }
            ExprKind::Assign(lhs, rhs) => {
                let ExprKind::Var(name) = &lhs.kind else {
                    return Err(Diagnostic::new(lhs.span, "assignment target must be a variable"));
                };
                let (lt, mutable) = match self.lookup(name) {
                    Some(v) => v,
                    None => return Err(Diagnostic::new(lhs.span, format!("unknown variable `{name}`"))),
                };
                if !mutable {
                    return Err(Diagnostic::new(lhs.span, format!("cannot assign twice to immutable variable `{name}`")));
                }
                self.record(lhs, lt.clone());
                let rt = self.expr(rhs)?;
                self.inf.unify(&lt, &rt, rhs.span)?;
                Type::unit()
            }
            ExprKind::Return(v) => {
                let vt = match v {
                    Some(x) => self.expr(x)?,
                    None => Type::unit(),
                };
                let span = v.as_ref().map(|x| x.span).unwrap_or(e.span);
                let ret = self.ret_ty.clone();
                self.inf.unify(&ret, &vt, span)?;
                self.inf.fresh()
            }
        };
        Ok(self.record(e, t))
    }
}

pub fn check(prog: &Program) -> Result<TypeInfo, Diagnostic> {
    let mut cx = Checker {
        inf: Infer { subst: vec![] },
        globals: HashMap::new(),
        scopes: vec![],
        expr_types: HashMap::new(),
        ret_ty: Type::unit(),
    };
    for item in &prog.items {
        let (d, is_extern) = match item {
            Item::Def(d) => (d, false),
            Item::Extern(d) => (d, true),
        };
        let mut params = Vec::new();
        for p in &d.params {
            params.push(match &p.ty {
                Some(t) => cx.from_ast(t)?,
                None => cx.inf.fresh(),
            });
        }
        let ret = match &d.ret {
            Some(t) => cx.from_ast(t)?,
            None if is_extern => Type::unit(),
            None => cx.inf.fresh(),
        };
        if cx.globals.contains_key(&d.name) {
            return Err(Diagnostic::new(d.span, format!("duplicate definition of `{}`", d.name)));
        }
        cx.globals.insert(d.name.clone(), Global { ty: Type::func(&params, ret), n_params: params.len(), is_extern });
    }
    for item in &prog.items {
        let Item::Def(d) = item else { continue };
        let (params, ret) = cx.globals[&d.name].ty.uncurry_n(d.params.len());
        let mut scope = HashMap::new();
        for (p, t) in d.params.iter().zip(&params) {
            scope.insert(p.name.clone(), (t.clone(), false));
        }
        cx.scopes.push(scope);
        cx.ret_ty = ret.clone();
        let body_ty = cx.block(&d.body)?;
        let span = d.body.stmts.last().map(|s| match s {
            Stmt::Expr(e) => e.span,
            Stmt::Let { span, .. } => *span,
        }).unwrap_or(d.span);
        cx.inf.unify(&ret, &body_ty, span)?;
        cx.scopes.pop();
    }
    if !cx.globals.contains_key("main") {
        return Err(Diagnostic::new(Span::default(), "no `main` function defined"));
    }
    let mut info = TypeInfo::default();
    for item in &prog.items {
        let d = match item {
            Item::Def(d) | Item::Extern(d) => d,
        };
        let mut g = cx.globals[&d.name].clone();
        g.ty = cx.inf.resolve(&g.ty);
        let (params, ret) = g.ty.uncurry_n(g.n_params);
        for (p, t) in d.params.iter().zip(&params) {
            if !is_ground(t) {
                return Err(Diagnostic::new(p.span, format!("cannot infer the type of parameter `{}`; add an annotation", p.name)));
            }
        }
        if !is_ground(&ret) {
            return Err(Diagnostic::new(d.span, format!("cannot infer the return type of `{}`; add an annotation", d.name)));
        }
        info.globals.insert(d.name.clone(), g);
    }
    for (id, t) in &cx.expr_types {
        info.expr_types.insert(*id, cx.inf.resolve(t));
    }
    Ok(info)
}
```

Add `mod types;` to `src/main.rs`.

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test`
Expected: all PASS. If `unconstrained_parameter_is_an_error` fails because `main` is missing, check that the test source defines `main`; it does.

- [ ] **Step 5: Commit**

```bash
git add src/types.rs src/ast.rs src/parser.rs src/main.rs
git commit -m "feat: Hindley-Milner inference for primitives and functions"
```

---

### Task 4: MIR and lowering

**Files:**
- Create: `src/mir.rs`
- Modify: `src/main.rs` (add `mod mir;`)

**Interfaces:**
- Consumes: `ast::*`, `types::{Type, TypeInfo, Global}`.
- Produces: `mir::{LocalId, BlockId, Local, Body, BasicBlock, Statement, Rvalue, Callee, Operand, Const, Terminator}`, `mir::lower(&Program, &TypeInfo) -> Result<Vec<Body>, Diagnostic>`, `mir::dump(&Body) -> String`.
- Body layout: `locals[0]` is the return slot, `locals[1..=n_params]` are the parameters, `blocks[0]` is the entry block. Every block ends in a real terminator except dead blocks created after `return`, which end in `Unreachable`.
- Plan 1 restriction: a call target must be a global name applied to exactly `n_params` arguments. Anything else is the diagnostic "only direct calls are supported in this version" or "partial application is not supported in this version". Plan 4 lifts both.

- [ ] **Step 1: Write the failing tests**

`src/mir.rs`:

```rust
use std::collections::HashMap;
use std::fmt::Write;

use crate::ast::*;
use crate::diag::Diagnostic;
use crate::types::{Type, TypeInfo};

pub type LocalId = u32;
pub type BlockId = u32;

#[derive(Debug, Clone, PartialEq)]
pub struct Local {
    pub name: String,
    pub ty: Type,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Body {
    pub name: String,
    pub locals: Vec<Local>,
    pub n_params: usize,
    pub blocks: Vec<BasicBlock>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct BasicBlock {
    pub stmts: Vec<Statement>,
    pub term: Terminator,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Statement {
    Assign(LocalId, Rvalue),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Rvalue {
    Use(Operand),
    Binary(BinOp, Operand, Operand),
    Unary(UnOp, Operand),
    Call(Callee, Vec<Operand>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Callee {
    Def(String),
    Extern(String),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Operand {
    Local(LocalId),
    Const(Const),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Const {
    Int(i64),
    Float(f64),
    Bool(bool),
    Str(String),
    Unit,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Terminator {
    Goto(BlockId),
    If(Operand, BlockId, BlockId),
    Return,
    Unreachable,
}

pub fn lower(prog: &Program, info: &TypeInfo) -> Result<Vec<Body>, Diagnostic> {
    todo!()
}

pub fn dump(b: &Body) -> String {
    todo!()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::lex;
    use crate::parser::parse;
    use crate::types::check;

    fn lower_src(s: &str) -> Result<Vec<Body>, Diagnostic> {
        let prelude = "extern \"C\" def puts(s: String) -> Unit\nextern \"C\" def int_to_s(v: Int) -> String\n";
        let mut id = 0;
        let mut p = parse(lex(prelude).unwrap(), &mut id).unwrap();
        p.items.extend(parse(lex(s).unwrap(), &mut id).unwrap().items);
        let info = check(&p)?;
        lower(&p, &info)
    }

    fn dump_fn(s: &str, name: &str) -> String {
        let bodies = lower_src(s).unwrap();
        dump(bodies.iter().find(|b| b.name == name).unwrap())
    }

    #[test]
    fn straight_line() {
        assert_eq!(
            dump_fn("def add(a: Int, b: Int) -> Int\n  let c = a + b\n  c * 2\nend\ndef main\n  ()\nend\n", "add"),
            "fn add(_1: Int, _2: Int) -> Int\n\
             bb0:\n  _3 = Add _1 _2\n  _4 = _3\n  _5 = Mul _4 2\n  _0 = _5\n  return\n"
        );
    }

    #[test]
    fn if_expression_joins() {
        assert_eq!(
            dump_fn("def f(n: Int) -> Int\n  if n < 2\n    n\n  else\n    f(n - 1)\n  end\nend\ndef main\n  ()\nend\n", "f"),
            "fn f(_1: Int) -> Int\n\
             bb0:\n  _2 = Lt _1 2\n  if _2 then bb1 else bb2\n\
             bb1:\n  _3 = _1\n  goto bb3\n\
             bb2:\n  _4 = Sub _1 1\n  _5 = call f(_4)\n  _3 = _5\n  goto bb3\n\
             bb3:\n  _0 = _3\n  return\n"
        );
    }

    #[test]
    fn while_loop_and_extern_call() {
        assert_eq!(
            dump_fn("def main\n  let mut i = 0\n  while i < 3\n    puts(int_to_s(i))\n    i += 1\n  end\nend\n", "main"),
            "fn main() -> Unit\n\
             bb0:\n  _1 = 0\n  goto bb1\n\
             bb1:\n  _2 = Lt _1 3\n  if _2 then bb2 else bb3\n\
             bb2:\n  _3 = call extern int_to_s(_1)\n  _4 = call extern puts(_3)\n  _5 = Add _1 1\n  _1 = _5\n  goto bb1\n\
             bb3:\n  _0 = ()\n  return\n"
        );
    }

    #[test]
    fn short_circuit_and() {
        assert_eq!(
            dump_fn("def f(a: Bool, b: Bool) -> Bool\n  a and b\nend\ndef main\n  ()\nend\n", "f"),
            "fn f(_1: Bool, _2: Bool) -> Bool\n\
             bb0:\n  _3 = _1\n  if _3 then bb1 else bb2\n\
             bb1:\n  _3 = _2\n  goto bb2\n\
             bb2:\n  _0 = _3\n  return\n"
        );
    }

    #[test]
    fn early_return_leaves_dead_block() {
        assert_eq!(
            dump_fn("def f(a: Int) -> Int\n  return a\n  0\nend\ndef main\n  ()\nend\n", "f"),
            "fn f(_1: Int) -> Int\n\
             bb0:\n  _0 = _1\n  return\n\
             bb1:\n  _0 = 0\n  return\n"
        );
    }

    #[test]
    fn partial_application_rejected_for_now() {
        let err = lower_src("def add(a: Int, b: Int) -> Int\n  a + b\nend\ndef main\n  add(1)\n  ()\nend\n").unwrap_err();
        assert_eq!(err.msg, "partial application is not supported in this version");
    }

    #[test]
    fn function_value_rejected_for_now() {
        let err = lower_src("def add(a: Int, b: Int) -> Int\n  a + b\nend\ndef main\n  let f = add\n  ()\nend\n").unwrap_err();
        assert_eq!(err.msg, "functions as values are not supported in this version");
    }
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test mir`
Expected: FAIL with `not yet implemented`.

- [ ] **Step 3: Implement lowering and dump**

Replace both `todo!()` functions with:

```rust
pub fn lower(prog: &Program, info: &TypeInfo) -> Result<Vec<Body>, Diagnostic> {
    let mut out = Vec::new();
    for item in &prog.items {
        if let Item::Def(d) = item {
            out.push(lower_def(d, info)?);
        }
    }
    Ok(out)
}

struct Lowerer<'a> {
    body: Body,
    cur: BlockId,
    scopes: Vec<HashMap<String, LocalId>>,
    info: &'a TypeInfo,
}

fn lower_def(d: &Def, info: &TypeInfo) -> Result<Body, Diagnostic> {
    let g = &info.globals[&d.name];
    let (params, ret) = g.ty.uncurry_n(g.n_params);
    let mut l = Lowerer {
        body: Body {
            name: d.name.clone(),
            locals: vec![Local { name: "_ret".into(), ty: ret }],
            n_params: params.len(),
            blocks: vec![BasicBlock { stmts: vec![], term: Terminator::Unreachable }],
        },
        cur: 0,
        scopes: vec![HashMap::new()],
        info,
    };
    for (p, t) in d.params.iter().zip(params) {
        let id = l.new_local(&p.name, t);
        l.scopes[0].insert(p.name.clone(), id);
    }
    let v = l.block(&d.body)?;
    l.push(Statement::Assign(0, Rvalue::Use(v)));
    l.terminate(Terminator::Return);
    Ok(l.body)
}

impl<'a> Lowerer<'a> {
    fn new_local(&mut self, name: &str, ty: Type) -> LocalId {
        self.body.locals.push(Local { name: name.to_string(), ty });
        self.body.locals.len() as LocalId - 1
    }
    fn temp(&mut self, ty: Type) -> LocalId {
        self.new_local("", ty)
    }
    fn new_block(&mut self) -> BlockId {
        self.body.blocks.push(BasicBlock { stmts: vec![], term: Terminator::Unreachable });
        self.body.blocks.len() as BlockId - 1
    }
    fn push(&mut self, s: Statement) {
        self.body.blocks[self.cur as usize].stmts.push(s);
    }
    fn terminate(&mut self, t: Terminator) {
        self.body.blocks[self.cur as usize].term = t;
    }
    fn ty(&self, e: &Expr) -> Type {
        self.info.expr_types[&e.id].clone()
    }
    fn lookup(&self, name: &str) -> Option<LocalId> {
        self.scopes.iter().rev().find_map(|s| s.get(name).copied())
    }

    fn block(&mut self, b: &Block) -> Result<Operand, Diagnostic> {
        self.scopes.push(HashMap::new());
        let mut last = Operand::Const(Const::Unit);
        for (i, s) in b.stmts.iter().enumerate() {
            match s {
                Stmt::Let { name, init, .. } => {
                    let v = self.expr(init)?;
                    let id = self.new_local(name, self.ty(init));
                    self.push(Statement::Assign(id, Rvalue::Use(v)));
                    self.scopes.last_mut().unwrap().insert(name.clone(), id);
                    last = Operand::Const(Const::Unit);
                }
                Stmt::Expr(e) => {
                    let v = self.expr(e)?;
                    last = if i + 1 == b.stmts.len() { v } else { Operand::Const(Const::Unit) };
                }
            }
        }
        self.scopes.pop();
        Ok(last)
    }

    fn expr(&mut self, e: &Expr) -> Result<Operand, Diagnostic> {
        Ok(match &e.kind {
            ExprKind::Int(v) => Operand::Const(Const::Int(*v)),
            ExprKind::Float(v) => Operand::Const(Const::Float(*v)),
            ExprKind::Str(s) => Operand::Const(Const::Str(s.clone())),
            ExprKind::Bool(b) => Operand::Const(Const::Bool(*b)),
            ExprKind::Unit => Operand::Const(Const::Unit),
            ExprKind::Var(n) => match self.lookup(n) {
                Some(id) => Operand::Local(id),
                None => {
                    let g = &self.info.globals[n];
                    if g.n_params != 0 {
                        return Err(Diagnostic::new(e.span, "functions as values are not supported in this version"));
                    }
                    let callee = if g.is_extern { Callee::Extern(n.clone()) } else { Callee::Def(n.clone()) };
                    let t = self.temp(self.ty(e));
                    self.push(Statement::Assign(t, Rvalue::Call(callee, vec![])));
                    Operand::Local(t)
                }
            },
            ExprKind::Unary(op, x) => {
                let v = self.expr(x)?;
                let t = self.temp(self.ty(e));
                self.push(Statement::Assign(t, Rvalue::Unary(*op, v)));
                Operand::Local(t)
            }
            ExprKind::Binary(op @ (BinOp::And | BinOp::Or), a, b) => {
                let t = self.temp(Type::con("Bool"));
                let va = self.expr(a)?;
                self.push(Statement::Assign(t, Rvalue::Use(va)));
                let rhs_bb = self.new_block();
                let join = self.new_block();
                let term = match op {
                    BinOp::And => Terminator::If(Operand::Local(t), rhs_bb, join),
                    _ => Terminator::If(Operand::Local(t), join, rhs_bb),
                };
                self.terminate(term);
                self.cur = rhs_bb;
                let vb = self.expr(b)?;
                self.push(Statement::Assign(t, Rvalue::Use(vb)));
                self.terminate(Terminator::Goto(join));
                self.cur = join;
                Operand::Local(t)
            }
            ExprKind::Binary(op, a, b) => {
                let va = self.expr(a)?;
                let vb = self.expr(b)?;
                let t = self.temp(self.ty(e));
                self.push(Statement::Assign(t, Rvalue::Binary(*op, va, vb)));
                Operand::Local(t)
            }
            ExprKind::Call(f, args) => {
                let name = match &f.kind {
                    ExprKind::Var(n) if self.lookup(n).is_none() => n.clone(),
                    _ => return Err(Diagnostic::new(f.span, "only direct calls are supported in this version")),
                };
                let g = &self.info.globals[&name];
                if args.len() != g.n_params {
                    return Err(Diagnostic::new(e.span, "partial application is not supported in this version"));
                }
                let callee = if g.is_extern { Callee::Extern(name) } else { Callee::Def(name) };
                let mut ops = Vec::new();
                for a in args {
                    ops.push(self.expr(a)?);
                }
                let t = self.temp(self.ty(e));
                self.push(Statement::Assign(t, Rvalue::Call(callee, ops)));
                Operand::Local(t)
            }
            ExprKind::If { cond, then, els } => {
                let c = self.expr(cond)?;
                let then_bb = self.new_block();
                let else_bb = self.new_block();
                let join = self.new_block();
                let t = self.temp(self.ty(e));
                self.terminate(Terminator::If(c, then_bb, else_bb));
                self.cur = then_bb;
                let v = self.block(then)?;
                self.push(Statement::Assign(t, Rvalue::Use(v)));
                self.terminate(Terminator::Goto(join));
                self.cur = else_bb;
                let v = match els {
                    Some(b) => self.block(b)?,
                    None => Operand::Const(Const::Unit),
                };
                self.push(Statement::Assign(t, Rvalue::Use(v)));
                self.terminate(Terminator::Goto(join));
                self.cur = join;
                Operand::Local(t)
            }
            ExprKind::While { cond, body } => {
                let head = self.new_block();
                let body_bb = self.new_block();
                let exit = self.new_block();
                self.terminate(Terminator::Goto(head));
                self.cur = head;
                let c = self.expr(cond)?;
                self.terminate(Terminator::If(c, body_bb, exit));
                self.cur = body_bb;
                self.block(body)?;
                self.terminate(Terminator::Goto(head));
                self.cur = exit;
                Operand::Const(Const::Unit)
            }
            ExprKind::Assign(lhs, rhs) => {
                let v = self.expr(rhs)?;
                let ExprKind::Var(n) = &lhs.kind else { unreachable!("type checker rejects other targets") };
                let id = self.lookup(n).expect("type checker resolved the variable");
                self.push(Statement::Assign(id, Rvalue::Use(v)));
                Operand::Const(Const::Unit)
            }
            ExprKind::Return(v) => {
                let val = match v {
                    Some(x) => self.expr(x)?,
                    None => Operand::Const(Const::Unit),
                };
                self.push(Statement::Assign(0, Rvalue::Use(val)));
                self.terminate(Terminator::Return);
                self.cur = self.new_block();
                Operand::Const(Const::Unit)
            }
        })
    }
}

fn fmt_operand(o: &Operand) -> String {
    match o {
        Operand::Local(id) => format!("_{id}"),
        Operand::Const(Const::Int(v)) => v.to_string(),
        Operand::Const(Const::Float(v)) => format!("{v:?}"),
        Operand::Const(Const::Bool(v)) => v.to_string(),
        Operand::Const(Const::Str(s)) => format!("{s:?}"),
        Operand::Const(Const::Unit) => "()".to_string(),
    }
}

pub fn dump(b: &Body) -> String {
    let mut s = String::new();
    let params: Vec<String> = (1..=b.n_params).map(|i| format!("_{i}: {}", b.locals[i].ty)).collect();
    writeln!(s, "fn {}({}) -> {}", b.name, params.join(", "), b.locals[0].ty).unwrap();
    for (i, bb) in b.blocks.iter().enumerate() {
        writeln!(s, "bb{i}:").unwrap();
        for st in &bb.stmts {
            let Statement::Assign(id, rv) = st;
            let rhs = match rv {
                Rvalue::Use(o) => fmt_operand(o),
                Rvalue::Binary(op, a, c) => format!("{op:?} {} {}", fmt_operand(a), fmt_operand(c)),
                Rvalue::Unary(op, a) => format!("{op:?} {}", fmt_operand(a)),
                Rvalue::Call(callee, args) => {
                    let args: Vec<String> = args.iter().map(fmt_operand).collect();
                    match callee {
                        Callee::Def(n) => format!("call {n}({})", args.join(", ")),
                        Callee::Extern(n) => format!("call extern {n}({})", args.join(", ")),
                    }
                }
            };
            writeln!(s, "  _{id} = {rhs}").unwrap();
        }
        match &bb.term {
            Terminator::Goto(t) => writeln!(s, "  goto bb{t}").unwrap(),
            Terminator::If(c, a, d) => writeln!(s, "  if {} then bb{a} else bb{d}", fmt_operand(c)).unwrap(),
            Terminator::Return => writeln!(s, "  return").unwrap(),
            Terminator::Unreachable => writeln!(s, "  unreachable").unwrap(),
        }
    }
    s
}
```

Add `mod mir;` to `src/main.rs`.

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test`
Expected: all PASS. If a dump test differs only in local numbering, the numbering in the plan is authoritative: temporaries are allocated in evaluation order, and the `if` result temp is allocated after the condition and after the three blocks are created.

- [ ] **Step 5: Commit**

```bash
git add src/mir.rs src/main.rs
git commit -m "feat: MIR lowering with CFG, short-circuit, and early return"
```

---

### Task 5: C runtime and code generation

**Files:**
- Create: `runtime/rush_rt.h`, `runtime/rush_rt.c`, `std/prelude.rush`, `src/cgen.rs`
- Modify: `src/main.rs` (add `mod cgen;`)

**Interfaces:**
- Consumes: `mir::*`, `types::{Type, TypeInfo}`.
- Produces: `cgen::gen(bodies: &[Body], info: &TypeInfo) -> String` returning a complete C translation unit that includes `rush_rt.h` and defines `main`. C symbol for Rush global `f` is `rush_f`. Runtime primitives: `rush_puts`, `rush_print`, `rush_int_to_s`, `rush_float_to_s`, `rush_bool_to_s`, `rush_str_eq`, `rush_div_i64`, `rush_rem_i64`, `rush_str_lit`, `rush_panic`, `rush_unreachable`, `rush_rt_init`.

- [ ] **Step 1: Write the runtime header**

`runtime/rush_rt.h`:

```c
#ifndef RUSH_RT_H
#define RUSH_RT_H
#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

typedef struct { char _; } rush_unit;
#define RUSH_UNIT ((rush_unit){0})

/* Immutable UTF-8 string view. Plan 3 adds ownership and drop. */
typedef struct { const uint8_t *ptr; size_t len; } rush_str;

void rush_rt_init(int argc, char **argv);
void rush_panic(const char *msg);
void rush_unreachable(void);
rush_str rush_str_lit(const char *s, size_t len);
bool rush_str_eq(rush_str a, rush_str b);
int64_t rush_div_i64(int64_t a, int64_t b);
int64_t rush_rem_i64(int64_t a, int64_t b);

/* Primitives declared in std/prelude.rush as extern "C". */
rush_unit rush_puts(rush_str s);
rush_unit rush_print(rush_str s);
rush_str rush_int_to_s(int64_t v);
rush_str rush_float_to_s(double v);
rush_str rush_bool_to_s(bool v);

#endif
```

- [ ] **Step 2: Write the runtime implementation**

`runtime/rush_rt.c`:

```c
#include "rush_rt.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void rush_rt_init(int argc, char **argv) {
    (void)argc;
    (void)argv;
}

void rush_panic(const char *msg) {
    fprintf(stderr, "panic: %s\n", msg);
    fflush(stderr);
    abort();
}

void rush_unreachable(void) {
    rush_panic("entered unreachable code");
}

rush_str rush_str_lit(const char *s, size_t len) {
    rush_str r;
    r.ptr = (const uint8_t *)s;
    r.len = len;
    return r;
}

bool rush_str_eq(rush_str a, rush_str b) {
    return a.len == b.len && memcmp(a.ptr, b.ptr, a.len) == 0;
}

int64_t rush_div_i64(int64_t a, int64_t b) {
    if (b == 0) rush_panic("division by zero");
    if (a == INT64_MIN && b == -1) rush_panic("integer overflow in division");
    return a / b;
}

int64_t rush_rem_i64(int64_t a, int64_t b) {
    if (b == 0) rush_panic("remainder by zero");
    if (a == INT64_MIN && b == -1) return 0;
    return a % b;
}

rush_unit rush_puts(rush_str s) {
    fwrite(s.ptr, 1, s.len, stdout);
    fputc('\n', stdout);
    return RUSH_UNIT;
}

rush_unit rush_print(rush_str s) {
    fwrite(s.ptr, 1, s.len, stdout);
    return RUSH_UNIT;
}

/* ponytail: these allocate and never free; Plan 3 makes String owned and dropped. */
static rush_str rush_str_own(const char *buf, size_t len) {
    uint8_t *p = (uint8_t *)malloc(len ? len : 1);
    if (!p) rush_panic("out of memory");
    memcpy(p, buf, len);
    rush_str r;
    r.ptr = p;
    r.len = len;
    return r;
}

rush_str rush_int_to_s(int64_t v) {
    char buf[32];
    int n = snprintf(buf, sizeof buf, "%lld", (long long)v);
    return rush_str_own(buf, (size_t)n);
}

rush_str rush_float_to_s(double v) {
    char buf[64];
    int n = snprintf(buf, sizeof buf, "%.15g", v);
    /* Print whole floats as `2.0` like Ruby, not `2`. */
    if (strspn(buf, "-0123456789") == (size_t)n) {
        buf[n++] = '.';
        buf[n++] = '0';
        buf[n] = 0;
    }
    return rush_str_own(buf, (size_t)n);
}

rush_str rush_bool_to_s(bool v) {
    return v ? rush_str_lit("true", 4) : rush_str_lit("false", 5);
}
```

- [ ] **Step 3: Write the prelude**

`std/prelude.rush`:

```ruby
extern "C" def puts(s: String) -> Unit
extern "C" def print(s: String) -> Unit
extern "C" def int_to_s(v: Int) -> String
extern "C" def float_to_s(v: Float) -> String
extern "C" def bool_to_s(v: Bool) -> String
```

- [ ] **Step 4: Compile the runtime alone to catch C errors early**

Run (Git Bash, from the repo root):

```bash
tcc -std=c99 -c -o /dev/null runtime/rush_rt.c -I runtime
```

Expected: no output, exit 0. On tcc, if `-o /dev/null` fails, use `-o "$TMP/rt.o"`.

- [ ] **Step 5: Write the failing cgen tests**

`src/cgen.rs`:

```rust
use std::fmt::Write;

use crate::ast::{BinOp, UnOp};
use crate::mir::*;
use crate::types::{Type, TypeInfo};

pub fn gen(bodies: &[Body], info: &TypeInfo) -> String {
    todo!()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::lex;
    use crate::parser::parse;
    use crate::types::check;

    fn gen_src(s: &str) -> String {
        let prelude = include_str!("../std/prelude.rush");
        let mut id = 0;
        let mut p = parse(lex(prelude).unwrap(), &mut id).unwrap();
        p.items.extend(parse(lex(s).unwrap(), &mut id).unwrap().items);
        let info = check(&p).unwrap();
        let bodies = lower(&p, &info).unwrap();
        gen(&bodies, &info)
    }

    #[test]
    fn emits_prototype_definition_and_main() {
        let c = gen_src("def fib(n: Int) -> Int\n  if n < 2\n    n\n  else\n    fib(n - 1) + fib(n - 2)\n  end\nend\ndef main\n  puts(int_to_s(fib(10)))\nend\n");
        assert!(c.starts_with("#include \"rush_rt.h\"\n"));
        assert!(c.contains("static int64_t rush_fib(int64_t _1);\n"));
        assert!(c.contains("static rush_unit rush_main(void);\n"));
        assert!(c.contains("static int64_t rush_fib(int64_t _1) {\n"));
        assert!(c.contains("  _2 = (_1 < INT64_C(2));\n"));
        assert!(c.contains("  if (_2) goto bb1; else goto bb2;\n"));
        assert!(c.contains("  _5 = rush_fib(_4);\n"));
        assert!(c.contains("  return _0;\n"));
        assert!(c.contains("int main(int argc, char **argv) {\n  rush_rt_init(argc, argv);\n  rush_main();\n  return 0;\n}\n"));
    }

    #[test]
    fn string_literals_are_octal_escaped_with_length() {
        let c = gen_src("def main\n  puts(\"a\\\"b\\n\")\nend\n");
        assert!(c.contains("rush_str_lit(\"a\\042b\\012\", 4)"), "{c}");
    }

    #[test]
    fn division_and_string_equality_call_the_runtime() {
        let c = gen_src("def main\n  let a = 7 / 2\n  let b = 7 % 2\n  let c = \"x\" == \"y\"\n  ()\nend\n");
        assert!(c.contains("rush_div_i64("));
        assert!(c.contains("rush_rem_i64("));
        assert!(c.contains("rush_str_eq("));
    }

    #[test]
    fn float_division_is_inline() {
        let c = gen_src("def main\n  let a = 7.0 / 2.0\n  ()\nend\n");
        assert!(c.contains(" / "));
        assert!(!c.contains("rush_div_i64"));
    }

    #[test]
    fn unit_and_bool_constants() {
        let c = gen_src("def main\n  let u = ()\n  let b = not true\n  ()\nend\n");
        assert!(c.contains("RUSH_UNIT"));
        assert!(c.contains("(!true)"));
    }
}
```

- [ ] **Step 6: Run tests to verify they fail**

Run: `cargo test cgen`
Expected: FAIL with `not yet implemented`.

- [ ] **Step 7: Implement code generation**

Replace the `todo!()` with:

```rust
fn c_type(t: &Type) -> &'static str {
    match t {
        Type::Con(n, _) => match n.as_str() {
            "Int" => "int64_t",
            "Float" => "double",
            "Bool" => "bool",
            "String" => "rush_str",
            "Unit" => "rush_unit",
            _ => panic!("cgen: unsupported type {t}"),
        },
        _ => panic!("cgen: non-ground type {t}"),
    }
}

fn is_named(t: &Type, name: &str) -> bool {
    matches!(t, Type::Con(n, _) if n == name)
}

fn c_string_lit(s: &str) -> String {
    let mut out = String::from("\"");
    for b in s.bytes() {
        match b {
            b'"' | b'\\' => write!(out, "\\{:03o}", b).unwrap(),
            0x20..=0x7e => out.push(b as char),
            _ => write!(out, "\\{:03o}", b).unwrap(),
        }
    }
    out.push('"');
    out
}

fn operand(o: &Operand) -> String {
    match o {
        Operand::Local(id) => format!("_{id}"),
        Operand::Const(Const::Int(v)) => format!("INT64_C({v})"),
        Operand::Const(Const::Float(v)) => {
            if v.is_finite() && v.fract() == 0.0 { format!("{v:.1}") } else { format!("{v:?}") }
        }
        Operand::Const(Const::Bool(v)) => v.to_string(),
        Operand::Const(Const::Str(s)) => format!("rush_str_lit({}, {})", c_string_lit(s), s.len()),
        Operand::Const(Const::Unit) => "RUSH_UNIT".to_string(),
    }
}

fn operand_type(b: &Body, o: &Operand) -> Type {
    match o {
        Operand::Local(id) => b.locals[*id as usize].ty.clone(),
        Operand::Const(Const::Int(_)) => Type::con("Int"),
        Operand::Const(Const::Float(_)) => Type::con("Float"),
        Operand::Const(Const::Bool(_)) => Type::con("Bool"),
        Operand::Const(Const::Str(_)) => Type::con("String"),
        Operand::Const(Const::Unit) => Type::unit(),
    }
}

fn signature(b: &Body) -> String {
    let params: Vec<String> = (1..=b.n_params).map(|i| format!("{} _{i}", c_type(&b.locals[i].ty))).collect();
    let params = if params.is_empty() { "void".to_string() } else { params.join(", ") };
    format!("static {} rush_{}({})", c_type(&b.locals[0].ty), b.name, params)
}

fn rvalue(b: &Body, rv: &Rvalue) -> String {
    match rv {
        Rvalue::Use(o) => operand(o),
        Rvalue::Unary(UnOp::Neg, o) => format!("(-{})", operand(o)),
        Rvalue::Unary(UnOp::Not, o) => format!("(!{})", operand(o)),
        Rvalue::Binary(op, x, y) => {
            let t = operand_type(b, x);
            let (l, r) = (operand(x), operand(y));
            let is_int = is_named(&t, "Int");
            match op {
                BinOp::Div if is_int => format!("rush_div_i64({l}, {r})"),
                BinOp::Rem if is_int => format!("rush_rem_i64({l}, {r})"),
                BinOp::Rem => format!("fmod({l}, {r})"),
                BinOp::Eq if is_named(&t, "String") => format!("rush_str_eq({l}, {r})"),
                BinOp::Ne if is_named(&t, "String") => format!("(!rush_str_eq({l}, {r}))"),
                _ => {
                    let sym = match op {
                        BinOp::Add => "+", BinOp::Sub => "-", BinOp::Mul => "*", BinOp::Div => "/",
                        BinOp::Rem => "%", BinOp::Eq => "==", BinOp::Ne => "!=", BinOp::Lt => "<",
                        BinOp::Le => "<=", BinOp::Gt => ">", BinOp::Ge => ">=", BinOp::And => "&&",
                        BinOp::Or => "||",
                    };
                    format!("({l} {sym} {r})")
                }
            }
        }
        Rvalue::Call(callee, args) => {
            let name = match callee {
                Callee::Def(n) | Callee::Extern(n) => n,
            };
            let args: Vec<String> = args.iter().map(operand).collect();
            format!("rush_{name}({})", args.join(", "))
        }
    }
}

pub fn gen(bodies: &[Body], _info: &TypeInfo) -> String {
    let mut c = String::new();
    c.push_str("#include \"rush_rt.h\"\n#include <math.h>\n\n");
    for b in bodies {
        writeln!(c, "{};", signature(b)).unwrap();
    }
    c.push('\n');
    for b in bodies {
        writeln!(c, "{} {{", signature(b)).unwrap();
        for (i, l) in b.locals.iter().enumerate() {
            if i >= 1 && i <= b.n_params {
                continue;
            }
            writeln!(c, "  {} _{i};", c_type(&l.ty)).unwrap();
        }
        for (i, bb) in b.blocks.iter().enumerate() {
            writeln!(c, "bb{i}:").unwrap();
            for st in &bb.stmts {
                let Statement::Assign(id, rv) = st;
                writeln!(c, "  _{id} = {};", rvalue(b, rv)).unwrap();
            }
            match &bb.term {
                Terminator::Goto(t) => writeln!(c, "  goto bb{t};").unwrap(),
                Terminator::If(cond, a, d) => writeln!(c, "  if ({}) goto bb{a}; else goto bb{d};", operand(cond)).unwrap(),
                Terminator::Return => writeln!(c, "  return _0;").unwrap(),
                Terminator::Unreachable => writeln!(c, "  rush_unreachable();\n  return _0;").unwrap(),
            }
        }
        c.push_str("}\n\n");
    }
    c.push_str("int main(int argc, char **argv) {\n  rush_rt_init(argc, argv);\n  rush_main();\n  return 0;\n}\n");
    c
}
```

Add `mod cgen;` to `src/main.rs`. Note: `rush_unreachable` never returns, but the `return _0;` after it keeps C compilers from warning about a missing return.

- [ ] **Step 8: Run tests to verify they pass**

Run: `cargo test`
Expected: all PASS.

- [ ] **Step 9: Commit**

```bash
git add runtime std src/cgen.rs src/main.rs
git commit -m "feat: C runtime and C99 code generation from MIR"
```

---

### Task 6: Driver, CLI, and golden tests

**Files:**
- Create: `src/driver.rs`, `tests/programs.rs`, `tests/programs/hello.rush`, `tests/programs/hello.out`, `tests/programs/fib.rush`, `tests/programs/fib.out`, `tests/programs/floats.rush`, `tests/programs/floats.out`, `tests/errors/mismatch.rush`, `tests/errors/mismatch.err`, `tests/errors/immutable.rush`, `tests/errors/immutable.err`, `.gitignore` (already has `.rush-build/` and `target/`)
- Modify: `src/main.rs`

**Interfaces:**
- Consumes: every module above.
- Produces: `rush build <file.rush> [--debug]` writes `<dir>/.rush-build/<stem>.c`, `rush_rt.c`, `rush_rt.h`, compiles to `<dir>/<stem>.exe` on Windows or `<dir>/<stem>` elsewhere, exit 0 on success, 1 on compile error (diagnostic on stderr), 2 on usage error. `rush run <file.rush>` builds then runs, returning the program's exit code. `driver::compile_to_c(path, src) -> Result<String, String>` is the pure part, used by tests.

- [ ] **Step 1: Write the golden programs**

`tests/programs/hello.rush`:

```ruby
def main
  puts("Hello, Rush!")
end
```

`tests/programs/hello.out`:

```
Hello, Rush!
```

`tests/programs/fib.rush`:

```ruby
def fib(n: Int) -> Int
  if n < 2
    n
  else
    fib(n - 1) + fib(n - 2)
  end
end

def main
  let mut i = 0
  while i < 10
    puts(int_to_s(fib(i)))
    i += 1
  end
end
```

`tests/programs/fib.out`:

```
0
1
1
2
3
5
8
13
21
34
```

`tests/programs/floats.rush`:

```ruby
def avg(a: Float, b: Float) -> Float
  (a + b) / 2.0
end

def main
  puts(float_to_s(avg(1.0, 2.0)))
  puts(float_to_s(4.0))
  puts(bool_to_s(1 < 2 and not false))
  puts(int_to_s(7 / 2))
  puts(int_to_s(-7 % 3))
  puts(bool_to_s("a" == "a"))
  puts(bool_to_s("a" != "a"))
end
```

`tests/programs/floats.out`:

```
1.5
4.0
true
3
-1
true
false
```

`tests/errors/mismatch.rush`:

```ruby
def main
  let x = 1 + true
end
```

`tests/errors/mismatch.err`:

```
mismatch.rush:2:15: error: type mismatch: expected Int, found Bool
```

`tests/errors/immutable.rush`:

```ruby
def main
  let x = 1
  x = 2
end
```

`tests/errors/immutable.err`:

```
immutable.rush:3:3: error: cannot assign twice to immutable variable `x`
```

- [ ] **Step 2: Write the golden test runner**

`tests/programs.rs`:

```rust
use std::path::{Path, PathBuf};
use std::process::Command;

fn rush(args: &[&str], cwd: &Path) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_rush"))
        .args(args)
        .current_dir(cwd)
        .output()
        .expect("failed to spawn rush")
}

fn cases(dir: &str, ext: &str) -> Vec<(PathBuf, String)> {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests").join(dir);
    let mut out = Vec::new();
    for entry in std::fs::read_dir(&dir).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().map_or(true, |e| e != "rush") {
            continue;
        }
        let expected = std::fs::read_to_string(path.with_extension(ext)).unwrap().replace("\r\n", "\n");
        out.push((path, expected));
    }
    assert!(!out.is_empty(), "no test cases in {}", dir.display());
    out.sort();
    out
}

#[test]
fn programs_produce_expected_output() {
    for (path, expected) in cases("programs", "out") {
        let dir = path.parent().unwrap();
        let file = path.file_name().unwrap().to_str().unwrap();
        let out = rush(&["run", file], dir);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(out.status.success(), "{file}: rush run failed\n{stderr}");
        let stdout = String::from_utf8_lossy(&out.stdout).replace("\r\n", "\n");
        assert_eq!(stdout, expected, "{file}: stdout mismatch");
    }
}

#[test]
fn error_programs_report_expected_diagnostic() {
    for (path, expected) in cases("errors", "err") {
        let dir = path.parent().unwrap();
        let file = path.file_name().unwrap().to_str().unwrap();
        let out = rush(&["build", file], dir);
        assert_eq!(out.status.code(), Some(1), "{file}: expected exit code 1");
        let stderr = String::from_utf8_lossy(&out.stderr).replace("\r\n", "\n");
        assert!(stderr.contains(expected.trim_end()), "{file}: stderr was:\n{stderr}\nexpected to contain:\n{expected}");
    }
}
```

- [ ] **Step 3: Run tests to verify they fail**

Run: `cargo test --test programs`
Expected: FAIL. The binary prints `rush 0.1.0` and exits 0, so `programs_produce_expected_output` fails on stdout mismatch and `error_programs_report_expected_diagnostic` fails on the exit code.

- [ ] **Step 4: Implement the driver**

`src/driver.rs`:

```rust
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use crate::{cgen, diag, lexer, mir, parser, types};

const PRELUDE: &str = include_str!("../std/prelude.rush");
const RT_C: &str = include_str!("../runtime/rush_rt.c");
const RT_H: &str = include_str!("../runtime/rush_rt.h");

pub fn main(args: Vec<String>) -> i32 {
    match args.first().map(String::as_str) {
        Some("build") => build(&args[1..], false),
        Some("run") => build(&args[1..], true),
        _ => {
            eprintln!("usage: rush build <file.rush> [--debug]\n       rush run <file.rush> [--debug]");
            2
        }
    }
}

/// Runs the whole front end and returns C source, or a rendered diagnostic.
pub fn compile_to_c(path: &str, src: &str) -> Result<String, String> {
    let go = || -> Result<String, diag::Diagnostic> {
        let mut id = 0;
        let mut prog = parser::parse(lexer::lex(PRELUDE)?, &mut id)?;
        prog.items.extend(parser::parse(lexer::lex(src)?, &mut id)?.items);
        let info = types::check(&prog)?;
        let bodies = mir::lower(&prog, &info)?;
        Ok(cgen::gen(&bodies, &info))
    };
    go().map_err(|d| diag::render(path, src, &d))
}

fn find_cc() -> Option<Vec<String>> {
    if let Ok(cc) = std::env::var("RUSH_CC") {
        return Some(cc.split_whitespace().map(str::to_string).collect());
    }
    let candidates: [&[&str]; 5] = [&["cc"], &["gcc"], &["clang"], &["tcc"], &["zig", "cc"]];
    for cand in candidates {
        let ok = Command::new(cand[0])
            .args(&cand[1..])
            .arg("-v")
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .map(|s| s.success())
            .unwrap_or(false);
        if ok {
            return Some(cand.iter().map(|s| s.to_string()).collect());
        }
    }
    None
}

fn build(args: &[String], run: bool) -> i32 {
    let Some(path) = args.iter().find(|a| !a.starts_with("--")) else {
        eprintln!("error: no input file");
        return 2;
    };
    let debug = args.iter().any(|a| a == "--debug");
    let src = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: cannot read {path}: {e}");
            return 2;
        }
    };
    let c = match compile_to_c(path, &src) {
        Ok(c) => c,
        Err(msg) => {
            eprint!("{msg}");
            return 1;
        }
    };
    let src_path = Path::new(path);
    let stem = src_path.file_stem().unwrap().to_string_lossy().to_string();
    let parent = src_path.parent().filter(|p| !p.as_os_str().is_empty()).unwrap_or(Path::new("."));
    let build_dir = parent.join(".rush-build");
    let exe: PathBuf = parent.join(if cfg!(windows) { format!("{stem}.exe") } else { stem.clone() });
    let write = |name: &str, data: &str| std::fs::write(build_dir.join(name), data);
    if let Err(e) = std::fs::create_dir_all(&build_dir)
        .and_then(|_| write(&format!("{stem}.c"), &c))
        .and_then(|_| write("rush_rt.c", RT_C))
        .and_then(|_| write("rush_rt.h", RT_H))
    {
        eprintln!("error: cannot write build directory {}: {e}", build_dir.display());
        return 2;
    }
    let Some(cc) = find_cc() else {
        eprintln!("error: no C compiler found; install gcc, clang, or tcc, or set RUSH_CC");
        return 2;
    };
    let mut cmd = Command::new(&cc[0]);
    cmd.args(&cc[1..]);
    cmd.arg("-std=c99");
    if debug {
        cmd.args(["-O0", "-g"]);
    } else {
        cmd.arg("-O2");
    }
    cmd.arg("-I").arg(&build_dir);
    cmd.arg("-o").arg(&exe);
    cmd.arg(build_dir.join(format!("{stem}.c")));
    cmd.arg(build_dir.join("rush_rt.c"));
    if !cfg!(windows) {
        cmd.arg("-lm");
    }
    match cmd.status() {
        Ok(s) if s.success() => {}
        Ok(s) => {
            eprintln!("error: C compiler exited with {s}");
            return 1;
        }
        Err(e) => {
            eprintln!("error: cannot run {}: {e}", cc[0]);
            return 2;
        }
    }
    if !run {
        return 0;
    }
    let exe_abs = std::fs::canonicalize(&exe).unwrap_or(exe);
    match Command::new(&exe_abs).status() {
        Ok(s) => s.code().unwrap_or(1),
        Err(e) => {
            eprintln!("error: cannot run {}: {e}", exe_abs.display());
            return 2;
        }
    }
}
```

`src/main.rs`:

```rust
mod ast;
mod cgen;
mod diag;
mod driver;
mod lexer;
mod mir;
mod parser;
mod types;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    std::process::exit(driver::main(args));
}
```

- [ ] **Step 5: Run the whole suite**

Run: `cargo test`
Expected: all unit tests and both golden tests PASS. If `programs_produce_expected_output` fails with "no C compiler found", confirm `tcc -v` exits 0 in the same shell.

- [ ] **Step 6: Try it by hand**

Run from the repo root:

```bash
cargo run -q -- run tests/programs/fib.rush
```

Expected: the ten Fibonacci numbers, and `tests/programs/fib.exe` plus `tests/programs/.rush-build/` exist.

- [ ] **Step 7: Ignore build outputs and commit**

Append to `.gitignore`:

```
tests/programs/*
!tests/programs/*.rush
!tests/programs/*.out
```

```bash
git add .gitignore src/driver.rs src/main.rs tests
git commit -m "feat: rush build/run CLI and golden test suite"
```

---

### Task 7: Windows binary sanity and handoff note

**Files:**
- Create: `README.md`

- [ ] **Step 1: Release build and clean checkout check**

```bash
cargo build --release
./target/release/rush.exe run tests/programs/hello.rush
git status --short
```

Expected: `Hello, Rush!` and an empty `git status`. If build products show up in status, fix `.gitignore` in this task.

- [ ] **Step 2: Write README.md**

```markdown
# Rush

A compiled language: Go-style single binaries, Haskell-style types, Rust-style ownership, Ruby-style syntax.
Design: `docs/superpowers/specs/2026-09-17-rush-stage1-design.md`.

## Build

    export PATH="$HOME/.cargo/bin:$PATH"   # Git Bash on Windows
    cargo build --release

Needs a C compiler on PATH (`cc`, `gcc`, `clang`, `tcc`, or `zig cc`) or `RUSH_CC="path/to/cc"`.

## Use

    rush build hello.rush     # writes hello(.exe) next to the source
    rush run hello.rush       # build and run
    rush build hello.rush --debug

## Test

    cargo test
```

- [ ] **Step 3: Commit**

```bash
git add README.md .gitignore
git commit -m "docs: README with build and usage"
```

---

## Self-review against the spec

- **Covered by this plan:** lexical rules (newline continuation, comments, integer and float literals, strings with escapes, `?`/`!` suffixes), `def`/`end`, `let`/`let mut` with immutability enforced, `if`/`elsif`/`else`, `while`, `return`, compound assignment, calls with parentheses, zero-arg calls by bare name, `extern "C" def`, curried function types, HM unification, C99 emission via a CFG MIR, `rush build`/`rush run`, C compiler discovery order, `.rush-build/` layout, diagnostics format from section 7, golden tests from section 6, division by zero panics.
- **Deferred to Plan 2:** `struct`, `enum`, `case`/`in`, exhaustiveness, generics and `[T]` syntax, traits, HKT, associated types, `Show` and interpolation, `Char`, `Symbol`, tuples, sized integer types beyond `Int`, `f32`, literal defaulting by context.
- **Deferred to Plan 3:** moves, `Copy`, `&`/`&mut`, borrow checker, drop insertion, `Drop`, `Gc[T]`, the GC, owned `String` freeing (the runtime comment marks the leak), integer overflow checks in debug builds.
- **Deferred to Plan 4:** blocks and closures, `move`, partial application and function values (the two MIR diagnostics mark the spot), `|>`, `?`, `>>=`, `mdo`, `for`, `loop`, `break`, `next`, ranges, `@field`, `[]` and `{}` literals.
- **Deferred to Plan 5:** stdlib types and methods, `import`, `rush test`, Linux and macOS runs.
- **Type consistency check:** `parse(Vec<Token>, &mut ExprId)` is used identically in Tasks 3, 4, 5, and 6. `TypeInfo.globals: HashMap<String, Global>` with `n_params` and `is_extern` is used in Tasks 4 and 6. `Type::uncurry_n` is used in Tasks 3 and 4. `ExprKind::Unit` is added in Task 3 and consumed in Tasks 4 and 5. Runtime symbol names in Task 5's header match the prelude and the cgen `rush_` prefix.
