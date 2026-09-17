use crate::ast::*;
use crate::diag::{Diagnostic, Span};
use crate::lexer::{Tok, Token};

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
                Tok::Str(s) if s == "C" => {
                    self.bump();
                }
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
            ("=", None),
            ("+=", Some(BinOp::Add)),
            ("-=", Some(BinOp::Sub)),
            ("*=", Some(BinOp::Mul)),
            ("/=", Some(BinOp::Div)),
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
            Tok::Int(v) => {
                self.bump();
                Ok(self.mk(ExprKind::Int(v), sp))
            }
            Tok::Float(v) => {
                self.bump();
                Ok(self.mk(ExprKind::Float(v), sp))
            }
            Tok::Str(s) => {
                self.bump();
                Ok(self.mk(ExprKind::Str(s), sp))
            }
            Tok::Kw("true") => {
                self.bump();
                Ok(self.mk(ExprKind::Bool(true), sp))
            }
            Tok::Kw("false") => {
                self.bump();
                Ok(self.mk(ExprKind::Bool(false), sp))
            }
            Tok::Ident(n) => {
                self.bump();
                Ok(self.mk(ExprKind::Var(n), sp))
            }
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
    fn unit_literal() {
        let p = parse_src("def main\n  ()\nend\n").unwrap();
        assert!(matches!(&only_def(&p).body.stmts[0], Stmt::Expr(Expr { kind: ExprKind::Unit, .. })));
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
