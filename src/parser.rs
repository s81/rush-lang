use crate::ast::*;
use crate::diag::{Diagnostic, Span};
use crate::lexer::{lex, RawPart, Tok, Token};

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
        Tok::Interp(_) => "interpolated string".to_string(),
        Tok::Ident(s) => format!("`{s}`"),
        Tok::Sym(s) => format!("`:{s}`"),
        Tok::Kw(k) => format!("`{k}`"),
        Tok::Op(o) => format!("`{o}`"),
        Tok::Newline => "end of line".to_string(),
        Tok::Eof => "end of file".to_string(),
    }
}

fn is_camel(s: &str) -> bool {
    s.chars().next().map_or(false, |c| c.is_ascii_uppercase())
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
    fn peek_at(&self, n: usize) -> &Tok {
        &self.toks[(self.pos + n).min(self.toks.len() - 1)].tok
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
    fn is_op_at(&self, n: usize, op: &str) -> bool {
        matches!(self.peek_at(n), Tok::Op(o) if *o == op)
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
    fn fresh_id(&mut self) -> u32 {
        let id = self.next_id;
        self.next_id += 1;
        id
    }
    fn mk(&mut self, kind: ExprKind, span: Span) -> Expr {
        let id = self.fresh_id();
        Expr { id, kind, span }
    }
    fn mk_pat(&mut self, kind: PatKind, span: Span) -> Pattern {
        let id = self.fresh_id();
        Pattern { id, kind, span }
    }

    // ----- items -----

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
        if self.is_kw("struct") {
            return Ok(Item::Struct(self.struct_def()?));
        }
        if self.is_kw("enum") {
            return Ok(Item::Enum(self.enum_def()?));
        }
        if self.is_kw("trait") {
            return Ok(Item::Trait(self.trait_def()?));
        }
        if self.is_kw("impl") {
            return Ok(Item::Impl(self.impl_def()?));
        }
        Err(self.err("`def`, `struct`, `enum`, `trait`, or `impl`"))
    }

    /// `[T, U: Show + Eq]` or nothing.
    fn generics(&mut self) -> Result<Generics, Diagnostic> {
        let mut params = Vec::new();
        if !self.eat_op("[") {
            return Ok(Generics { params });
        }
        loop {
            self.skip_newlines();
            let (name, span) = self.expect_ident()?;
            let mut bounds = Vec::new();
            if self.eat_op(":") {
                loop {
                    bounds.push(self.expect_ident()?.0);
                    if !self.eat_op("+") {
                        break;
                    }
                }
            }
            params.push(GenericParam { name, bounds, span });
            self.skip_newlines();
            if !self.eat_op(",") {
                break;
            }
        }
        self.expect_op("]")?;
        Ok(Generics { params })
    }

    fn def_header(&mut self) -> Result<Def, Diagnostic> {
        let start = self.expect_kw("def")?;
        let (name, _) = self.expect_ident()?;
        let generics = self.generics()?;
        let mut params = Vec::new();
        let mut self_param = None;
        if self.eat_op("(") {
            self.skip_newlines();
            // self, &self, &mut self
            if self.is_kw("self") {
                self.bump();
                self_param = Some(SelfKind::Value);
            } else if self.is_op("&") && matches!(self.peek_at(1), Tok::Kw("self")) {
                self.bump();
                self.bump();
                self_param = Some(SelfKind::Ref);
            } else if self.is_op("&") && matches!(self.peek_at(1), Tok::Kw("mut")) && matches!(self.peek_at(2), Tok::Kw("self")) {
                self.bump();
                self.bump();
                self.bump();
                self_param = Some(SelfKind::RefMut);
            }
            if self_param.is_some() {
                self.skip_newlines();
                if !self.eat_op(",") {
                    self.expect_op(")")?;
                    let ret = if self.eat_op("->") { Some(self.type_expr()?) } else { None };
                    return Ok(Def { name, generics, self_param, params, ret, body: Block { stmts: vec![], span: start }, span: start });
                }
                self.skip_newlines();
            }
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
        Ok(Def { name, generics, self_param, params, ret, body: Block { stmts: vec![], span: start }, span: start })
    }

    fn def(&mut self) -> Result<Def, Diagnostic> {
        let mut d = self.def_header()?;
        self.expect_newline()?;
        d.body = self.block_until(&["end"])?;
        let end = self.expect_kw("end")?;
        d.span = d.span.to(end);
        Ok(d)
    }

    fn struct_def(&mut self) -> Result<StructDef, Diagnostic> {
        let start = self.expect_kw("struct")?;
        let (name, _) = self.expect_ident()?;
        let generics = self.generics()?;
        self.expect_newline()?;
        let derives = self.derives()?;
        let mut fields = Vec::new();
        while !self.is_kw("end") {
            if self.at_eof() {
                return Err(self.err("`end`"));
            }
            fields.push(self.field_def()?);
            self.expect_newline()?;
        }
        let end = self.expect_kw("end")?;
        Ok(StructDef { name, generics, derives, fields, span: start.to(end) })
    }

    /// `derive A, B` as the first line of a struct or enum body.
    fn derives(&mut self) -> Result<Vec<String>, Diagnostic> {
        let mut out = Vec::new();
        if self.eat_kw("derive") {
            loop {
                out.push(self.expect_ident()?.0);
                if !self.eat_op(",") {
                    break;
                }
            }
            self.expect_newline()?;
        }
        Ok(out)
    }

    fn field_def(&mut self) -> Result<FieldDef, Diagnostic> {
        let (name, span) = self.expect_ident()?;
        self.expect_op(":")?;
        let ty = self.type_expr()?;
        Ok(FieldDef { name, ty, span })
    }

    fn enum_def(&mut self) -> Result<EnumDef, Diagnostic> {
        let start = self.expect_kw("enum")?;
        let (name, _) = self.expect_ident()?;
        let generics = self.generics()?;
        self.expect_newline()?;
        let derives = self.derives()?;
        let mut variants = Vec::new();
        while !self.is_kw("end") {
            if self.at_eof() {
                return Err(self.err("`end`"));
            }
            let (vname, vspan) = self.expect_ident()?;
            let fields = if self.eat_op("(") {
                let mut tys = Vec::new();
                self.skip_newlines();
                while !self.is_op(")") {
                    tys.push(self.type_expr()?);
                    self.skip_newlines();
                    if !self.eat_op(",") {
                        break;
                    }
                    self.skip_newlines();
                }
                self.expect_op(")")?;
                VariantFields::Tuple(tys)
            } else if self.eat_op("{") {
                let mut fs = Vec::new();
                self.skip_newlines();
                while !self.is_op("}") {
                    fs.push(self.field_def()?);
                    self.skip_newlines();
                    if !self.eat_op(",") {
                        break;
                    }
                    self.skip_newlines();
                }
                self.expect_op("}")?;
                VariantFields::Named(fs)
            } else {
                VariantFields::Unit
            };
            variants.push(VariantDef { name: vname, fields, span: vspan.to(self.prev_span()) });
            self.expect_newline()?;
        }
        let end = self.expect_kw("end")?;
        Ok(EnumDef { name, generics, derives, variants, span: start.to(end) })
    }

    fn trait_def(&mut self) -> Result<TraitDef, Diagnostic> {
        let start = self.expect_kw("trait")?;
        let (name, _) = self.expect_ident()?;
        let mut supertraits = Vec::new();
        if self.eat_op(":") {
            loop {
                supertraits.push(self.expect_ident()?.0);
                if !self.eat_op("+") {
                    break;
                }
            }
        }
        self.expect_newline()?;
        let mut methods = Vec::new();
        while !self.is_kw("end") {
            if self.at_eof() {
                return Err(self.err("`end`"));
            }
            let mut d = self.def_header()?;
            self.expect_newline()?;
            if !(self.is_kw("def") || self.is_kw("end")) {
                d.body = self.block_until(&["end"])?;
                let end = self.expect_kw("end")?;
                d.span = d.span.to(end);
                self.expect_newline()?;
            }
            methods.push(d);
        }
        let end = self.expect_kw("end")?;
        Ok(TraitDef { name, supertraits, methods, span: start.to(end) })
    }

    fn impl_def(&mut self) -> Result<ImplDef, Diagnostic> {
        let start = self.expect_kw("impl")?;
        let generics = self.generics()?;
        let first = self.type_expr()?;
        let (trait_name, self_ty) = if self.eat_kw("for") {
            let tn = match first {
                TypeExpr::Name(n, args, _) if args.is_empty() => n,
                other => return Err(Diagnostic::new(other.span(), "expected a trait name before `for`")),
            };
            (Some(tn), self.type_expr()?)
        } else {
            (None, first)
        };
        self.expect_newline()?;
        let mut methods = Vec::new();
        while !self.is_kw("end") {
            if self.at_eof() {
                return Err(self.err("`end`"));
            }
            methods.push(self.def()?);
            self.expect_newline()?;
        }
        let end = self.expect_kw("end")?;
        Ok(ImplDef { generics, trait_name, self_ty, methods, span: start.to(end) })
    }

    // ----- types -----

    fn type_expr(&mut self) -> Result<TypeExpr, Diagnostic> {
        let lhs = self.type_atom()?;
        if self.eat_op("->") {
            let rhs = self.type_expr()?;
            let span = lhs.span().to(rhs.span());
            return Ok(TypeExpr::Fn(Box::new(lhs), Box::new(rhs), span));
        }
        Ok(lhs)
    }

    fn type_atom(&mut self) -> Result<TypeExpr, Diagnostic> {
        let sp = self.span();
        if self.eat_op("&") {
            let mutable = self.eat_kw("mut");
            let inner = self.type_atom()?;
            let span = sp.to(inner.span());
            return Ok(TypeExpr::Ref(mutable, Box::new(inner), span));
        }
        if self.eat_op("(") {
            let mut tys = Vec::new();
            self.skip_newlines();
            while !self.is_op(")") {
                tys.push(self.type_expr()?);
                self.skip_newlines();
                if !self.eat_op(",") {
                    break;
                }
                self.skip_newlines();
            }
            let end = self.expect_op(")")?;
            if tys.len() == 1 {
                return Ok(tys.pop().unwrap());
            }
            return Ok(TypeExpr::Tuple(tys, sp.to(end)));
        }
        if self.is_kw("Self") {
            let s = self.bump().span;
            return Ok(TypeExpr::Name("Self".into(), vec![], s));
        }
        let (name, nsp) = self.expect_ident()?;
        let mut args = Vec::new();
        if self.eat_op("[") {
            loop {
                self.skip_newlines();
                args.push(self.type_expr()?);
                self.skip_newlines();
                if !self.eat_op(",") {
                    break;
                }
            }
            self.expect_op("]")?;
        }
        Ok(TypeExpr::Name(name, args, nsp.to(self.prev_span())))
    }

    // ----- statements -----

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
            let pat = if self.is_op("(") || matches!(self.peek(), Tok::Ident(n) if is_camel(n)) {
                self.pattern()?
            } else {
                let (name, sp) = self.expect_ident()?;
                self.mk_pat(PatKind::Bind(name), sp)
            };
            self.expect_op("=")?;
            let init = self.expr()?;
            let span = start.to(init.span);
            return Ok(Stmt::Let { pat, mutable, init, span });
        }
        Ok(Stmt::Expr(self.expr()?))
    }

    // ----- patterns -----

    fn pattern(&mut self) -> Result<Pattern, Diagnostic> {
        let first = self.at_pattern()?;
        if !self.is_op("|") {
            return Ok(first);
        }
        let mut alts = vec![first];
        while self.eat_op("|") {
            alts.push(self.at_pattern()?);
        }
        let span = alts[0].span.to(alts.last().unwrap().span);
        Ok(self.mk_pat(PatKind::Or(alts), span))
    }

    fn at_pattern(&mut self) -> Result<Pattern, Diagnostic> {
        if let Tok::Ident(n) = self.peek().clone() {
            if !is_camel(&n) && self.is_op_at(1, "@") {
                let sp = self.bump().span;
                self.bump();
                let inner = self.pat_atom()?;
                let span = sp.to(inner.span);
                return Ok(self.mk_pat(PatKind::At(n, Box::new(inner)), span));
            }
        }
        self.pat_atom()
    }

    fn pat_atom(&mut self) -> Result<Pattern, Diagnostic> {
        let sp = self.span();
        match self.peek().clone() {
            Tok::Int(v) => {
                self.bump();
                Ok(self.mk_pat(PatKind::Lit(Lit::Int(v)), sp))
            }
            Tok::Float(v) => {
                self.bump();
                Ok(self.mk_pat(PatKind::Lit(Lit::Float(v)), sp))
            }
            Tok::Str(s) => {
                self.bump();
                Ok(self.mk_pat(PatKind::Lit(Lit::Str(s)), sp))
            }
            Tok::Sym(s) => {
                self.bump();
                Ok(self.mk_pat(PatKind::Lit(Lit::Symbol(s)), sp))
            }
            Tok::Kw("true") => {
                self.bump();
                Ok(self.mk_pat(PatKind::Lit(Lit::Bool(true)), sp))
            }
            Tok::Kw("false") => {
                self.bump();
                Ok(self.mk_pat(PatKind::Lit(Lit::Bool(false)), sp))
            }
            Tok::Op("-") => {
                self.bump();
                match self.peek().clone() {
                    Tok::Int(v) => {
                        let end = self.bump().span;
                        Ok(self.mk_pat(PatKind::Lit(Lit::Int(-v)), sp.to(end)))
                    }
                    Tok::Float(v) => {
                        let end = self.bump().span;
                        Ok(self.mk_pat(PatKind::Lit(Lit::Float(-v)), sp.to(end)))
                    }
                    _ => Err(self.err("number after `-` in pattern")),
                }
            }
            Tok::Op("(") => {
                self.bump();
                if self.is_op(")") {
                    let end = self.bump().span;
                    return Ok(self.mk_pat(PatKind::Lit(Lit::Unit), sp.to(end)));
                }
                let mut pats = Vec::new();
                let mut trailing_comma = false;
                self.skip_newlines();
                while !self.is_op(")") {
                    pats.push(self.pattern()?);
                    self.skip_newlines();
                    trailing_comma = self.eat_op(",");
                    if !trailing_comma {
                        break;
                    }
                    self.skip_newlines();
                }
                let end = self.expect_op(")")?;
                if pats.len() == 1 && !trailing_comma {
                    return Ok(pats.pop().unwrap());
                }
                Ok(self.mk_pat(PatKind::Tuple(pats), sp.to(end)))
            }
            Tok::Ident(n) if n == "_" => {
                self.bump();
                Ok(self.mk_pat(PatKind::Wild, sp))
            }
            Tok::Ident(n) if !is_camel(&n) => {
                self.bump();
                Ok(self.mk_pat(PatKind::Bind(n), sp))
            }
            Tok::Ident(n) => {
                self.bump();
                if self.eat_op("(") {
                    let mut fields = Vec::new();
                    self.skip_newlines();
                    while !self.is_op(")") {
                        fields.push(self.pattern()?);
                        self.skip_newlines();
                        if !self.eat_op(",") {
                            break;
                        }
                        self.skip_newlines();
                    }
                    let end = self.expect_op(")")?;
                    return Ok(self.mk_pat(PatKind::Variant { name: n, fields }, sp.to(end)));
                }
                if self.eat_op("{") {
                    let mut fields = Vec::new();
                    self.skip_newlines();
                    while !self.is_op("}") {
                        let (fname, fsp) = self.expect_ident()?;
                        let pat = if self.eat_op(":") {
                            self.pattern()?
                        } else {
                            self.mk_pat(PatKind::Bind(fname.clone()), fsp)
                        };
                        fields.push((fname, pat));
                        self.skip_newlines();
                        if !self.eat_op(",") {
                            break;
                        }
                        self.skip_newlines();
                    }
                    let end = self.expect_op("}")?;
                    return Ok(self.mk_pat(PatKind::Struct { name: n, fields }, sp.to(end)));
                }
                Ok(self.mk_pat(PatKind::Variant { name: n, fields: vec![] }, sp))
            }
            _ => Err(self.err("pattern")),
        }
    }

    // ----- expressions -----

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
        let lhs = self.range()?;
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

    /// `a..b` and `a...b` bind more loosely than every binary operator and do not chain.
    fn range(&mut self) -> Result<Expr, Diagnostic> {
        let lhs = self.binary(0)?;
        let exclusive = match self.peek() {
            Tok::Op("..") => false,
            Tok::Op("...") => true,
            _ => return Ok(lhs),
        };
        self.bump();
        let rhs = self.binary(0)?;
        let span = lhs.span.to(rhs.span);
        Ok(self.mk(ExprKind::Range(Box::new(lhs), Box::new(rhs), exclusive), span))
    }

    /// Fresh copy of an assignment target, for desugaring `x += e` and `p.x += e`.
    fn reid(&mut self, e: &Expr) -> Result<Expr, Diagnostic> {
        match &e.kind {
            ExprKind::Var(n) => Ok(self.mk(ExprKind::Var(n.clone()), e.span)),
            ExprKind::Dot { recv, name, args: None } => {
                let r = self.reid(recv)?;
                Ok(self.mk(ExprKind::Dot { recv: Box::new(r), name: name.clone(), args: None }, e.span))
            }
            ExprKind::TupleIndex(recv, i) => {
                let r = self.reid(recv)?;
                Ok(self.mk(ExprKind::TupleIndex(Box::new(r), *i), e.span))
            }
            _ => Err(Diagnostic::new(e.span, "compound assignment target must be a variable or field")),
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
        if self.is_op("&") {
            let sp = self.bump().span;
            let mutable = self.eat_kw("mut");
            let e = self.unary()?;
            let span = sp.to(e.span);
            return Ok(self.mk(ExprKind::Ref(mutable, Box::new(e)), span));
        }
        if self.is_op("*") {
            let sp = self.bump().span;
            let e = self.unary()?;
            let span = sp.to(e.span);
            return Ok(self.mk(ExprKind::Deref(Box::new(e)), span));
        }
        self.postfix()
    }

    fn call_args(&mut self) -> Result<(Vec<Expr>, Span), Diagnostic> {
        self.expect_op("(")?;
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
        Ok((args, end))
    }

    fn postfix(&mut self) -> Result<Expr, Diagnostic> {
        let mut e = self.primary()?;
        loop {
            if self.is_op("(") {
                let (args, end) = self.call_args()?;
                let span = e.span.to(end);
                e = self.mk(ExprKind::Call(Box::new(e), args), span);
            } else if self.is_op(".") {
                self.bump();
                match self.peek().clone() {
                    Tok::Int(i) => {
                        let end = self.bump().span;
                        let span = e.span.to(end);
                        e = self.mk(ExprKind::TupleIndex(Box::new(e), i as usize), span);
                    }
                    Tok::Ident(name) => {
                        let end = self.bump().span;
                        let (args, end) = if self.is_op("(") {
                            let (a, end) = self.call_args()?;
                            (Some(a), end)
                        } else {
                            (None, end)
                        };
                        let span = e.span.to(end);
                        e = self.mk(ExprKind::Dot { recv: Box::new(e), name, args }, span);
                    }
                    _ => return Err(self.err("field or method name after `.`")),
                }
            } else {
                break;
            }
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
            Tok::Sym(s) => {
                self.bump();
                Ok(self.mk(ExprKind::Symbol(s), sp))
            }
            Tok::Interp(parts) => {
                self.bump();
                let mut out = Vec::new();
                for part in parts {
                    match part {
                        RawPart::Lit(s) => out.push(InterpPart::Lit(s)),
                        RawPart::Code(code, offset) => out.push(InterpPart::Expr(self.sub_expr(&code, offset)?)),
                    }
                }
                Ok(self.mk(ExprKind::Interp(out), sp))
            }
            Tok::Kw("true") => {
                self.bump();
                Ok(self.mk(ExprKind::Bool(true), sp))
            }
            Tok::Kw("false") => {
                self.bump();
                Ok(self.mk(ExprKind::Bool(false), sp))
            }
            Tok::Kw("self") => {
                self.bump();
                Ok(self.mk(ExprKind::Var("self".into()), sp))
            }
            Tok::Op("@") => {
                self.bump();
                let (name, end) = self.expect_ident()?;
                let recv = self.mk(ExprKind::Var("self".into()), sp);
                Ok(self.mk(ExprKind::Dot { recv: Box::new(recv), name, args: None }, sp.to(end)))
            }
            Tok::Ident(n) if is_camel(&n) && self.is_op_at(1, "{") => {
                self.bump();
                self.bump();
                let mut fields = Vec::new();
                self.skip_newlines();
                while !self.is_op("}") {
                    let (fname, _) = self.expect_ident()?;
                    self.expect_op(":")?;
                    let value = self.expr()?;
                    fields.push((fname, value));
                    self.skip_newlines();
                    if !self.eat_op(",") {
                        break;
                    }
                    self.skip_newlines();
                }
                let end = self.expect_op("}")?;
                Ok(self.mk(ExprKind::StructLit { name: n, fields }, sp.to(end)))
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
                let first = self.expr()?;
                self.skip_newlines();
                if self.eat_op(",") {
                    let mut items = vec![first];
                    self.skip_newlines();
                    while !self.is_op(")") {
                        items.push(self.expr()?);
                        self.skip_newlines();
                        if !self.eat_op(",") {
                            break;
                        }
                        self.skip_newlines();
                    }
                    let end = self.expect_op(")")?;
                    return Ok(self.mk(ExprKind::Tuple(items), sp.to(end)));
                }
                self.expect_op(")")?;
                Ok(first)
            }
            Tok::Kw("if") => self.if_expr(),
            Tok::Kw("case") => self.case_expr(),
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

    /// Parses interpolated code with spans shifted to the enclosing source.
    fn sub_expr(&mut self, code: &str, offset: u32) -> Result<Expr, Diagnostic> {
        let shift = |d: Diagnostic| Diagnostic::new(Span { start: d.span.start + offset, end: d.span.end + offset }, d.msg);
        let mut toks = lex(code).map_err(shift)?;
        for t in &mut toks {
            t.span = Span { start: t.span.start + offset, end: t.span.end + offset };
            if matches!(t.tok, Tok::Newline | Tok::Eof) && t.span.start == t.span.end {
                // Point at the closing `}` so errors at the end of the code underline something.
                t.span.end += 1;
            }
        }
        let mut sub = Parser { toks, pos: 0, next_id: self.next_id };
        let e = sub.expr()?;
        sub.skip_newlines();
        if !sub.at_eof() {
            return Err(sub.err("end of interpolation"));
        }
        self.next_id = sub.next_id;
        Ok(e)
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

    fn case_expr(&mut self) -> Result<Expr, Diagnostic> {
        let sp = self.expect_kw("case")?;
        let scrutinee = self.expr()?;
        self.expect_newline()?;
        let mut arms = Vec::new();
        loop {
            self.skip_newlines();
            if self.is_kw("in") {
                let arm_start = self.bump().span;
                let pat = self.pattern()?;
                let guard = if self.eat_kw("if") { Some(self.expr()?) } else { None };
                let body = if self.eat_kw("then") {
                    let e = self.expr()?;
                    let span = e.span;
                    self.expect_newline()?;
                    Block { stmts: vec![Stmt::Expr(e)], span }
                } else {
                    self.expect_newline()?;
                    self.block_until(&["in", "else", "end"])?
                };
                arms.push(Arm { pat, guard, body, span: arm_start.to(self.prev_span()) });
            } else if self.is_kw("else") {
                let arm_start = self.bump().span;
                self.expect_newline()?;
                let body = self.block_until(&["end"])?;
                let pat = self.mk_pat(PatKind::Wild, arm_start);
                arms.push(Arm { pat, guard: None, body, span: arm_start.to(self.prev_span()) });
            } else if self.is_kw("end") {
                break;
            } else {
                return Err(self.err("`in`, `else`, or `end`"));
            }
        }
        let end = self.expect_kw("end")?;
        if arms.is_empty() {
            return Err(Diagnostic::new(sp.to(end), "`case` needs at least one `in` arm"));
        }
        Ok(self.mk(ExprKind::Case { scrutinee: Box::new(scrutinee), arms }, sp.to(end)))
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

    fn first_expr(p: &Program) -> &Expr {
        match &only_def(p).body.stmts[0] {
            Stmt::Expr(e) => e,
            other => panic!("expected expr stmt, got {other:?}"),
        }
    }

    fn main_expr(src: &str) -> Expr {
        let p = parse_src(&format!("def main\n  {src}\nend\n")).unwrap();
        first_expr(&p).clone()
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
        assert!(matches!(main_expr("()").kind, ExprKind::Unit));
    }

    #[test]
    fn precedence_and_associativity() {
        let e = main_expr("1 + 2 * 3 - 4");
        let ExprKind::Binary(BinOp::Sub, l, r) = &e.kind else { panic!("{:?}", e.kind) };
        assert!(matches!(r.kind, ExprKind::Int(4)));
        let ExprKind::Binary(BinOp::Add, _, m) = &l.kind else { panic!() };
        assert!(matches!(m.kind, ExprKind::Binary(BinOp::Mul, _, _)));
    }

    #[test]
    fn comparison_binds_looser_than_arithmetic_and_tighter_than_and() {
        let e = main_expr("a + 1 < b and c");
        let ExprKind::Binary(BinOp::And, l, _) = &e.kind else { panic!() };
        assert!(matches!(l.kind, ExprKind::Binary(BinOp::Lt, _, _)));
    }

    #[test]
    fn ranges_bind_looser_than_arithmetic() {
        let e = main_expr("1..n - 1");
        let ExprKind::Range(l, r, false) = &e.kind else { panic!("{:?}", e.kind) };
        assert!(matches!(l.kind, ExprKind::Int(1)));
        assert!(matches!(r.kind, ExprKind::Binary(BinOp::Sub, _, _)));
        assert!(matches!(main_expr("a...b").kind, ExprKind::Range(_, _, true)));
    }

    #[test]
    fn symbol_literals_and_patterns() {
        assert!(matches!(&main_expr(":ok").kind, ExprKind::Symbol(s) if s == "ok"));
        let e = main_expr("case x
  in :a then 1
  in _ then 2
  end");
        let ExprKind::Case { arms, .. } = &e.kind else { panic!() };
        assert!(matches!(&arms[0].pat.kind, PatKind::Lit(Lit::Symbol(s)) if s == "a"));
    }

    #[test]
    fn let_mut_and_compound_assign() {
        let p = parse_src("def main\n  let mut x = 1\n  x += 2\nend\n").unwrap();
        let d = only_def(&p);
        assert!(matches!(&d.body.stmts[0], Stmt::Let { pat: Pattern { kind: PatKind::Bind(name), .. }, mutable: true, .. } if name == "x"));
        let Stmt::Expr(e) = &d.body.stmts[1] else { panic!() };
        let ExprKind::Assign(lhs, rhs) = &e.kind else { panic!() };
        assert!(matches!(&lhs.kind, ExprKind::Var(n) if n == "x"));
        assert!(matches!(rhs.kind, ExprKind::Binary(BinOp::Add, _, _)));
    }

    #[test]
    fn if_elsif_else_desugars() {
        let e = main_expr("if a\n    1\n  elsif b\n    2\n  else\n    3\n  end");
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
        let ExprKind::Binary(_, l, r) = &first_expr(&p).kind else { panic!() };
        assert_eq!((l.id, r.id, first_expr(&p).id), (10, 11, 12));
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

    // ----- Plan 2 -----

    #[test]
    fn struct_and_generic_struct() {
        let p = parse_src("struct Point\n  x: Float\n  y: Float\nend\nstruct Pair[A, B: Show + Eq]\n  first: A\n  second: B\nend\n").unwrap();
        let Item::Struct(s) = &p.items[0] else { panic!() };
        assert_eq!(s.name, "Point");
        assert_eq!(s.fields.iter().map(|f| f.name.as_str()).collect::<Vec<_>>(), ["x", "y"]);
        let Item::Struct(s) = &p.items[1] else { panic!() };
        assert_eq!(s.generics.params[0].name, "A");
        assert_eq!(s.generics.params[1].bounds, vec!["Show", "Eq"]);
    }

    #[test]
    fn enum_with_three_variant_shapes() {
        let p = parse_src("enum Shape\n  Circle(Float)\n  Rect { w: Float, h: Float }\n  Empty\nend\n").unwrap();
        let Item::Enum(e) = &p.items[0] else { panic!() };
        assert!(matches!(&e.variants[0].fields, VariantFields::Tuple(t) if t.len() == 1));
        assert!(matches!(&e.variants[1].fields, VariantFields::Named(f) if f.len() == 2 && f[1].name == "h"));
        assert!(matches!(&e.variants[2].fields, VariantFields::Unit));
    }

    #[test]
    fn trait_with_required_and_default_method_and_supertrait() {
        let p = parse_src("trait Area: Show\n  def area(&self) -> Float\n  def describe(&self) -> String\n    \"x\"\n  end\nend\n").unwrap();
        let Item::Trait(t) = &p.items[0] else { panic!() };
        assert_eq!(t.supertraits, vec!["Show"]);
        assert_eq!(t.methods.len(), 2);
        assert!(t.methods[0].body.stmts.is_empty());
        assert_eq!(t.methods[0].self_param, Some(SelfKind::Ref));
        assert_eq!(t.methods[1].body.stmts.len(), 1);
    }

    #[test]
    fn impl_inherent_and_generic_trait_impl() {
        let p = parse_src("impl Point\n  def swap(self) -> Point\n    self\n  end\nend\nimpl[T: Show] Show for Option[T]\n  def to_s(&mut self)\n    \"\"\n  end\nend\n").unwrap();
        let Item::Impl(i) = &p.items[0] else { panic!() };
        assert_eq!(i.trait_name, None);
        assert!(matches!(&i.self_ty, TypeExpr::Name(n, _, _) if n == "Point"));
        assert_eq!(i.methods[0].self_param, Some(SelfKind::Value));
        let Item::Impl(i) = &p.items[1] else { panic!() };
        assert_eq!(i.trait_name.as_deref(), Some("Show"));
        assert_eq!(i.generics.params[0].bounds, vec!["Show"]);
        assert!(matches!(&i.self_ty, TypeExpr::Name(n, a, _) if n == "Option" && a.len() == 1));
        assert_eq!(i.methods[0].self_param, Some(SelfKind::RefMut));
    }

    #[test]
    fn method_with_self_and_params() {
        let p = parse_src("def dist(&self, other: Point, k) -> Float\n  1.0\nend\n").unwrap();
        let d = only_def(&p);
        assert_eq!(d.self_param, Some(SelfKind::Ref));
        assert_eq!(d.params.len(), 2);
    }

    #[test]
    fn type_exprs() {
        let p = parse_src("def f(a: Pair[Int, String], b: (Int, Bool), c: Int -> Int -> Bool, d: &mut T, e: Self) -> ()\n  ()\nend\n").unwrap();
        let d = only_def(&p);
        assert!(matches!(&d.params[0].ty, Some(TypeExpr::Name(n, a, _)) if n == "Pair" && a.len() == 2));
        assert!(matches!(&d.params[1].ty, Some(TypeExpr::Tuple(t, _)) if t.len() == 2));
        let Some(TypeExpr::Fn(a, b, _)) = &d.params[2].ty else { panic!() };
        assert!(matches!(**a, TypeExpr::Name(ref n, _, _) if n == "Int"));
        assert!(matches!(**b, TypeExpr::Fn(..)));
        assert!(matches!(&d.params[3].ty, Some(TypeExpr::Ref(true, _, _))));
        assert!(matches!(&d.params[4].ty, Some(TypeExpr::Name(n, _, _)) if n == "Self"));
        assert!(matches!(&d.ret, Some(TypeExpr::Tuple(t, _)) if t.is_empty()));
    }

    #[test]
    fn dot_field_method_and_tuple_index() {
        let e = main_expr("p.x");
        assert!(matches!(&e.kind, ExprKind::Dot { name, args: None, .. } if name == "x"));
        let e = main_expr("p.m(1, 2)");
        assert!(matches!(&e.kind, ExprKind::Dot { name, args: Some(a), .. } if name == "m" && a.len() == 2));
        let e = main_expr("t.0");
        assert!(matches!(&e.kind, ExprKind::TupleIndex(_, 0)));
        let e = main_expr("a.b.c(1).d");
        let ExprKind::Dot { recv, name, args: None } = &e.kind else { panic!() };
        assert_eq!(name, "d");
        assert!(matches!(&recv.kind, ExprKind::Dot { name, args: Some(_), .. } if name == "c"));
    }

    #[test]
    fn struct_literal() {
        let e = main_expr("Point { x: 1.0, y: 2.0 }");
        let ExprKind::StructLit { name, fields } = &e.kind else { panic!("{:?}", e.kind) };
        assert_eq!(name, "Point");
        assert_eq!(fields.len(), 2);
        assert_eq!(fields[1].0, "y");
    }

    #[test]
    fn tuple_literal_and_let_pattern() {
        let e = main_expr("(1, \"a\")");
        assert!(matches!(&e.kind, ExprKind::Tuple(items) if items.len() == 2));
        let p = parse_src("def main\n  let (a, (b, _)) = t\nend\n").unwrap();
        let Stmt::Let { pat, .. } = &only_def(&p).body.stmts[0] else { panic!() };
        let PatKind::Tuple(items) = &pat.kind else { panic!() };
        assert!(matches!(&items[0].kind, PatKind::Bind(n) if n == "a"));
        let PatKind::Tuple(inner) = &items[1].kind else { panic!() };
        assert!(matches!(inner[1].kind, PatKind::Wild));
    }

    #[test]
    fn case_arms_single_and_multi_line_with_guard_and_else() {
        let e = main_expr("case s\n  in Circle(r) if r > 1.0 then r\n  in Rect { w, h: hh }\n    w\n    hh\n  in None then 0.0\n  else\n    1.0\n  end");
        let ExprKind::Case { arms, .. } = &e.kind else { panic!("{:?}", e.kind) };
        assert_eq!(arms.len(), 4);
        assert!(arms[0].guard.is_some());
        assert!(matches!(&arms[0].pat.kind, PatKind::Variant { name, fields } if name == "Circle" && fields.len() == 1));
        let PatKind::Struct { name, fields } = &arms[1].pat.kind else { panic!() };
        assert_eq!(name, "Rect");
        assert!(matches!(&fields[0].1.kind, PatKind::Bind(n) if n == "w"));
        assert!(matches!(&fields[1].1.kind, PatKind::Bind(n) if n == "hh"));
        assert_eq!(arms[1].body.stmts.len(), 2);
        assert!(matches!(&arms[2].pat.kind, PatKind::Variant { name, fields } if name == "None" && fields.is_empty()));
        assert!(matches!(arms[3].pat.kind, PatKind::Wild));
    }

    #[test]
    fn patterns_or_at_and_negative_literal() {
        let e = main_expr("case n\n  in x @ (1 | -2) then x\n  in _ then 0\n  end");
        let ExprKind::Case { arms, .. } = &e.kind else { panic!() };
        let PatKind::At(name, inner) = &arms[0].pat.kind else { panic!("{:?}", arms[0].pat.kind) };
        assert_eq!(name, "x");
        let PatKind::Or(alts) = &inner.kind else { panic!() };
        assert!(matches!(alts[1].kind, PatKind::Lit(Lit::Int(-2))));
    }

    #[test]
    fn interpolation_parses_code_with_correct_spans() {
        let src = "def main\n  \"a #{1 + x} b\"\nend\n";
        let p = parse_src(src).unwrap();
        let ExprKind::Interp(parts) = &first_expr(&p).kind else { panic!() };
        assert!(matches!(&parts[0], InterpPart::Lit(s) if s == "a "));
        let InterpPart::Expr(e) = &parts[1] else { panic!() };
        assert!(matches!(e.kind, ExprKind::Binary(BinOp::Add, _, _)));
        assert_eq!(&src[e.span.start as usize..e.span.end as usize], "1 + x");
        assert!(matches!(&parts[2], InterpPart::Lit(s) if s == " b"));
    }

    #[test]
    fn interpolation_error_reports_outer_offset() {
        let src = "def main\n  \"a #{1 +} b\"\nend\n";
        let err = parse_src(src).unwrap_err();
        assert_eq!(&src[err.span.start as usize..err.span.end as usize], "}");
    }

    #[test]
    fn at_field_is_self_dot() {
        let e = main_expr("@x + 1");
        let ExprKind::Binary(_, l, _) = &e.kind else { panic!() };
        let ExprKind::Dot { recv, name, args: None } = &l.kind else { panic!() };
        assert_eq!(name, "x");
        assert!(matches!(&recv.kind, ExprKind::Var(n) if n == "self"));
    }

    #[test]
    fn refs_parse() {
        assert!(matches!(main_expr("&x").kind, ExprKind::Ref(false, _)));
        assert!(matches!(main_expr("&mut x").kind, ExprKind::Ref(true, _)));
        assert!(matches!(main_expr("*x").kind, ExprKind::Deref(_)));
        let e = main_expr("&p.x");
        let ExprKind::Ref(false, inner) = &e.kind else { panic!() };
        assert!(matches!(inner.kind, ExprKind::Dot { .. }));
    }

    #[test]
    fn derive_lines_and_paths() {
        let p = parse_src("struct P
  derive Show, Eq
  x: Int
end
enum E
  derive Copy
  A
end
").unwrap();
        let Item::Struct(s) = &p.items[0] else { panic!() };
        assert_eq!(s.derives, vec!["Show", "Eq"]);
        assert_eq!(s.fields.len(), 1);
        let Item::Enum(e) = &p.items[1] else { panic!() };
        assert_eq!(e.derives, vec!["Copy"]);
        // `Type.name(args)` is an ordinary Dot; the checker resolves associated functions.
        let e = main_expr("Gc.new(1)");
        let ExprKind::Dot { recv, name, args: Some(args) } = &e.kind else { panic!("{:?}", e.kind) };
        assert!(matches!(&recv.kind, ExprKind::Var(t) if t == "Gc"));
        assert_eq!(name, "new");
        assert_eq!(args.len(), 1);
        assert!(matches!(main_expr("Point { x: 1.0 }").kind, ExprKind::StructLit { .. }));
    }

    #[test]
    fn field_compound_assign() {
        let e = main_expr("p.x += 1");
        let ExprKind::Assign(lhs, rhs) = &e.kind else { panic!() };
        assert!(matches!(&lhs.kind, ExprKind::Dot { .. }));
        let ExprKind::Binary(BinOp::Add, l, _) = &rhs.kind else { panic!() };
        assert!(matches!(&l.kind, ExprKind::Dot { .. }));
        assert_ne!(l.id, lhs.id);
    }

    #[test]
    fn empty_case_is_error() {
        let err = parse_src("def main\n  case x\n  end\nend\n").unwrap_err();
        assert_eq!(err.msg, "`case` needs at least one `in` arm");
    }
}
