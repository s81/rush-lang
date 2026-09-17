//! Expression, pattern, and method inference; generalization; constraint solving.

use std::collections::{HashMap, HashSet};

use super::*;
use crate::ast::*;

pub(super) struct Infer {
    pub subst: Vec<Option<Type>>,
}

fn occurs(v: u32, t: &Type) -> bool {
    match t {
        Type::Var(x) => *x == v,
        Type::Param(_) => false,
        Type::Con(_, args) => args.iter().any(|a| occurs(v, a)),
        Type::Fn(a, b) => occurs(v, a) || occurs(v, b),
    }
}

impl Infer {
    pub fn fresh(&mut self) -> Type {
        self.subst.push(None);
        Type::Var(self.subst.len() as u32 - 1)
    }
    pub fn resolve(&self, t: &Type) -> Type {
        match t {
            Type::Var(v) => match &self.subst[*v as usize] {
                Some(t2) => self.resolve(t2),
                None => t.clone(),
            },
            Type::Param(_) => t.clone(),
            Type::Con(n, args) => Type::Con(n.clone(), args.iter().map(|a| self.resolve(a)).collect()),
            Type::Fn(a, b) => Type::Fn(Box::new(self.resolve(a)), Box::new(self.resolve(b))),
        }
    }
    pub fn unify(&mut self, expected: &Type, found: &Type, span: Span) -> Result<(), Diagnostic> {
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
            (Type::Param(p), Type::Param(q)) if p == q => Ok(()),
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

/// A function body waiting to be checked.
pub(super) struct BodyJob<'a> {
    pub global: String,
    pub def: &'a Def,
    pub generics: Vec<String>,
    pub bounds: Vec<(String, String)>,
    pub self_ty: Option<Type>,
    /// True when the scheme is a placeholder to be generalized after checking.
    pub generalize: bool,
}

pub(super) enum Match {
    Yes(HashMap<String, Type>),
    No,
    Undecided,
}

pub(super) struct Checker<'a> {
    pub prog: &'a Program,
    pub inf: Infer,
    pub info: TypeInfo,
    pub adts: HashMap<String, usize>,
    pub jobs: Vec<BodyJob<'a>>,
    // Per-body context.
    pub scopes: Vec<HashMap<String, (Type, bool)>>,
    pub generics: Vec<String>,
    pub param_bounds: HashMap<String, Vec<String>>,
    pub self_ty: Option<Type>,
    pub ret_ty: Type,
    pub pending: Vec<(Type, String, Span)>,
    // Generalization bookkeeping.
    pub gen_map: HashMap<u32, String>,
    pub next_param: u32,
    pub inst_spans: HashMap<ExprId, Span>,
    /// Calls to not-yet-generalized defs; filled with insts after generalization.
    pub late_insts: Vec<(ExprId, String)>,
}

pub(super) fn check_program(prog: &Program) -> Result<TypeInfo, Diagnostic> {
    let mut cx = Checker {
        prog,
        inf: Infer { subst: vec![] },
        info: TypeInfo::default(),
        adts: HashMap::new(),
        jobs: vec![],
        scopes: vec![],
        generics: vec![],
        param_bounds: HashMap::new(),
        self_ty: None,
        ret_ty: Type::unit(),
        pending: vec![],
        gen_map: HashMap::new(),
        next_param: 0,
        inst_spans: HashMap::new(),
        late_insts: vec![],
    };
    cx.collect_types()?;
    cx.collect_traits()?;
    cx.collect_impls()?;
    cx.collect_defs()?;
    cx.check_all_bodies()?;
    cx.finish()
}

fn last_span(b: &Block, fallback: Span) -> Span {
    b.stmts
        .last()
        .map(|s| match s {
            Stmt::Expr(e) => e.span,
            Stmt::Let { span, .. } => *span,
        })
        .unwrap_or(fallback)
}

fn lit_type(l: &Lit) -> Type {
    match l {
        Lit::Int(_) => Type::con("Int"),
        Lit::Float(_) => Type::con("Float"),
        Lit::Str(_) => Type::con("String"),
        Lit::Bool(_) => Type::con("Bool"),
        Lit::Unit => Type::unit(),
    }
}

impl<'a> Checker<'a> {
    // ----- helpers -----

    pub fn env(&self) -> TypeEnv<'_> {
        TypeEnv { adts: &self.adts, generics: &self.generics, self_ty: self.self_ty.as_ref() }
    }

    pub fn lookup(&self, name: &str) -> Option<(Type, bool)> {
        for s in self.scopes.iter().rev() {
            if let Some(v) = s.get(name) {
                return Some(v.clone());
            }
        }
        None
    }

    fn record(&mut self, e: &Expr, t: Type) -> Type {
        self.info.expr_types.insert(e.id, t.clone());
        t
    }

    /// Instantiates a scheme with fresh variables, pushing its bounds as pending constraints.
    /// `fixed` pre-binds some vars (used for `Self`).
    pub fn instantiate(&mut self, s: &Scheme, fixed: HashMap<String, Type>, span: Span) -> (Type, Vec<Type>) {
        let mut map = fixed;
        let mut fresh = Vec::new();
        for v in &s.vars {
            let t = map.entry(v.clone()).or_insert_with(|| self.inf.fresh()).clone();
            fresh.push(t);
        }
        for (p, tr) in &s.bounds {
            self.pending.push((map[p].clone(), tr.clone(), span));
        }
        (subst(&s.ty, &map), fresh)
    }

    fn bounds_of(&self, param: &str) -> Vec<String> {
        let mut out = Vec::new();
        for b in self.param_bounds.get(param).into_iter().flatten() {
            for t in self.info.trait_closure(b) {
                if !out.contains(&t) {
                    out.push(t);
                }
            }
        }
        out
    }

    /// One-way match of an impl pattern (with impl generics as `Param`s) against a resolved type.
    pub fn match_type(&self, pat: &Type, ty: &Type, map: &mut HashMap<String, Type>) -> Match {
        match (pat, ty) {
            (Type::Param(p), _) => {
                if let Some(bound) = map.get(p) {
                    if self.inf.resolve(bound) != self.inf.resolve(ty) {
                        return Match::No;
                    }
                } else {
                    map.insert(p.clone(), ty.clone());
                }
                Match::Yes(HashMap::new())
            }
            (_, Type::Var(_)) => Match::Undecided,
            (Type::Con(n, a), Type::Con(m, b)) if n == m && a.len() == b.len() => {
                let mut undecided = false;
                for (x, y) in a.iter().zip(b) {
                    match self.match_type(x, y, map) {
                        Match::No => return Match::No,
                        Match::Undecided => undecided = true,
                        Match::Yes(_) => {}
                    }
                }
                if undecided { Match::Undecided } else { Match::Yes(HashMap::new()) }
            }
            (Type::Fn(a1, r1), Type::Fn(a2, r2)) => {
                let mut undecided = false;
                for (x, y) in [(a1, a2), (r1, r2)] {
                    match self.match_type(x, y, map) {
                        Match::No => return Match::No,
                        Match::Undecided => undecided = true,
                        Match::Yes(_) => {}
                    }
                }
                if undecided { Match::Undecided } else { Match::Yes(HashMap::new()) }
            }
            _ => Match::No,
        }
    }

    /// Finds the impl of `trait_name` for `ty`. Returns the impl id and the binding of its generics.
    pub fn find_impl(&self, trait_name: &str, ty: &Type) -> Match {
        let mut undecided = false;
        for imp in &self.info.impls {
            if imp.trait_name.as_deref() != Some(trait_name) {
                continue;
            }
            let mut map = HashMap::new();
            match self.match_type(&imp.self_ty, ty, &mut map) {
                Match::Yes(_) => {
                    map.insert("#impl".into(), Type::Con(imp.id.to_string(), vec![]));
                    return Match::Yes(map);
                }
                Match::Undecided => undecided = true,
                Match::No => {}
            }
        }
        if undecided { Match::Undecided } else { Match::No }
    }

    /// Discharges pending constraints that can be decided now; keeps the rest.
    fn solve_pending(&mut self) -> Result<(), Diagnostic> {
        let mut work = std::mem::take(&mut self.pending);
        let mut remaining = Vec::new();
        while let Some((ty, tr, span)) = work.pop() {
            let ty = self.inf.resolve(&ty);
            match &ty {
                Type::Var(_) => remaining.push((ty, tr, span)),
                Type::Param(p) => {
                    if !self.bounds_of(p).contains(&tr) {
                        return Err(Diagnostic::new(span, format!("`{p}` is not bounded by `{tr}`; add `{p}: {tr}`")));
                    }
                }
                _ => match self.find_impl(&tr, &ty) {
                    Match::Yes(map) => {
                        let id: usize = map["#impl"].head().unwrap().parse().unwrap();
                        let imp = &self.info.impls[id];
                        for (gp, btr) in &imp.bounds {
                            work.push((map[gp].clone(), btr.clone(), span));
                        }
                    }
                    Match::Undecided => remaining.push((ty, tr, span)),
                    Match::No => return Err(Diagnostic::new(span, format!("no instance of `{tr}` for `{ty}`"))),
                },
            }
        }
        self.pending = remaining;
        Ok(())
    }

    // ----- bodies -----

    fn check_all_bodies(&mut self) -> Result<(), Diagnostic> {
        let jobs = std::mem::take(&mut self.jobs);
        // Order user defs by call-graph SCCs so callees are generalized before callers.
        let user: Vec<usize> = jobs.iter().enumerate().filter(|(_, j)| matches!(self.info.globals[&j.global].kind, GlobalKind::Def)).map(|(i, _)| i).collect();
        let by_name: HashMap<&str, usize> = user.iter().map(|&i| (jobs[i].global.as_str(), i)).collect();
        let mut edges: HashMap<usize, Vec<usize>> = HashMap::new();
        for &i in &user {
            let mut refs = Vec::new();
            collect_refs_block(&jobs[i].def.body, &mut refs);
            let targets: Vec<usize> = refs.iter().filter_map(|n| by_name.get(n.as_str()).copied()).collect();
            edges.insert(i, targets);
        }
        let order = scc_order(&user, &edges);
        for group in order {
            for &i in &group {
                self.check_body(&jobs[i])?;
            }
            for &i in &group {
                if jobs[i].generalize {
                    self.generalize(&jobs[i].global)?;
                }
            }
            // Calls inside the group to members that had placeholder schemes get their insts now.
            let late = std::mem::take(&mut self.late_insts);
            for (id, g) in late {
                let vars: Vec<Type> = self.info.globals[&g].scheme.vars.iter().map(|v| Type::Param(v.clone())).collect();
                if !vars.is_empty() {
                    self.info.insts.insert(id, vars);
                }
            }
        }
        for (i, job) in jobs.iter().enumerate() {
            if !user.contains(&i) {
                self.check_body(job)?;
                self.reject_unresolved_pending()?;
            }
        }
        Ok(())
    }

    fn reject_unresolved_pending(&mut self) -> Result<(), Diagnostic> {
        if let Some((_, _, span)) = self.pending.first() {
            return Err(Diagnostic::new(*span, "type annotations needed"));
        }
        Ok(())
    }

    fn check_body(&mut self, job: &BodyJob<'a>) -> Result<(), Diagnostic> {
        self.generics = job.generics.clone();
        self.param_bounds.clear();
        for (p, t) in &job.bounds {
            self.param_bounds.entry(p.clone()).or_default().push(t.clone());
        }
        self.self_ty = job.self_ty.clone();
        self.pending.clear();
        let g = self.info.globals[&job.global].clone();
        let (params, ret) = g.scheme.ty.uncurry_n(g.n_params);
        let mut scope = HashMap::new();
        let mut params = params.into_iter();
        if job.def.self_param.is_some() {
            scope.insert("self".to_string(), (params.next().unwrap(), false));
        }
        for (p, t) in job.def.params.iter().zip(params) {
            scope.insert(p.name.clone(), (t, false));
        }
        self.scopes = vec![scope];
        self.ret_ty = ret.clone();
        let body_ty = self.block(&job.def.body)?;
        self.inf.unify(&ret, &body_ty, last_span(&job.def.body, job.def.span))?;
        self.solve_pending()?;
        if !job.generalize {
            // Declared generics: every remaining variable must have been fixed by the body.
            let ty = self.inf.resolve(&g.scheme.ty);
            if ty.has_var() {
                let what = if job.def.ret.is_none() { "return type" } else { "type" };
                return Err(Diagnostic::new(job.def.span, format!("cannot infer the {what} of `{}`; add an annotation", job.def.name)));
            }
            self.reject_unresolved_pending()?;
        }
        Ok(())
    }

    fn param_name(&mut self, v: u32) -> String {
        if let Some(n) = self.gen_map.get(&v) {
            return n.clone();
        }
        let n = format!("T{}", self.next_param);
        self.next_param += 1;
        self.gen_map.insert(v, n.clone());
        n
    }

    fn var_to_param(&self, t: &Type) -> Type {
        match t {
            Type::Var(v) => match self.gen_map.get(v) {
                Some(n) => Type::Param(n.clone()),
                None => t.clone(),
            },
            Type::Param(_) => t.clone(),
            Type::Con(n, args) => Type::Con(n.clone(), args.iter().map(|a| self.var_to_param(a)).collect()),
            Type::Fn(a, b) => Type::Fn(Box::new(self.var_to_param(a)), Box::new(self.var_to_param(b))),
        }
    }

    fn generalize(&mut self, global: &str) -> Result<(), Diagnostic> {
        let ty = self.inf.resolve(&self.info.globals[global].scheme.ty);
        let mut vars = Vec::new();
        ty.vars(&mut vars);
        let names: Vec<String> = vars.iter().map(|v| self.param_name(*v)).collect();
        let mut bounds = Vec::new();
        for (pty, tr, span) in std::mem::take(&mut self.pending) {
            match self.inf.resolve(&pty) {
                Type::Var(v) if vars.contains(&v) => {
                    let b = (self.gen_map[&v].clone(), tr);
                    if !bounds.contains(&b) {
                        bounds.push(b);
                    }
                }
                _ => return Err(Diagnostic::new(span, "type annotations needed")),
            }
        }
        let ty = self.var_to_param(&ty);
        let g = self.info.globals.get_mut(global).unwrap();
        g.scheme = Scheme { vars: names, bounds, ty };
        Ok(())
    }

    fn finish(mut self) -> Result<TypeInfo, Diagnostic> {
        let resolve = |cx: &Checker, t: &Type| cx.var_to_param(&cx.inf.resolve(t));
        let mut expr_types = HashMap::new();
        for (id, t) in &self.info.expr_types {
            let mut t = resolve(&self, t);
            if t.has_var() {
                // Only diverging expressions (`return`) keep a free variable; it is never materialized.
                t = default_vars(&t);
            }
            expr_types.insert(*id, t);
        }
        self.info.expr_types = expr_types;
        let pat_types: HashMap<PatId, Type> = self.info.pat_types.iter().map(|(id, t)| (*id, default_vars(&resolve(&self, t)))).collect();
        self.info.pat_types = pat_types;
        let mut insts = HashMap::new();
        for (id, ts) in &self.info.insts {
            let ts: Vec<Type> = ts.iter().map(|t| resolve(&self, t)).collect();
            if ts.iter().any(Type::has_var) {
                return Err(Diagnostic::new(self.inst_spans[id], "type annotations needed"));
            }
            insts.insert(*id, ts);
        }
        self.info.insts = insts;
        let mut dots = HashMap::new();
        for (id, d) in &self.info.dots {
            let d = match d {
                DotRes::Field(i) => DotRes::Field(*i),
                DotRes::Method(MethodRes::Direct { global, targs }) => {
                    DotRes::Method(MethodRes::Direct { global: global.clone(), targs: targs.iter().map(|t| resolve(&self, t)).collect() })
                }
                DotRes::Method(MethodRes::Trait { trait_name, method, self_ty }) => {
                    DotRes::Method(MethodRes::Trait { trait_name: trait_name.clone(), method: method.clone(), self_ty: resolve(&self, self_ty) })
                }
            };
            dots.insert(*id, d);
        }
        self.info.dots = dots;
        for g in self.info.globals.values_mut() {
            g.scheme.ty = self.inf.resolve(&g.scheme.ty);
        }
        match self.info.globals.get("main") {
            None => return Err(Diagnostic::new(Span::default(), "no `main` function defined")),
            Some(g) if g.n_params != 0 => return Err(Diagnostic::new(Span::default(), "`main` takes no parameters")),
            _ => {}
        }
        // Exhaustiveness, now that every scrutinee type is known.
        let mut cases = Vec::new();
        for item in &self.prog.items {
            match item {
                Item::Def(d) => collect_cases_block(&d.body, &mut cases),
                Item::Impl(i) => i.methods.iter().for_each(|m| collect_cases_block(&m.body, &mut cases)),
                Item::Trait(t) => t.methods.iter().for_each(|m| collect_cases_block(&m.body, &mut cases)),
                _ => {}
            }
        }
        for (scrut, arms, span) in cases {
            let ty = self.info.expr_types[&scrut.id].clone();
            exhaust::check_case(&self.info, &ty, arms, span)?;
        }
        Ok(self.info)
    }

    // ----- statements and expressions -----

    fn block(&mut self, b: &Block) -> Result<Type, Diagnostic> {
        self.scopes.push(HashMap::new());
        let mut last = Type::unit();
        for (i, s) in b.stmts.iter().enumerate() {
            match s {
                Stmt::Let { pat, mutable, init, .. } => {
                    let t = self.expr(init)?;
                    if !self.irrefutable(pat) {
                        return Err(Diagnostic::new(pat.span, "refutable pattern in `let`; use `case`"));
                    }
                    let mut binds = Vec::new();
                    self.check_pat(pat, &t, &mut binds)?;
                    for (name, ty, _) in binds {
                        self.scopes.last_mut().unwrap().insert(name, (ty, *mutable));
                    }
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

    /// Arithmetic operands must be Int, Float, or (for `+`) String. Unresolved defaults to Int.
    fn numeric(&mut self, t: &Type, span: Span, allow_string: bool) -> Result<(), Diagnostic> {
        match self.inf.resolve(t) {
            Type::Var(_) => self.inf.unify(&Type::con("Int"), t, span),
            Type::Con(n, _) if n == "Int" || n == "Float" => Ok(()),
            Type::Con(n, _) if allow_string && n == "String" => Ok(()),
            other => Err(Diagnostic::new(span, format!("expected Int or Float, found {other}"))),
        }
    }

    /// Applies curried `ft` to `args` as in Plan 1. `what` names the callee for errors.
    fn apply(&mut self, mut ft: Type, args: &[Expr], what: &str, span: Span, skip: usize) -> Result<Type, Diagnostic> {
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
                _ => return Err(Diagnostic::new(span, format!("too many arguments: `{what}` takes {}", i + skip))),
            }
        }
        Ok(ft)
    }

    fn global_var(&mut self, e: &Expr, n: &str) -> Result<Type, Diagnostic> {
        let Some(g) = self.info.globals.get(n).cloned() else {
            return Err(Diagnostic::new(e.span, format!("unknown variable `{n}`")));
        };
        if g.scheme.vars.is_empty() {
            if matches!(g.kind, GlobalKind::Def) {
                self.late_insts.push((e.id, n.to_string()));
            }
            return Ok(g.scheme.ty.clone());
        }
        let (t, fresh) = self.instantiate(&g.scheme, HashMap::new(), e.span);
        self.info.insts.insert(e.id, fresh);
        self.inst_spans.insert(e.id, e.span);
        Ok(t)
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
                None => self.global_var(e, n)?,
            },
            ExprKind::Tuple(items) => {
                let mut ts = Vec::new();
                for i in items {
                    ts.push(self.expr(i)?);
                }
                Type::tuple(ts)
            }
            ExprKind::StructLit { name, fields } => self.struct_lit(e, name, fields)?,
            ExprKind::Dot { recv, name, args } => self.dot(e, recv, name, args.as_deref())?,
            ExprKind::TupleIndex(recv, i) => {
                let rt = self.expr(recv)?;
                match self.inf.resolve(&rt) {
                    Type::Con(n, items) if n == "Tuple" && *i < items.len() => items[*i].clone(),
                    Type::Var(_) => return Err(Diagnostic::new(e.span, format!("cannot infer the receiver type of `.{i}`; add an annotation"))),
                    other => return Err(Diagnostic::new(e.span, format!("cannot index `{other}` with `.{i}`"))),
                }
            }
            // Temporary until Task 4 of Plan 3a: references are still erased.
            ExprKind::Ref(_, x) | ExprKind::Deref(x) => self.expr(x)?,
            ExprKind::Unary(UnOp::Neg, x) => {
                let t = self.expr(x)?;
                self.numeric(&t, x.span, false)?;
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
                        self.pending.push((ta.clone(), "Eq".into(), e.span));
                        Type::con("Bool")
                    }
                    BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                        self.inf.unify(&ta, &tb, b.span)?;
                        self.numeric(&ta, a.span, false)?;
                        Type::con("Bool")
                    }
                    BinOp::Add => {
                        self.inf.unify(&ta, &tb, b.span)?;
                        self.numeric(&ta, a.span, true)?;
                        ta
                    }
                    _ => {
                        self.inf.unify(&ta, &tb, b.span)?;
                        self.numeric(&ta, a.span, false)?;
                        ta
                    }
                }
            }
            ExprKind::Call(f, args) => {
                let ft = self.expr(f)?;
                let what = match &f.kind {
                    ExprKind::Var(n) => n.clone(),
                    _ => "expression".to_string(),
                };
                self.apply(ft, args, &what, e.span, 0)?
            }
            ExprKind::If { cond, then, els } => {
                let ct = self.expr(cond)?;
                self.inf.unify(&Type::con("Bool"), &ct, cond.span)?;
                let tt = self.block(then)?;
                match els {
                    Some(b) => {
                        let et = self.block(b)?;
                        self.inf.unify(&tt, &et, last_span(b, b.span))?;
                    }
                    None => self.inf.unify(&Type::unit(), &tt, last_span(then, then.span))?,
                }
                tt
            }
            ExprKind::While { cond, body } => {
                let ct = self.expr(cond)?;
                self.inf.unify(&Type::con("Bool"), &ct, cond.span)?;
                self.block(body)?;
                Type::unit()
            }
            ExprKind::Case { scrutinee, arms } => {
                let st = self.expr(scrutinee)?;
                let result = self.inf.fresh();
                for arm in arms {
                    let mut binds = Vec::new();
                    self.check_pat(&arm.pat, &st, &mut binds)?;
                    let mut scope = HashMap::new();
                    for (name, ty, _) in binds {
                        scope.insert(name, (ty, false));
                    }
                    self.scopes.push(scope);
                    if let Some(g) = &arm.guard {
                        let gt = self.expr(g)?;
                        self.inf.unify(&Type::con("Bool"), &gt, g.span)?;
                    }
                    let bt = self.block(&arm.body)?;
                    self.inf.unify(&result, &bt, last_span(&arm.body, arm.span))?;
                    self.scopes.pop();
                }
                result
            }
            ExprKind::Interp(parts) => {
                for p in parts {
                    if let InterpPart::Expr(x) = p {
                        let t = self.expr(x)?;
                        self.pending.push((t, "Show".into(), x.span));
                    }
                }
                Type::con("String")
            }
            ExprKind::Assign(lhs, rhs) => {
                let lt = self.assign_target(lhs)?;
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

    /// Type of an assignment target, checking mutability of the root variable.
    fn assign_target(&mut self, lhs: &Expr) -> Result<Type, Diagnostic> {
        let t = match &lhs.kind {
            ExprKind::Var(name) => {
                let (lt, mutable) = match self.lookup(name) {
                    Some(v) => v,
                    None => return Err(Diagnostic::new(lhs.span, format!("unknown variable `{name}`"))),
                };
                if !mutable {
                    return Err(Diagnostic::new(lhs.span, format!("cannot assign twice to immutable variable `{name}`")));
                }
                lt
            }
            ExprKind::Dot { recv, name, args: None } => {
                let rt = self.assign_target(recv)?;
                let (idx, fty) = self.field_of(&rt, name, lhs.span)?;
                self.info.dots.insert(lhs.id, DotRes::Field(idx));
                fty
            }
            ExprKind::TupleIndex(recv, i) => {
                let rt = self.assign_target(recv)?;
                match self.inf.resolve(&rt) {
                    Type::Con(n, items) if n == "Tuple" && *i < items.len() => items[*i].clone(),
                    other => return Err(Diagnostic::new(lhs.span, format!("cannot index `{other}` with `.{i}`"))),
                }
            }
            _ => return Err(Diagnostic::new(lhs.span, "cannot assign to this expression")),
        };
        Ok(self.record(lhs, t))
    }

    /// Field index and type of `name` on struct type `t`.
    fn field_of(&self, t: &Type, name: &str, span: Span) -> Result<(usize, Type), Diagnostic> {
        let rt = self.inf.resolve(t);
        if let Type::Con(head, targs) = &rt {
            if let Some(s) = self.info.structs.get(head) {
                if let Some(idx) = s.fields.iter().position(|(f, _)| f == name) {
                    let map: HashMap<String, Type> = s.generics.iter().cloned().zip(targs.iter().cloned()).collect();
                    return Ok((idx, subst(&s.fields[idx].1, &map)));
                }
            }
        }
        if matches!(rt, Type::Var(_)) {
            return Err(Diagnostic::new(span, format!("cannot infer the receiver type of `.{name}`; add an annotation")));
        }
        Err(Diagnostic::new(span, format!("no field or method `{name}` on type `{rt}`")))
    }

    fn struct_lit(&mut self, e: &Expr, name: &str, fields: &[(String, Expr)]) -> Result<Type, Diagnostic> {
        // (declared fields, generics, result type)
        let (decl, generics, ty, fresh): (Vec<(String, Type)>, Vec<String>, Type, Vec<Type>) = if let Some(s) = self.info.structs.get(name).cloned() {
            let fresh: Vec<Type> = s.generics.iter().map(|_| self.inf.fresh()).collect();
            (s.fields.clone(), s.generics.clone(), Type::Con(name.to_string(), fresh.clone()), fresh)
        } else if let Some((en, idx)) = self.info.variant_names.get(name).cloned() {
            let en_info = self.info.enums[&en].clone();
            let v = &en_info.variants[idx];
            if v.fields.iter().any(|(n, _)| n.is_none()) {
                return Err(Diagnostic::new(e.span, format!("variant `{name}` has positional fields; use `{name}(..)`")));
            }
            let fresh: Vec<Type> = en_info.generics.iter().map(|_| self.inf.fresh()).collect();
            let decl = v.fields.iter().map(|(n, t)| (n.clone().unwrap(), t.clone())).collect();
            (decl, en_info.generics.clone(), Type::Con(en, fresh.clone()), fresh)
        } else {
            return Err(Diagnostic::new(e.span, format!("unknown struct or variant `{name}`")));
        };
        if !fresh.is_empty() {
            self.info.insts.insert(e.id, fresh.clone());
            self.inst_spans.insert(e.id, e.span);
        }
        let map: HashMap<String, Type> = generics.into_iter().zip(fresh).collect();
        let mut seen = HashSet::new();
        for (fname, value) in fields {
            let Some((_, fty)) = decl.iter().find(|(n, _)| n == fname) else {
                return Err(Diagnostic::new(value.span, format!("unknown field `{fname}` in `{name}`")));
            };
            if !seen.insert(fname.clone()) {
                return Err(Diagnostic::new(value.span, format!("field `{fname}` given twice")));
            }
            let vt = self.expr(value)?;
            self.inf.unify(&subst(fty, &map), &vt, value.span)?;
        }
        for (fname, _) in &decl {
            if !seen.contains(fname) {
                return Err(Diagnostic::new(e.span, format!("missing field `{fname}` in `{name}`")));
            }
        }
        Ok(ty)
    }

    fn dot(&mut self, e: &Expr, recv: &Expr, name: &str, args: Option<&[Expr]>) -> Result<Type, Diagnostic> {
        let rt = self.expr(recv)?;
        let rt = self.inf.resolve(&rt);
        if matches!(rt, Type::Var(_)) {
            return Err(Diagnostic::new(e.span, format!("cannot infer the receiver type of `.{name}`; add an annotation")));
        }
        // Field access.
        if args.is_none() {
            if let Type::Con(head, _) = &rt {
                if self.info.structs.get(head).map_or(false, |s| s.fields.iter().any(|(f, _)| f == name)) {
                    let (idx, fty) = self.field_of(&rt, name, e.span)?;
                    self.info.dots.insert(e.id, DotRes::Field(idx));
                    return Ok(fty);
                }
            }
        }
        // Inherent methods.
        if let Type::Con(head, _) = &rt {
            let hit = self.info.impls.iter().find(|i| i.trait_name.is_none() && i.self_ty.head() == Some(head) && i.methods.contains_key(name)).map(|i| i.methods[name].clone());
            if let Some(global) = hit {
                let g = self.info.globals[&global].clone();
                let (ft, fresh) = self.instantiate(&g.scheme, HashMap::new(), e.span);
                let (mut params, _) = ft.uncurry_n(1);
                self.inf.unify(&params.remove(0), &rt, recv.span)?;
                let Type::Fn(_, rest) = ft else { unreachable!() };
                self.info.dots.insert(e.id, DotRes::Method(MethodRes::Direct { global, targs: fresh }));
                self.inst_spans.insert(e.id, e.span);
                return self.apply(*rest, args.unwrap_or(&[]), name, e.span, 0);
            }
        }
        // Trait methods.
        let mut candidates: Vec<String> = Vec::new();
        let mut trait_names: Vec<String> = self.info.traits.keys().cloned().collect();
        trait_names.sort();
        let mut with_method = Vec::new();
        for tn in trait_names {
            if !self.info.traits[&tn].methods.contains_key(name) {
                continue;
            }
            with_method.push(tn.clone());
            let applicable = match &rt {
                Type::Param(p) => self.bounds_of(p).contains(&tn),
                _ => self.info.impls.iter().any(|i| {
                    i.trait_name.as_deref() == Some(&tn) && (matches!(i.self_ty, Type::Param(_)) || i.self_ty.head() == rt.head())
                }),
            };
            if applicable {
                candidates.push(tn);
            }
        }
        candidates.sort();
        let tn = match candidates.len() {
            0 => {
                if let (Type::Param(p), Some(tn)) = (&rt, with_method.first()) {
                    return Err(Diagnostic::new(e.span, format!("`{p}` is not bounded by `{tn}`; add `{p}: {tn}`")));
                }
                return Err(Diagnostic::new(e.span, format!("no field or method `{name}` on type `{rt}`")));
            }
            1 => candidates.pop().unwrap(),
            _ => {
                return Err(Diagnostic::new(
                    e.span,
                    format!("ambiguous method `{name}` on type `{rt}`: candidates `{}`", candidates.join("`, `")),
                ))
            }
        };
        let sig = self.info.traits[&tn].methods[name].clone();
        let mut fixed = HashMap::new();
        fixed.insert("Self".to_string(), rt.clone());
        let (ft, _) = self.instantiate(&sig.scheme, fixed, e.span);
        let Type::Fn(_, rest) = ft else { unreachable!("trait methods take self") };
        self.info.dots.insert(e.id, DotRes::Method(MethodRes::Trait { trait_name: tn, method: name.to_string(), self_ty: rt }));
        self.apply(*rest, args.unwrap_or(&[]), name, e.span, 0)
    }

    // ----- patterns -----

    fn irrefutable(&self, p: &Pattern) -> bool {
        match &p.kind {
            PatKind::Wild | PatKind::Bind(_) => true,
            PatKind::Lit(Lit::Unit) => true,
            PatKind::Lit(_) => false,
            PatKind::Tuple(ps) => ps.iter().all(|q| self.irrefutable(q)),
            PatKind::At(_, inner) => self.irrefutable(inner),
            PatKind::Or(alts) => alts.iter().any(|q| self.irrefutable(q)),
            PatKind::Variant { name, fields } => {
                let single = self.info.variant_names.get(name).map_or(false, |(en, _)| self.info.enums[en].variants.len() == 1);
                single && fields.iter().all(|q| self.irrefutable(q))
            }
            PatKind::Struct { name, fields } => {
                let ok = self.info.structs.contains_key(name)
                    || self.info.variant_names.get(name).map_or(false, |(en, _)| self.info.enums[en].variants.len() == 1);
                ok && fields.iter().all(|(_, q)| self.irrefutable(q))
            }
        }
    }

    fn check_pat(&mut self, pat: &Pattern, expected: &Type, binds: &mut Vec<(String, Type, Span)>) -> Result<(), Diagnostic> {
        self.info.pat_types.insert(pat.id, expected.clone());
        match &pat.kind {
            PatKind::Wild => Ok(()),
            PatKind::Bind(n) => {
                if binds.iter().any(|(b, _, _)| b == n) {
                    return Err(Diagnostic::new(pat.span, format!("`{n}` is bound more than once in this pattern")));
                }
                binds.push((n.clone(), expected.clone(), pat.span));
                Ok(())
            }
            PatKind::Lit(l) => self.inf.unify(expected, &lit_type(l), pat.span),
            PatKind::Tuple(ps) => {
                let fresh: Vec<Type> = ps.iter().map(|_| self.inf.fresh()).collect();
                self.inf.unify(expected, &Type::tuple(fresh.clone()), pat.span)?;
                for (p, t) in ps.iter().zip(&fresh) {
                    self.check_pat(p, t, binds)?;
                }
                Ok(())
            }
            PatKind::Variant { name, fields } => {
                let Some((en, idx)) = self.info.variant_names.get(name).cloned() else {
                    return Err(Diagnostic::new(pat.span, format!("unknown variant `{name}`")));
                };
                let en_info = self.info.enums[&en].clone();
                let v = &en_info.variants[idx];
                if v.fields.iter().any(|(n, _)| n.is_some()) {
                    return Err(Diagnostic::new(pat.span, format!("variant `{name}` has named fields; use `{name} {{ .. }}`")));
                }
                if v.fields.len() != fields.len() {
                    return Err(Diagnostic::new(pat.span, format!("variant `{name}` has {} fields, pattern has {}", v.fields.len(), fields.len())));
                }
                let fresh: Vec<Type> = en_info.generics.iter().map(|_| self.inf.fresh()).collect();
                self.inf.unify(expected, &Type::Con(en.clone(), fresh.clone()), pat.span)?;
                let map: HashMap<String, Type> = en_info.generics.iter().cloned().zip(fresh).collect();
                for (p, (_, ft)) in fields.iter().zip(&v.fields) {
                    self.check_pat(p, &subst(ft, &map), binds)?;
                }
                Ok(())
            }
            PatKind::Struct { name, fields } => {
                let (decl, generics, ty): (Vec<(String, Type)>, Vec<String>, Type) = if let Some(s) = self.info.structs.get(name).cloned() {
                    let fresh: Vec<Type> = s.generics.iter().map(|_| self.inf.fresh()).collect();
                    (s.fields.clone(), s.generics.clone(), Type::Con(name.clone(), fresh))
                } else if let Some((en, idx)) = self.info.variant_names.get(name).cloned() {
                    let en_info = self.info.enums[&en].clone();
                    let v = &en_info.variants[idx];
                    if v.fields.iter().any(|(n, _)| n.is_none()) {
                        return Err(Diagnostic::new(pat.span, format!("variant `{name}` has positional fields; use `{name}(..)`")));
                    }
                    let fresh: Vec<Type> = en_info.generics.iter().map(|_| self.inf.fresh()).collect();
                    (v.fields.iter().map(|(n, t)| (n.clone().unwrap(), t.clone())).collect(), en_info.generics.clone(), Type::Con(en, fresh))
                } else {
                    return Err(Diagnostic::new(pat.span, format!("unknown struct or variant `{name}`")));
                };
                let Type::Con(_, fresh) = &ty else { unreachable!() };
                let map: HashMap<String, Type> = generics.into_iter().zip(fresh.iter().cloned()).collect();
                self.inf.unify(expected, &ty, pat.span)?;
                let mut seen = HashSet::new();
                for (fname, p) in fields {
                    let Some((_, fty)) = decl.iter().find(|(n, _)| n == fname) else {
                        return Err(Diagnostic::new(p.span, format!("unknown field `{fname}` in `{name}`")));
                    };
                    if !seen.insert(fname.clone()) {
                        return Err(Diagnostic::new(p.span, format!("field `{fname}` given twice")));
                    }
                    self.check_pat(p, &subst(fty, &map), binds)?;
                }
                Ok(())
            }
            PatKind::Or(alts) => {
                let mut first: Option<Vec<(String, Type, Span)>> = None;
                for alt in alts {
                    let mut b = Vec::new();
                    self.check_pat(alt, expected, &mut b)?;
                    match &first {
                        None => first = Some(b),
                        Some(f) => {
                            let names = |v: &Vec<(String, Type, Span)>| {
                                let mut n: Vec<&String> = v.iter().map(|(n, _, _)| n).collect();
                                n.sort();
                                n.into_iter().cloned().collect::<Vec<_>>()
                            };
                            if names(f) != names(&b) {
                                return Err(Diagnostic::new(pat.span, "pattern alternatives bind different names"));
                            }
                            for (n, t, sp) in &b {
                                let (_, ft, _) = f.iter().find(|(m, _, _)| m == n).unwrap();
                                self.inf.unify(ft, t, *sp)?;
                            }
                        }
                    }
                }
                for (n, t, sp) in first.unwrap_or_default() {
                    if binds.iter().any(|(b, _, _)| *b == n) {
                        return Err(Diagnostic::new(sp, format!("`{n}` is bound more than once in this pattern")));
                    }
                    binds.push((n, t, sp));
                }
                Ok(())
            }
            PatKind::At(n, inner) => {
                if binds.iter().any(|(b, _, _)| b == n) {
                    return Err(Diagnostic::new(pat.span, format!("`{n}` is bound more than once in this pattern")));
                }
                binds.push((n.clone(), expected.clone(), pat.span));
                self.check_pat(inner, expected, binds)
            }
        }
    }
}

/// Replaces leftover variables (only from diverging expressions) with Unit.
fn default_vars(t: &Type) -> Type {
    match t {
        Type::Var(_) => Type::unit(),
        Type::Param(_) => t.clone(),
        Type::Con(n, args) => Type::Con(n.clone(), args.iter().map(default_vars).collect()),
        Type::Fn(a, b) => Type::Fn(Box::new(default_vars(a)), Box::new(default_vars(b))),
    }
}

// ----- AST walks -----

fn collect_refs_block(b: &Block, out: &mut Vec<String>) {
    for s in &b.stmts {
        match s {
            Stmt::Let { init, .. } => collect_refs(init, out),
            Stmt::Expr(e) => collect_refs(e, out),
        }
    }
}

fn collect_refs(e: &Expr, out: &mut Vec<String>) {
    match &e.kind {
        ExprKind::Var(n) => out.push(n.clone()),
        ExprKind::Tuple(items) => items.iter().for_each(|i| collect_refs(i, out)),
        ExprKind::StructLit { fields, .. } => fields.iter().for_each(|(_, v)| collect_refs(v, out)),
        ExprKind::Dot { recv, args, .. } => {
            collect_refs(recv, out);
            args.iter().flatten().for_each(|a| collect_refs(a, out));
        }
        ExprKind::TupleIndex(r, _) => collect_refs(r, out),
        ExprKind::Ref(_, x) | ExprKind::Deref(x) => collect_refs(x, out),
        ExprKind::Unary(_, x) => collect_refs(x, out),
        ExprKind::Binary(_, a, b) => {
            collect_refs(a, out);
            collect_refs(b, out);
        }
        ExprKind::Call(f, args) => {
            collect_refs(f, out);
            args.iter().for_each(|a| collect_refs(a, out));
        }
        ExprKind::If { cond, then, els } => {
            collect_refs(cond, out);
            collect_refs_block(then, out);
            if let Some(b) = els {
                collect_refs_block(b, out);
            }
        }
        ExprKind::While { cond, body } => {
            collect_refs(cond, out);
            collect_refs_block(body, out);
        }
        ExprKind::Case { scrutinee, arms } => {
            collect_refs(scrutinee, out);
            for a in arms {
                if let Some(g) = &a.guard {
                    collect_refs(g, out);
                }
                collect_refs_block(&a.body, out);
            }
        }
        ExprKind::Interp(parts) => parts.iter().for_each(|p| {
            if let InterpPart::Expr(x) = p {
                collect_refs(x, out)
            }
        }),
        ExprKind::Assign(a, b) => {
            collect_refs(a, out);
            collect_refs(b, out);
        }
        ExprKind::Return(v) => v.iter().for_each(|x| collect_refs(x, out)),
        _ => {}
    }
}

pub(super) fn collect_cases_block<'a>(b: &'a Block, out: &mut Vec<(&'a Expr, &'a [Arm], Span)>) {
    for s in &b.stmts {
        match s {
            Stmt::Let { init, .. } => collect_cases(init, out),
            Stmt::Expr(e) => collect_cases(e, out),
        }
    }
}

fn collect_cases<'a>(e: &'a Expr, out: &mut Vec<(&'a Expr, &'a [Arm], Span)>) {
    match &e.kind {
        ExprKind::Case { scrutinee, arms } => {
            out.push((scrutinee, arms, e.span));
            collect_cases(scrutinee, out);
            for a in arms {
                if let Some(g) = &a.guard {
                    collect_cases(g, out);
                }
                collect_cases_block(&a.body, out);
            }
        }
        ExprKind::Tuple(items) => items.iter().for_each(|i| collect_cases(i, out)),
        ExprKind::StructLit { fields, .. } => fields.iter().for_each(|(_, v)| collect_cases(v, out)),
        ExprKind::Dot { recv, args, .. } => {
            collect_cases(recv, out);
            args.iter().flatten().for_each(|a| collect_cases(a, out));
        }
        ExprKind::TupleIndex(r, _) => collect_cases(r, out),
        ExprKind::Ref(_, x) | ExprKind::Deref(x) => collect_cases(x, out),
        ExprKind::Unary(_, x) => collect_cases(x, out),
        ExprKind::Binary(_, a, b) => {
            collect_cases(a, out);
            collect_cases(b, out);
        }
        ExprKind::Call(f, args) => {
            collect_cases(f, out);
            args.iter().for_each(|a| collect_cases(a, out));
        }
        ExprKind::If { cond, then, els } => {
            collect_cases(cond, out);
            collect_cases_block(then, out);
            if let Some(b) = els {
                collect_cases_block(b, out);
            }
        }
        ExprKind::While { cond, body } => {
            collect_cases(cond, out);
            collect_cases_block(body, out);
        }
        ExprKind::Interp(parts) => parts.iter().for_each(|p| {
            if let InterpPart::Expr(x) = p {
                collect_cases(x, out)
            }
        }),
        ExprKind::Assign(a, b) => {
            collect_cases(a, out);
            collect_cases(b, out);
        }
        ExprKind::Return(v) => v.iter().for_each(|x| collect_cases(x, out)),
        _ => {}
    }
}

/// Tarjan's SCC, returning groups in dependency order (callees before callers).
fn scc_order(nodes: &[usize], edges: &HashMap<usize, Vec<usize>>) -> Vec<Vec<usize>> {
    struct St<'e> {
        edges: &'e HashMap<usize, Vec<usize>>,
        index: HashMap<usize, usize>,
        low: HashMap<usize, usize>,
        on_stack: HashSet<usize>,
        stack: Vec<usize>,
        next: usize,
        out: Vec<Vec<usize>>,
    }
    fn visit(s: &mut St, v: usize) {
        s.index.insert(v, s.next);
        s.low.insert(v, s.next);
        s.next += 1;
        s.stack.push(v);
        s.on_stack.insert(v);
        for &w in s.edges.get(&v).map(|v| v.as_slice()).unwrap_or(&[]) {
            if !s.index.contains_key(&w) {
                visit(s, w);
                let lw = s.low[&w];
                let lv = s.low.get_mut(&v).unwrap();
                *lv = (*lv).min(lw);
            } else if s.on_stack.contains(&w) {
                let iw = s.index[&w];
                let lv = s.low.get_mut(&v).unwrap();
                *lv = (*lv).min(iw);
            }
        }
        if s.low[&v] == s.index[&v] {
            let mut group = Vec::new();
            loop {
                let w = s.stack.pop().unwrap();
                s.on_stack.remove(&w);
                group.push(w);
                if w == v {
                    break;
                }
            }
            group.sort();
            s.out.push(group);
        }
    }
    let mut s = St { edges, index: HashMap::new(), low: HashMap::new(), on_stack: HashSet::new(), stack: vec![], next: 0, out: vec![] };
    for &n in nodes {
        if !s.index.contains_key(&n) {
            visit(&mut s, n);
        }
    }
    s.out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::lex;
    use crate::parser::parse;

    pub fn check_src(s: &str) -> Result<TypeInfo, Diagnostic> {
        let prelude = include_str!("../../std/prelude.rush");
        let mut id = 0;
        let mut p = parse(lex(prelude).unwrap(), &mut id).unwrap();
        p.items.extend(parse(lex(s).unwrap(), &mut id).unwrap().items);
        check_program(&p)
    }

    fn err(s: &str) -> String {
        check_src(s).unwrap_err().msg
    }

    /// Looks up a global by exact name, or an impl method by `Prefix#*::method`.
    fn global<'i>(info: &'i TypeInfo, name: &str) -> &'i Global {
        if let Some(g) = info.globals.get(name) {
            return g;
        }
        let (prefix, method) = name.split_once("#*::").expect("global name");
        let mut hits: Vec<&String> = info.globals.keys().filter(|k| k.starts_with(&format!("{prefix}#")) && k.ends_with(&format!("::{method}"))).collect();
        hits.sort();
        let key: &String = hits.last().unwrap_or_else(|| panic!("no global {name}"));
        &info.globals[key.as_str()]
    }

    fn scheme(s: &str, name: &str) -> String {
        let info = check_src(s).unwrap();
        let g = global(&info, name);
        let bounds: Vec<String> = g.scheme.bounds.iter().map(|(p, t)| format!("{p}: {t}")).collect();
        format!("[{}] [{}] {}", g.scheme.vars.join(", "), bounds.join(", "), g.scheme.ty)
    }

    const POINT: &str = "struct Point\n  x: Float\n  y: Float\nend\n";

    #[test]
    fn plan1_basics_still_hold() {
        assert_eq!(scheme("def fib(n: Int) -> Int\n  if n < 2\n    n\n  else\n    fib(n - 1) + fib(n - 2)\n  end\nend\ndef main\n  puts(int_to_s(fib(5)))\nend\n", "fib"), "[] [] Int -> Int");
        assert_eq!(scheme("def inc(x)\n  x + 1\nend\ndef main\n  inc(2)\n  ()\nend\n", "inc"), "[] [] Int -> Int");
        assert_eq!(err("def main\n  let x = 1 + true\nend\n"), "type mismatch: expected Int, found Bool");
        assert_eq!(err("def main\n  let x = 1\n  x = 2\nend\n"), "cannot assign twice to immutable variable `x`");
        assert_eq!(err("def main\n  puts(\"a\", \"b\")\nend\n"), "too many arguments: `puts` takes 1");
        assert_eq!(err("def f\n  1\nend\n"), "no `main` function defined");
        // An unused parameter is generic now, not an error.
        assert_eq!(scheme("def f(x)\n  1\nend\ndef main\n  ()\nend\n", "f"), "[T0] [] T0 -> Int");
    }

    #[test]
    fn struct_literal_field_access_and_inherent_method() {
        let src = format!("{POINT}impl Point\n  def swap(&self) -> Point\n    Point {{ x: self.y, y: self.x }}\n  end\nend\ndef main\n  let p = Point {{ x: 1.0, y: 2.0 }}\n  let q = p.swap\n  let f = q.x + 1.0\n  ()\nend\n");
        let info = check_src(&src).unwrap();
        assert_eq!(global(&info, "Point#*::swap").scheme.ty.to_string(), "Point -> Point");
        assert!(info.dots.values().any(|d| matches!(d, DotRes::Field(1))));
        assert!(info.dots.values().any(|d| matches!(d, DotRes::Method(MethodRes::Direct { global, .. }) if global.ends_with("::swap"))));
    }

    #[test]
    fn generic_struct_infers_type_args() {
        let src = "struct Pair[A, B]\n  first: A\n  second: B\nend\ndef main\n  let p = Pair { first: 1, second: \"a\" }\n  let s = p.second\n  ()\nend\n";
        let info = check_src(src).unwrap();
        let mut types: Vec<String> = info.expr_types.values().map(|t| t.to_string()).collect();
        types.sort();
        types.dedup();
        assert!(types.contains(&"Pair[Int, String]".to_string()), "{types:?}");
    }

    #[test]
    fn variant_constructors_are_functions() {
        let src = "enum Shape\n  Circle(Float)\n  Empty\nend\ndef main\n  let c = Circle(1.0)\n  let e = Empty\n  let o = Some(3)\n  ()\nend\n";
        let info = check_src(src).unwrap();
        assert_eq!(info.globals["Circle"].scheme.ty.to_string(), "Float -> Shape");
        assert_eq!(info.globals["Some"].scheme.ty.to_string(), "T -> Option[T]");
        assert_eq!(info.globals["None"].n_params, 0);
        let mut types: Vec<String> = info.expr_types.values().map(|t| t.to_string()).collect();
        types.sort();
        types.dedup();
        assert!(types.contains(&"Option[Int]".to_string()));
    }

    #[test]
    fn case_binds_and_unifies_arms() {
        let src = "enum Shape\n  Circle(Float)\n  Rect(Float, Float)\nend\ndef area(s: Shape) -> Float\n  case s\n  in Circle(r) then r * r\n  in Rect(w, h) then w * h\n  end\nend\ndef main\n  ()\nend\n";
        check_src(src).unwrap();
        let bad = "enum Shape\n  Circle(Float)\n  Rect(Float, Float)\nend\ndef area(s: Shape) -> Float\n  case s\n  in Circle(r) then r * r\n  in Rect(w, h) then \"x\"\n  end\nend\ndef main\n  ()\nend\n";
        assert_eq!(err(bad), "type mismatch: expected Float, found String");
    }

    #[test]
    fn tuple_index_and_let_destructure() {
        let src = "def main\n  let t = (1, \"a\", true)\n  let (a, b, c) = t\n  let n = t.0 + a\n  let s = b + t.1\n  ()\nend\n";
        check_src(src).unwrap();
        assert_eq!(err("def main\n  let t = (1, 2)\n  t.2\nend\n"), "cannot index `(Int, Int)` with `.2`");
    }

    #[test]
    fn refutable_let_is_error() {
        assert_eq!(err("def main\n  let Some(x) = Some(1)\nend\n"), "refutable pattern in `let`; use `case`");
    }

    #[test]
    fn unannotated_def_is_generalized_and_used_at_two_types() {
        let src = "def pair_up(a, b)\n  (a, b)\nend\ndef main\n  let x = pair_up(1, \"a\")\n  let y = pair_up(true, 2.5)\n  ()\nend\n";
        assert_eq!(scheme(src, "pair_up"), "[T0, T1] [] T0 -> T1 -> (T0, T1)");
        let info = check_src(src).unwrap();
        let mut insts: Vec<String> = info.insts.values().map(|ts| ts.iter().map(|t| t.to_string()).collect::<Vec<_>>().join(",")).collect();
        insts.sort();
        assert_eq!(insts, vec!["Bool,Float", "Int,String"]);
    }

    #[test]
    fn inferred_bounds_from_callee() {
        let src = "def show2[T: Show](x: T) -> String\n  x.to_s + x.to_s\nend\ndef f(x)\n  show2(x)\nend\ndef main\n  f(1)\n  ()\nend\n";
        assert_eq!(scheme(src, "f"), "[T0] [T0: Show] T0 -> String");
    }

    #[test]
    fn annotated_generic_with_bound_method_call() {
        let src = "def f[T: Show](x: T) -> String\n  x.to_s\nend\ndef main\n  puts(f(1))\nend\n";
        let info = check_src(src).unwrap();
        assert!(info.dots.values().any(|d| matches!(d, DotRes::Method(MethodRes::Trait { trait_name, self_ty, .. }) if trait_name == "Show" && *self_ty == Type::Param("T".into()))));
    }

    #[test]
    fn unbounded_param_method_call_error() {
        assert_eq!(err("def f[T](x: T) -> String\n  x.to_s\nend\ndef main\n  ()\nend\n"), "`T` is not bounded by `Show`; add `T: Show`");
    }

    #[test]
    fn missing_instance_error() {
        assert_eq!(err(&format!("{POINT}def main\n  let p = Point {{ x: 1.0, y: 2.0 }}\n  puts(\"#{{p}}\")\nend\n")), "no instance of `Show` for `Point`");
    }

    #[test]
    fn generic_impl_with_bound_resolves_recursively() {
        let ok = format!("{POINT}impl Show for Point\n  def to_s(&self)\n    \"p\"\n  end\nend\ndef main\n  puts(\"#{{Some(Point {{ x: 1.0, y: 2.0 }})}}\")\nend\n");
        check_src(&ok).unwrap();
        let bad = format!("{POINT}def main\n  puts(\"#{{Some(Point {{ x: 1.0, y: 2.0 }})}}\")\nend\n");
        assert_eq!(err(&bad), "no instance of `Show` for `Point`");
    }

    #[test]
    fn inherent_wins_over_trait_method() {
        let src = format!("{POINT}impl Show for Point\n  def to_s(&self)\n    \"trait\"\n  end\nend\nimpl Point\n  def to_s(&self) -> Int\n    1\n  end\nend\ndef main\n  let n = Point {{ x: 1.0, y: 2.0 }}.to_s + 1\n  ()\nend\n");
        check_src(&src).unwrap();
    }

    #[test]
    fn receiver_unknown_error() {
        assert_eq!(err("def f(x)\n  x.foo\nend\ndef main\n  ()\nend\n"), "cannot infer the receiver type of `.foo`; add an annotation");
    }

    #[test]
    fn ambiguous_var_error() {
        assert_eq!(err("def main\n  let x = None\nend\n"), "type annotations needed");
    }

    #[test]
    fn eq_on_user_type_requires_eq_instance() {
        let bad = format!("{POINT}def main\n  let b = Point {{ x: 1.0, y: 2.0 }} == Point {{ x: 1.0, y: 2.0 }}\nend\n");
        assert_eq!(err(&bad), "no instance of `Eq` for `Point`");
        let ok = format!("{POINT}impl Eq for Point\n  def eq(&self, other: Point)\n    self.x == other.x\n  end\nend\ndef main\n  let b = Point {{ x: 1.0, y: 2.0 }} == Point {{ x: 1.0, y: 2.0 }}\nend\n");
        check_src(&ok).unwrap();
    }

    #[test]
    fn supertrait_methods_available_through_bound() {
        let src = "trait Named: Show\n  def name(&self) -> String\nend\ndef f[T: Named](x: T) -> String\n  x.name + x.to_s\nend\ndef main\n  ()\nend\n";
        check_src(src).unwrap();
    }

    #[test]
    fn default_method_and_self_in_trait_body() {
        let src = "trait Area\n  def area(&self) -> Float\n  def describe(&self) -> String\n    \"area #{self.area}\"\n  end\nend\nstruct Sq\n  s: Float\nend\nimpl Area for Sq\n  def area(&self)\n    self.s * self.s\n  end\nend\ndef main\n  puts(Sq { s: 2.0 }.describe)\nend\n";
        let info = check_src(src).unwrap();
        assert_eq!(info.globals["Area::describe"].scheme.ty.to_string(), "Self -> String");
        assert_eq!(global(&info, "Area#*::area").scheme.ty.to_string(), "Sq -> Float");
    }

    #[test]
    fn unknown_field_error() {
        assert_eq!(err(&format!("{POINT}def main\n  Point {{ x: 1.0, y: 2.0 }}.z\nend\n")), "no field or method `z` on type `Point`");
        assert_eq!(err(&format!("{POINT}def main\n  Point {{ x: 1.0 }}\nend\n")), "missing field `y` in `Point`");
    }

    #[test]
    fn field_assignment_requires_mutable_root() {
        assert_eq!(err(&format!("{POINT}def main\n  let p = Point {{ x: 1.0, y: 2.0 }}\n  p.x = 3.0\nend\n")), "cannot assign twice to immutable variable `p`");
        check_src(&format!("{POINT}def main\n  let mut p = Point {{ x: 1.0, y: 2.0 }}\n  p.x = 3.0\n  p.y += 1.0\nend\n")).unwrap();
    }

    #[test]
    fn or_pattern_binding_mismatch() {
        assert_eq!(err("def main\n  case (1, 2)\n  in (a, 2) | (2, b) then a\n  in (_, _) then 0\n  end\nend\n"), "pattern alternatives bind different names");
    }
}
