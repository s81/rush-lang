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

/// A by-value binding whose move-ness is decided once its type is known.
struct BindRecord {
    pat: PatId,
    span: Span,
    guarded: bool,
    copy_params: Vec<String>,
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
    bind_records: Vec<BindRecord>,
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
        bind_records: vec![],
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
        Lit::Symbol(_) => Type::con("Symbol"),
        Lit::Bool(_) => Type::con("Bool"),
        Lit::Unit => Type::unit(),
    }
}

/// Source-level name of a place expression for messages, if it is a simple variable.
fn var_name(e: &Expr) -> Option<&str> {
    match &e.kind {
        ExprKind::Var(n) => Some(n),
        _ => None,
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

    fn copy_params(&self) -> Vec<String> {
        self.param_bounds.keys().filter(|p| self.bounds_of(p).iter().any(|t| t == "Copy")).cloned().collect()
    }

    fn is_copy(&self, t: &Type) -> bool {
        let t = self.inf.resolve(t);
        let bounds = &self.param_bounds;
        let info = &self.info;
        let param_copy = |p: &str| bounds.get(p).map_or(false, |bs| bs.iter().any(|b| info.trait_closure(b).iter().any(|t| t == "Copy")));
        self.info.is_copy(&t, &param_copy)
    }

    /// Whether `e` denotes a named place (a variable or a field/index chain rooted at one).
    fn is_place_expr(&self, e: &Expr) -> bool {
        match &e.kind {
            ExprKind::Var(n) => self.lookup(n).is_some(),
            ExprKind::Dot { recv, args: None, .. } => self.is_place_expr(recv) && matches!(self.info.dots.get(&e.id), Some(DotRes::Field(_))),
            ExprKind::TupleIndex(recv, _) => self.is_place_expr(recv),
            ExprKind::Deref(_) => true,
            _ => false,
        }
    }

    /// Errors unless the place rooted at `e` may be mutated (its root is `let mut`, or it is
    /// reached through a `&mut` reference or is a temporary).
    fn require_mutable(&self, e: &Expr, what: &str) -> Result<(), Diagnostic> {
        match &e.kind {
            ExprKind::Var(n) => match self.lookup(n) {
                Some((t, mutable)) => {
                    if mutable || matches!(self.inf.resolve(&t).as_ref(), Some((true, _))) {
                        Ok(())
                    } else {
                        Err(Diagnostic::new(e.span, format!("cannot {what} `{n}` as mutable; it is not declared `mut`")))
                    }
                }
                None => Ok(()),
            },
            ExprKind::Dot { recv, args: None, .. } | ExprKind::TupleIndex(recv, _) => {
                let rt = self.inf.resolve(&self.info.expr_types[&recv.id]);
                match rt.as_ref() {
                    Some((true, _)) => Ok(()),
                    Some((false, _)) => Err(Diagnostic::new(e.span, format!("cannot {what} through a shared reference"))),
                    None => self.require_mutable(recv, what),
                }
            }
            ExprKind::Deref(inner) => {
                let it = self.inf.resolve(&self.info.expr_types[&inner.id]);
                match it.as_ref() {
                    Some((true, _)) => Ok(()),
                    _ => Err(Diagnostic::new(e.span, format!("cannot {what} through a shared reference"))),
                }
            }
            _ => Ok(()),
        }
    }

    /// Reads a `Copy` value out of a reference when a plain value is expected.
    fn value_of(&mut self, e: &Expr, t: &Type) -> Type {
        let r = self.inf.resolve(t);
        if let Some((_, inner)) = r.as_ref() {
            if self.is_copy(inner) {
                self.info.derefs.insert(e.id);
                return inner.clone();
            }
        }
        t.clone()
    }

    /// Adapts a value of type `found` (expression `e`) to an expected type: auto-deref of
    /// `Copy` references, or an error asking for `.clone` when a non-`Copy` reference is
    /// used as a value.
    fn coerce(&mut self, e: &Expr, found: &Type, expected: &Type) -> Result<Type, Diagnostic> {
        let f = self.inf.resolve(found);
        let x = self.inf.resolve(expected);
        if let Some((_, inner)) = f.as_ref() {
            if x.as_ref().is_none() && !matches!(x, Type::Var(_)) {
                if self.is_copy(inner) {
                    self.info.derefs.insert(e.id);
                    return Ok(inner.clone());
                }
                let mut probe = Infer { subst: self.inf.subst.clone() };
                if probe.unify(&x, inner, e.span).is_ok() {
                    return Err(Diagnostic::new(e.span, format!("expected `{x}`, found `{f}`; use `.clone`")));
                }
            }
        }
        Ok(found.clone())
    }

    /// Adapts an argument to a parameter type: explicit `&x` for named places, auto-borrow
    /// for temporaries, auto-deref of `Copy` references.
    fn adapt_arg(&mut self, arg: &Expr, found: &Type, param: &Type) -> Result<Type, Diagnostic> {
        let p = self.inf.resolve(param);
        let f = self.inf.resolve(found);
        if let Some((m, _)) = p.as_ref() {
            if f.as_ref().is_none() && !matches!(f, Type::Var(_)) {
                if self.is_place_expr(arg) {
                    let hint = match var_name(arg) {
                        Some(n) => format!("write `&{n}`"),
                        None => "add `&`".to_string(),
                    };
                    return Err(Diagnostic::new(arg.span, format!("expected `{p}`, found `{f}`; {hint}")));
                }
                if m {
                    self.require_mutable(arg, "borrow")?;
                }
                self.info.autorefs.insert(arg.id, m);
                return Ok(Type::r#ref(m, f));
            }
            return Ok(found.clone());
        }
        self.coerce(arg, found, param)
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

    /// Finds the impl of `trait_name` for `ty`, falling back to the pointee of a reference.
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
        if undecided {
            return Match::Undecided;
        }
        match ty.as_ref() {
            Some((_, inner)) => self.find_impl(trait_name, inner),
            None => Match::No,
        }
    }

    /// Discharges pending constraints that can be decided now; keeps the rest.
    fn solve_pending(&mut self) -> Result<(), Diagnostic> {
        let mut work = std::mem::take(&mut self.pending);
        let mut remaining = Vec::new();
        while let Some((ty, tr, span)) = work.pop() {
            let ty = self.inf.resolve(&ty);
            match ty.peel() {
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
                    Match::No => return Err(Diagnostic::new(span, format!("no instance of `{tr}` for `{}`", ty.peel()))),
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
        // Elision needs final signatures, which unannotated defs only have now.
        for job in &jobs {
            let g = &self.info.globals[&job.global];
            let ty = self.inf.resolve(&g.scheme.ty);
            let (params, ret) = ty.uncurry_n(g.n_params);
            match self.info.elide(&params, job.def.self_param.is_some(), &ret) {
                Ok(Some(i)) => {
                    self.info.elided.insert(job.global.clone(), i);
                }
                Ok(None) => {}
                Err(()) => return Err(super::decls::elision_error(job.def)),
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
        let body_ty = match job.def.body.stmts.last() {
            Some(Stmt::Expr(e)) => self.coerce(e, &body_ty, &ret)?,
            _ => body_ty,
        };
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
            match self.inf.resolve(&pty).peel() {
                Type::Var(v) if vars.contains(v) => {
                    let b = (self.gen_map[v].clone(), tr);
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
                DotRes::Assoc { global, targs } => DotRes::Assoc { global: global.clone(), targs: targs.iter().map(|t| resolve(&self, t)).collect() },
            };
            dots.insert(*id, d);
        }
        self.info.dots = dots;
        for g in self.info.globals.values_mut() {
            g.scheme.ty = self.inf.resolve(&g.scheme.ty);
        }
        // By-value bindings of non-Copy values move out of the scrutinee.
        for r in std::mem::take(&mut self.bind_records) {
            let t = self.info.pat_types[&r.pat].clone();
            let cps = r.copy_params.clone();
            let param_copy = |p: &str| cps.iter().any(|c| c == p);
            if !self.info.is_copy(&t, &param_copy) {
                if r.guarded {
                    return Err(Diagnostic::new(r.span, "cannot move out of a pattern binding in an arm with a guard; match on a reference"));
                }
                self.info.pat_moves.insert(r.pat);
            }
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
            let ty = self.info.expr_types[&scrut.id].peel().clone();
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
                    if let PatKind::Bind(name) = &pat.kind {
                        // A plain binding takes the whole value; no pattern bookkeeping.
                        self.info.pat_types.insert(pat.id, t.clone());
                        self.scopes.last_mut().unwrap().insert(name.clone(), (t, *mutable));
                        last = Type::unit();
                        continue;
                    }
                    if !self.irrefutable(pat) {
                        return Err(Diagnostic::new(pat.span, "refutable pattern in `let`; use `case`"));
                    }
                    let mut binds = Vec::new();
                    self.check_pat(pat, &t, None, false, &mut binds)?;
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

    /// A block whose value is a `Copy` reference yields the copied value.
    fn block_value(&mut self, b: &Block, t: &Type) -> Type {
        match b.stmts.last() {
            Some(Stmt::Expr(e)) => self.value_of(e, t),
            _ => t.clone(),
        }
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
                    let at = self.adapt_arg(arg, &at, &p)?;
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
            if self.adts.contains_key(n) {
                return Err(Diagnostic::new(e.span, format!("`{n}` is a type; call an associated function as `{n}.name(..)`")));
            }
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
            ExprKind::Symbol(_) => Type::con("Symbol"),
            ExprKind::Range(a, b, _) => {
                let ta = self.expr(a)?;
                let tb = self.expr(b)?;
                self.inf.unify(&ta, &tb, b.span)?;
                Type::Con("Range".into(), vec![ta])
            }
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
                let rt = self.inf.resolve(&rt);
                let base = rt.peel().clone();
                match &base {
                    Type::Con(n, items) if n == "Tuple" && *i < items.len() => {
                        if rt.as_ref().is_some() {
                            self.info.adjust.insert(recv.id, Adjust::AutoDeref);
                        }
                        items[*i].clone()
                    }
                    Type::Var(_) => return Err(Diagnostic::new(e.span, format!("cannot infer the receiver type of `.{i}`; add an annotation"))),
                    other => return Err(Diagnostic::new(e.span, format!("cannot index `{other}` with `.{i}`"))),
                }
            }
            ExprKind::Ref(m, x) => {
                let t = self.expr(x)?;
                if *m && self.is_place_expr(x) {
                    self.require_mutable(x, "borrow")?;
                }
                Type::r#ref(*m, t)
            }
            ExprKind::Deref(x) => {
                let t = self.expr(x)?;
                match self.inf.resolve(&t).as_ref() {
                    Some((_, inner)) => inner.clone(),
                    None => return Err(Diagnostic::new(e.span, format!("cannot dereference `{}`", self.inf.resolve(&t)))),
                }
            }
            ExprKind::Unary(UnOp::Neg, x) => {
                let t = self.expr(x)?;
                let t = self.value_of(x, &t);
                self.numeric(&t, x.span, false)?;
                t
            }
            ExprKind::Unary(UnOp::Not, x) => {
                let t = self.expr(x)?;
                let t = self.value_of(x, &t);
                self.inf.unify(&Type::con("Bool"), &t, x.span)?;
                Type::con("Bool")
            }
            ExprKind::Binary(op, a, b) => {
                let ta = self.expr(a)?;
                let tb = self.expr(b)?;
                match op {
                    BinOp::And | BinOp::Or => {
                        let ta = self.value_of(a, &ta);
                        let tb = self.value_of(b, &tb);
                        self.inf.unify(&Type::con("Bool"), &ta, a.span)?;
                        self.inf.unify(&Type::con("Bool"), &tb, b.span)?;
                        Type::con("Bool")
                    }
                    BinOp::Eq | BinOp::Ne => {
                        // Both sides are borrowed; references are seen through.
                        let pa = self.inf.resolve(&ta).peel().clone();
                        let pb = self.inf.resolve(&tb).peel().clone();
                        self.inf.unify(&pa, &pb, b.span)?;
                        self.pending.push((pa, "Eq".into(), e.span));
                        Type::con("Bool")
                    }
                    BinOp::Add => {
                        let pa = self.inf.resolve(&ta);
                        if pa.peel().head() == Some("String") {
                            let pb = self.inf.resolve(&tb).peel().clone();
                            self.inf.unify(&Type::con("String"), &pb, b.span)?;
                            Type::con("String")
                        } else {
                            let ta = self.value_of(a, &ta);
                            let tb = self.value_of(b, &tb);
                            self.inf.unify(&ta, &tb, b.span)?;
                            self.numeric(&ta, a.span, true)?;
                            ta
                        }
                    }
                    BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                        let ta = self.value_of(a, &ta);
                        let tb = self.value_of(b, &tb);
                        self.inf.unify(&ta, &tb, b.span)?;
                        self.numeric(&ta, a.span, false)?;
                        Type::con("Bool")
                    }
                    _ => {
                        let ta = self.value_of(a, &ta);
                        let tb = self.value_of(b, &tb);
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
                let ct = self.value_of(cond, &ct);
                self.inf.unify(&Type::con("Bool"), &ct, cond.span)?;
                let tt = self.block(then)?;
                let tt = self.block_value(then, &tt);
                match els {
                    Some(b) => {
                        let et = self.block(b)?;
                        let et = self.block_value(b, &et);
                        self.inf.unify(&tt, &et, last_span(b, b.span))?;
                    }
                    None => self.inf.unify(&Type::unit(), &tt, last_span(then, then.span))?,
                }
                tt
            }
            ExprKind::While { cond, body } => {
                let ct = self.expr(cond)?;
                let ct = self.value_of(cond, &ct);
                self.inf.unify(&Type::con("Bool"), &ct, cond.span)?;
                self.block(body)?;
                Type::unit()
            }
            ExprKind::Case { scrutinee, arms } => {
                let st = self.expr(scrutinee)?;
                let result = self.inf.fresh();
                for arm in arms {
                    let mut binds = Vec::new();
                    self.check_pat(&arm.pat, &st, None, arm.guard.is_some(), &mut binds)?;
                    let mut scope = HashMap::new();
                    for (name, ty, _) in binds {
                        scope.insert(name, (ty, false));
                    }
                    self.scopes.push(scope);
                    if let Some(g) = &arm.guard {
                        let gt = self.expr(g)?;
                        let gt = self.value_of(g, &gt);
                        self.inf.unify(&Type::con("Bool"), &gt, g.span)?;
                    }
                    let bt = self.block(&arm.body)?;
                    let bt = self.block_value(&arm.body, &bt);
                    self.inf.unify(&result, &bt, last_span(&arm.body, arm.span))?;
                    self.scopes.pop();
                }
                result
            }
            ExprKind::Interp(parts) => {
                for p in parts {
                    if let InterpPart::Expr(x) = p {
                        let t = self.expr(x)?;
                        let t = self.inf.resolve(&t).peel().clone();
                        self.pending.push((t, "Show".into(), x.span));
                    }
                }
                Type::con("String")
            }
            ExprKind::Assign(lhs, rhs) => {
                let lt = self.assign_target(lhs)?;
                let rt = self.expr(rhs)?;
                let rt = self.coerce(rhs, &rt, &lt)?;
                self.inf.unify(&lt, &rt, rhs.span)?;
                Type::unit()
            }
            ExprKind::Return(v) => {
                let vt = match v {
                    Some(x) => {
                        let t = self.expr(x)?;
                        let ret = self.ret_ty.clone();
                        self.coerce(x, &t, &ret)?
                    }
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
        self.assign_target_in(lhs, false)
    }

    /// `through_field` is true when a field or element of the target is assigned, which is
    /// allowed through a `&mut` reference held in an immutable variable.
    fn assign_target_in(&mut self, lhs: &Expr, through_field: bool) -> Result<Type, Diagnostic> {
        let t = match &lhs.kind {
            ExprKind::Var(name) => {
                let (lt, mutable) = match self.lookup(name) {
                    Some(v) => v,
                    None => return Err(Diagnostic::new(lhs.span, format!("unknown variable `{name}`"))),
                };
                let via_mut_ref = through_field && matches!(self.inf.resolve(&lt).as_ref(), Some((true, _)));
                if !mutable && !via_mut_ref {
                    return Err(Diagnostic::new(lhs.span, format!("cannot assign twice to immutable variable `{name}`")));
                }
                lt
            }
            ExprKind::Dot { recv, name, args: None } => {
                let rt = self.assign_target_in(recv, true)?;
                let rt = self.inf.resolve(&rt);
                if let Some((m, _)) = rt.as_ref() {
                    if !m {
                        return Err(Diagnostic::new(lhs.span, "cannot assign through a shared reference"));
                    }
                    self.info.adjust.insert(recv.id, Adjust::AutoDeref);
                }
                let (idx, fty) = self.field_of(rt.peel(), name, lhs.span)?;
                self.info.dots.insert(lhs.id, DotRes::Field(idx));
                fty
            }
            ExprKind::TupleIndex(recv, i) => {
                let rt = self.assign_target_in(recv, true)?;
                let rt = self.inf.resolve(&rt);
                if let Some((m, _)) = rt.as_ref() {
                    if !m {
                        return Err(Diagnostic::new(lhs.span, "cannot assign through a shared reference"));
                    }
                    self.info.adjust.insert(recv.id, Adjust::AutoDeref);
                }
                match rt.peel() {
                    Type::Con(n, items) if n == "Tuple" && *i < items.len() => items[*i].clone(),
                    other => return Err(Diagnostic::new(lhs.span, format!("cannot index `{other}` with `.{i}`"))),
                }
            }
            ExprKind::Deref(inner) => {
                let it = self.expr(inner)?;
                match self.inf.resolve(&it).as_ref() {
                    Some((true, t)) => t.clone(),
                    Some((false, _)) => return Err(Diagnostic::new(lhs.span, "cannot assign through a shared reference")),
                    None => return Err(Diagnostic::new(lhs.span, format!("cannot dereference `{}`", self.inf.resolve(&it)))),
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
            let expected = subst(fty, &map);
            let vt = self.coerce(value, &vt, &expected)?;
            self.inf.unify(&expected, &vt, value.span)?;
        }
        for (fname, _) in &decl {
            if !seen.contains(fname) {
                return Err(Diagnostic::new(e.span, format!("missing field `{fname}` in `{name}`")));
            }
        }
        Ok(ty)
    }

    /// Adjusts a receiver of type `rt` to the method's declared self type `self_param`.
    fn adjust_receiver(&mut self, recv: &Expr, rt: &Type, self_param: &Type, span: Span) -> Result<Type, Diagnostic> {
        let rt = self.inf.resolve(rt);
        let sp = self.inf.resolve(self_param);
        match (rt.as_ref(), sp.as_ref()) {
            (None, Some((m, _))) => {
                if m {
                    self.require_mutable(recv, "borrow")?;
                }
                self.info.adjust.insert(recv.id, Adjust::AutoRef(m));
                Ok(Type::r#ref(m, rt.clone()))
            }
            (Some((_, inner)), None) => {
                if !self.is_copy(inner) {
                    return Err(Diagnostic::new(span, format!("cannot move out of a reference to `{inner}`; use `.clone`")));
                }
                self.info.adjust.insert(recv.id, Adjust::AutoDeref);
                Ok(inner.clone())
            }
            (Some((false, _)), Some((true, _))) => Err(Diagnostic::new(span, "cannot borrow as mutable through a shared reference")),
            (Some((true, inner)), Some((false, _))) => Ok(Type::r#ref(false, inner.clone())),
            _ => Ok(rt.clone()),
        }
    }

    fn dot(&mut self, e: &Expr, recv: &Expr, name: &str, args: Option<&[Expr]>) -> Result<Type, Diagnostic> {
        // `Type.function(args)`.
        if let ExprKind::Var(tn) = &recv.kind {
            if self.lookup(tn).is_none() && !self.info.globals.contains_key(tn) && self.adts.contains_key(tn) {
                let hit = self.info.impls.iter().find(|i| i.trait_name.is_none() && i.self_ty.head() == Some(tn) && i.assoc.contains_key(name)).map(|i| i.assoc[name].clone());
                let Some(global) = hit else {
                    return Err(Diagnostic::new(e.span, format!("no associated function `{name}` on `{tn}`")));
                };
                let g = self.info.globals[&global].clone();
                let (ft, fresh) = self.instantiate(&g.scheme, HashMap::new(), e.span);
                self.info.dots.insert(e.id, DotRes::Assoc { global, targs: fresh });
                self.inst_spans.insert(e.id, e.span);
                return self.apply(ft, args.unwrap_or(&[]), name, e.span, 0);
            }
        }
        let rt = self.expr(recv)?;
        let rt = self.inf.resolve(&rt);
        let base = rt.peel().clone();
        if matches!(base, Type::Var(_)) {
            return Err(Diagnostic::new(e.span, format!("cannot infer the receiver type of `.{name}`; add an annotation")));
        }
        // Field access.
        if args.is_none() {
            if let Type::Con(head, _) = &base {
                if self.info.structs.get(head).map_or(false, |s| s.fields.iter().any(|(f, _)| f == name)) {
                    let (idx, fty) = self.field_of(&base, name, e.span)?;
                    if rt.as_ref().is_some() {
                        self.info.adjust.insert(recv.id, Adjust::AutoDeref);
                    }
                    self.info.dots.insert(e.id, DotRes::Field(idx));
                    return Ok(fty);
                }
            }
        }
        // Inherent methods.
        if let Type::Con(head, _) = &base {
            let hit = self.info.impls.iter().find(|i| i.trait_name.is_none() && i.self_ty.head() == Some(head) && i.methods.contains_key(name)).map(|i| i.methods[name].clone());
            if let Some(global) = hit {
                let g = self.info.globals[&global].clone();
                let (ft, fresh) = self.instantiate(&g.scheme, HashMap::new(), e.span);
                let Type::Fn(self_param, rest) = ft else { unreachable!("methods take self") };
                let adjusted = self.adjust_receiver(recv, &rt, &self_param, e.span)?;
                self.inf.unify(&self_param, &adjusted, recv.span)?;
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
            let applicable = match &base {
                Type::Param(p) => self.bounds_of(p).contains(&tn),
                _ => self.info.impls.iter().any(|i| {
                    i.trait_name.as_deref() == Some(&tn) && (matches!(i.self_ty, Type::Param(_)) || i.self_ty.head() == base.head())
                }),
            };
            if applicable {
                candidates.push(tn);
            }
        }
        candidates.sort();
        let tn = match candidates.len() {
            0 => {
                if let (Type::Param(p), Some(tn)) = (&base, with_method.first()) {
                    return Err(Diagnostic::new(e.span, format!("`{p}` is not bounded by `{tn}`; add `{p}: {tn}`")));
                }
                return Err(Diagnostic::new(e.span, format!("no field or method `{name}` on type `{base}`")));
            }
            1 => candidates.pop().unwrap(),
            _ => {
                return Err(Diagnostic::new(
                    e.span,
                    format!("ambiguous method `{name}` on type `{base}`: candidates `{}`", candidates.join("`, `")),
                ))
            }
        };
        let sig = self.info.traits[&tn].methods[name].clone();
        let mut fixed = HashMap::new();
        fixed.insert("Self".to_string(), base.clone());
        let (ft, _) = self.instantiate(&sig.scheme, fixed, e.span);
        let Type::Fn(self_param, rest) = ft else { unreachable!("trait methods take self") };
        let adjusted = self.adjust_receiver(recv, &rt, &self_param, e.span)?;
        self.inf.unify(&self_param, &adjusted, recv.span)?;
        self.info.dots.insert(e.id, DotRes::Method(MethodRes::Trait { trait_name: tn, method: name.to_string(), self_ty: base }));
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

    /// Records a binding of `ty`. Under `by_ref`, the binding is a reference to the matched place.
    fn bind(&mut self, pat: &Pattern, name: &str, ty: &Type, by_ref: Option<bool>, guarded: bool, binds: &mut Vec<(String, Type, Span)>) -> Result<(), Diagnostic> {
        if binds.iter().any(|(b, _, _)| b == name) {
            return Err(Diagnostic::new(pat.span, format!("`{name}` is bound more than once in this pattern")));
        }
        let bound_ty = match by_ref {
            Some(m) => {
                self.info.pat_by_ref.insert(pat.id, m);
                Type::r#ref(m, ty.clone())
            }
            None => {
                self.bind_records.push(BindRecord { pat: pat.id, span: pat.span, guarded, copy_params: self.copy_params() });
                ty.clone()
            }
        };
        self.info.pat_types.insert(pat.id, bound_ty.clone());
        binds.push((name.to_string(), bound_ty, pat.span));
        Ok(())
    }

    fn check_pat(&mut self, pat: &Pattern, expected: &Type, by_ref: Option<bool>, guarded: bool, binds: &mut Vec<(String, Type, Span)>) -> Result<(), Diagnostic> {
        // Match ergonomics: a constructor pattern against a reference matches the pointee
        // and binds by reference.
        let resolved = self.inf.resolve(expected);
        if let Some((m, inner)) = resolved.as_ref() {
            if !matches!(pat.kind, PatKind::Wild | PatKind::Bind(_)) {
                self.info.pat_deref.insert(pat.id);
                let mode = Some(by_ref.map_or(m, |outer| outer && m));
                return self.check_pat(pat, inner, mode, guarded, binds);
            }
        }
        self.info.pat_types.insert(pat.id, expected.clone());
        match &pat.kind {
            PatKind::Wild => Ok(()),
            PatKind::Bind(n) => self.bind(pat, n, expected, by_ref, guarded, binds),
            PatKind::Lit(l) => self.inf.unify(expected, &lit_type(l), pat.span),
            PatKind::Tuple(ps) => {
                let fresh: Vec<Type> = ps.iter().map(|_| self.inf.fresh()).collect();
                self.inf.unify(expected, &Type::tuple(fresh.clone()), pat.span)?;
                for (p, t) in ps.iter().zip(&fresh) {
                    self.check_pat(p, t, by_ref, guarded, binds)?;
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
                    self.check_pat(p, &subst(ft, &map), by_ref, guarded, binds)?;
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
                    self.check_pat(p, &subst(fty, &map), by_ref, guarded, binds)?;
                }
                Ok(())
            }
            PatKind::Or(alts) => {
                let mut first: Option<Vec<(String, Type, Span)>> = None;
                for alt in alts {
                    let mut b = Vec::new();
                    self.check_pat(alt, expected, by_ref, guarded, &mut b)?;
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
                self.bind(pat, n, expected, by_ref, guarded, binds)?;
                self.check_pat(inner, expected, by_ref, guarded, binds)
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
        ExprKind::TupleIndex(r, _) | ExprKind::Ref(_, r) | ExprKind::Deref(r) | ExprKind::Unary(_, r) => collect_refs(r, out),
        ExprKind::Binary(_, a, b) | ExprKind::Assign(a, b) | ExprKind::Range(a, b, _) => {
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
        ExprKind::TupleIndex(r, _) | ExprKind::Ref(_, r) | ExprKind::Deref(r) | ExprKind::Unary(_, r) => collect_cases(r, out),
        ExprKind::Binary(_, a, b) | ExprKind::Assign(a, b) | ExprKind::Range(a, b, _) => {
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
        crate::derive::expand(&mut p, &mut id)?;
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
    const PERSON: &str = "struct Person\n  derive Show, Eq, Clone\n  name: String\n  age: Int\nend\n";

    #[test]
    fn plan1_basics_still_hold() {
        assert_eq!(scheme("def fib(n: Int) -> Int\n  if n < 2\n    n\n  else\n    fib(n - 1) + fib(n - 2)\n  end\nend\ndef main\n  puts(int_to_s(fib(5)))\nend\n", "fib"), "[] [] Int -> Int");
        assert_eq!(scheme("def inc(x)\n  x + 1\nend\ndef main\n  inc(2)\n  ()\nend\n", "inc"), "[] [] Int -> Int");
        assert_eq!(err("def main\n  let x = 1 + true\nend\n"), "type mismatch: expected Int, found Bool");
        assert_eq!(err("def main\n  let x = 1\n  x = 2\nend\n"), "cannot assign twice to immutable variable `x`");
        assert_eq!(err("def main\n  puts(\"a\", \"b\")\nend\n"), "too many arguments: `puts` takes 1");
        assert_eq!(err("def f\n  1\nend\n"), "no `main` function defined");
        assert_eq!(scheme("def f(x)\n  1\nend\ndef main\n  ()\nend\n", "f"), "[T0] [] T0 -> Int");
    }

    #[test]
    fn struct_literal_field_access_and_inherent_method() {
        let src = format!("{POINT}impl Point\n  def swap(&self) -> Point\n    Point {{ x: self.y, y: self.x }}\n  end\nend\ndef main\n  let p = Point {{ x: 1.0, y: 2.0 }}\n  let q = p.swap\n  let f = q.x + 1.0\n  ()\nend\n");
        let info = check_src(&src).unwrap();
        assert_eq!(global(&info, "Point#*::swap").scheme.ty.to_string(), "&Point -> Point");
        assert!(info.dots.values().any(|d| matches!(d, DotRes::Field(1))));
        assert!(info.dots.values().any(|d| matches!(d, DotRes::Method(MethodRes::Direct { global, .. }) if global.ends_with("::swap"))));
        assert!(info.adjust.values().any(|a| matches!(a, Adjust::AutoRef(false))));
        assert!(info.adjust.values().any(|a| matches!(a, Adjust::AutoDeref)));
    }

    #[test]
    fn generic_struct_infers_type_args() {
        let src = "struct Pair[A, B]\n  first: A\n  second: B\nend\ndef main\n  let p = Pair { first: 1, second: \"a\" }\n  let s = p.first\n  ()\nend\n";
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
        let src = "def main\n  let t = (1, \"a\", true)\n  let n = t.0 + 1\n  let (a, b, c) = t\n  let s = b + \"x\"\n  ()\nend\n";
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
    }

    #[test]
    fn inferred_bounds_from_callee() {
        let src = "def show2[T: Show](x: &T) -> String\n  x.to_s + x.to_s\nend\ndef f(x)\n  show2(&x)\nend\ndef main\n  f(1)\n  ()\nend\n";
        assert_eq!(scheme(src, "f"), "[T0] [T0: Show] T0 -> String");
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
        let ok = format!("{POINT}impl Eq for Point\n  def eq(&self, other: &Point)\n    self.x == other.x\n  end\nend\ndef main\n  let b = Point {{ x: 1.0, y: 2.0 }} == Point {{ x: 1.0, y: 2.0 }}\nend\n");
        check_src(&ok).unwrap();
    }

    #[test]
    fn default_method_and_self_in_trait_body() {
        let src = "trait Area\n  def area(&self) -> Float\n  def describe(&self) -> String\n    \"area #{self.area}\"\n  end\nend\nstruct Sq\n  s: Float\nend\nimpl Area for Sq\n  def area(&self)\n    self.s * self.s\n  end\nend\ndef main\n  puts(Sq { s: 2.0 }.describe)\nend\n";
        let info = check_src(src).unwrap();
        assert_eq!(info.globals["Area::describe"].scheme.ty.to_string(), "&Self -> String");
        assert_eq!(global(&info, "Area#*::area").scheme.ty.to_string(), "&Sq -> Float");
    }

    #[test]
    fn field_assignment_requires_mutable_root() {
        assert_eq!(err(&format!("{POINT}def main\n  let p = Point {{ x: 1.0, y: 2.0 }}\n  p.x = 3.0\nend\n")), "cannot assign twice to immutable variable `p`");
        check_src(&format!("{POINT}def main\n  let mut p = Point {{ x: 1.0, y: 2.0 }}\n  p.x = 3.0\n  p.y += 1.0\nend\n")).unwrap();
    }

    // ----- Plan 3a -----

    #[test]
    fn reference_types_and_copy_auto_deref() {
        let src = "def add(a: &Int, b: &Int) -> Int\n  a + b\nend\ndef main\n  let x = 1\n  let r = &x\n  let y = add(&x, r) + *r\n  ()\nend\n";
        let info = check_src(src).unwrap();
        assert_eq!(info.globals["add"].scheme.ty.to_string(), "&Int -> &Int -> Int");
        assert!(info.derefs.len() >= 2);
    }

    #[test]
    fn named_place_needs_explicit_borrow_but_rvalues_auto_borrow() {
        assert_eq!(err("def main\n  let s = \"a\"\n  puts(s)\nend\n"), "expected `&String`, found `String`; write `&s`");
        let info = check_src("def main\n  let s = \"a\"\n  puts(&s)\n  puts(\"b\")\n  puts(int_to_s(1))\nend\n").unwrap();
        assert_eq!(info.autorefs.len(), 2);
    }

    #[test]
    fn non_copy_reference_as_value_needs_clone() {
        assert_eq!(err("def id(s: String) -> String\n  s\nend\ndef main\n  let s = \"a\"\n  let r = &s\n  let t = id(r)\nend\n"), "expected `String`, found `&String`; use `.clone`");
        check_src("def id(s: String) -> String\n  s\nend\ndef main\n  let s = \"a\"\n  let r = &s\n  let t = id(r.clone)\nend\n").unwrap();
    }

    #[test]
    fn mut_self_requires_mutable_receiver() {
        let src = format!("{PERSON}impl Person\n  def birthday(&mut self)\n    @age += 1\n  end\nend\ndef main\n  let p = Person {{ name: \"a\", age: 1 }}\n  p.birthday\nend\n");
        assert_eq!(err(&src), "cannot borrow `p` as mutable; it is not declared `mut`");
        let ok = src.replace("let p", "let mut p");
        let info = check_src(&ok).unwrap();
        assert!(info.adjust.values().any(|a| matches!(a, Adjust::AutoRef(true))));
    }

    #[test]
    fn associated_functions_and_gc() {
        let src = format!("{PERSON}impl Person\n  def anonymous(age: Int) -> Person\n    Person {{ name: \"anon\", age: age }}\n  end\nend\ndef main\n  let g = Gc.new(Person.anonymous(5))\n  let g2 = g\n  let n = g.borrow.age + g2.borrow_mut.age\n  ()\nend\n");
        let info = check_src(&src).unwrap();
        assert!(info.dots.values().any(|d| matches!(d, DotRes::Assoc { global, .. } if global == "Gc::new")));
        assert!(info.dots.values().any(|d| matches!(d, DotRes::Assoc { global, .. } if global.ends_with("::anonymous"))));
        let mut types: Vec<String> = info.expr_types.values().map(|t| t.to_string()).collect();
        types.sort();
        types.dedup();
        assert!(types.contains(&"Gc[Person]".to_string()), "{types:?}");
        assert!(types.contains(&"&Person".to_string()) && types.contains(&"&mut Person".to_string()), "{types:?}");
        assert_eq!(err("def main\n  Gc.make(1)\nend\n"), "no associated function `make` on `Gc`");
    }

    #[test]
    fn match_ergonomics_bind_by_reference() {
        let src = "enum S\n  C(Float)\n  R(String, Float)\nend\ndef f(s: &S) -> Float\n  case s\n  in C(r) then r * r\n  in R(name, h) then h + 1.0\n  end\nend\ndef main\n  ()\nend\n";
        let info = check_src(src).unwrap();
        assert!(info.pat_by_ref.values().all(|m| !m));
        assert!(info.pat_deref.len() >= 2);
        // The prelude contributes generic bindings; user code binds these three.
        let mut bound: Vec<String> = info.pat_by_ref.keys().map(|id| info.pat_types[id].clone()).filter(|t| !t.has_param()).map(|t| t.to_string()).collect();
        bound.sort();
        assert_eq!(bound, vec!["&Float", "&Float", "&String"]);
        assert!(info.pat_moves.iter().all(|id| info.pat_types[id].has_param()));
    }

    #[test]
    fn by_value_bindings_move_and_guards_reject_moves() {
        let src = "def main\n  let t = (1, \"a\")\n  let (n, s) = t\n  ()\nend\n";
        let info = check_src(src).unwrap();
        let user_moves: Vec<String> = info.pat_moves.iter().map(|id| info.pat_types[id].clone()).filter(|t| !t.has_param()).map(|t| t.to_string()).collect();
        assert_eq!(user_moves, vec!["String"]);
        let guarded = "def main\n  case (1, \"a\")\n  in (n, s) if n > 0 then ()\n  in (_, _) then ()\n  end\nend\n";
        assert_eq!(err(guarded), "cannot move out of a pattern binding in an arm with a guard; match on a reference");
    }

    #[test]
    fn derive_copy_requires_copy_fields_and_copy_types_are_copy() {
        assert_eq!(err(&format!("struct Person\n  derive Copy\n  name: String\nend\ndef main\n  ()\nend\n")), "cannot derive `Copy` for `Person`: field `name` is not `Copy`");
        let info = check_src("struct Pt\n  derive Copy\n  x: Float\nend\ndef main\n  let a = Pt { x: 1.0 }\n  let b = a\n  let c = a\n  ()\nend\n").unwrap();
        assert!(info.is_copy(&Type::con("Pt"), &|_| false));
        assert!(!info.is_copy(&Type::con("String"), &|_| false));
        assert!(info.is_copy(&Type::Con("Gc".into(), vec![Type::con("String")]), &|_| false));
    }

    #[test]
    fn borrowing_types_and_mut_refs_are_not_copy() {
        let info = check_src("struct Words\n  first: &String\n  rest: &String\nend\nstruct Box[T]\n  v: T\nend\ndef main\n  ()\nend\n").unwrap();
        assert!(info.contains_ref(&Type::con("Words")));
        assert!(info.contains_ref(&Type::Con("Option".into(), vec![Type::r#ref(false, Type::con("Int"))])));
        assert!(info.contains_ref(&Type::Con("Box".into(), vec![Type::r#ref(false, Type::con("Int"))])));
        assert!(!info.contains_ref(&Type::Con("Box".into(), vec![Type::con("Int")])));
        assert!(!info.contains_ref(&Type::Con("Gc".into(), vec![Type::con("String")])));
        assert!(info.is_copy(&Type::r#ref(false, Type::con("String")), &|_| false));
        assert!(!info.is_copy(&Type::r#ref(true, Type::con("Int")), &|_| false));
    }

    #[test]
    fn elision_picks_self_or_the_single_reference_parameter() {
        let info = check_src(&format!("{PERSON}impl Person\n  def name_ref(&self, other: &String) -> &String\n    &@name\n  end\nend\nstruct Words\n  first: &String\nend\ndef pick(n: Int, s: &String) -> Words\n  Words {{ first: s }}\nend\ndef first(s: &String)\n  s\nend\ndef main\n  ()\nend\n")).unwrap();
        let method = info.impls.iter().find_map(|i| i.methods.get("name_ref")).unwrap();
        assert_eq!(info.elided.get(method), Some(&0));
        assert_eq!(info.elided.get("pick"), Some(&1));
        assert_eq!(info.elided.get("first"), Some(&0), "inferred return types are elided too");
        let msg = "cannot infer the lifetime of the returned reference; return an owned value instead";
        assert_eq!(err("def f(a: &String, b: &String) -> &String\n  a\nend\ndef main\n  ()\nend\n"), msg);
        assert_eq!(err("def f -> &String\n  let s = int_to_s(1)\n  &s\nend\ndef main\n  ()\nend\n"), msg);
    }

    #[test]
    fn derived_impls_typecheck() {
        let src = format!("{PERSON}enum S\n  derive Show, Eq, Clone\n  C(Float)\n  R {{ w: Float, h: String }}\n  E\nend\ndef main\n  let p = Person {{ name: \"a\", age: 1 }}\n  let q = p.clone\n  puts(\"#{{p == q}} #{{p}} #{{R {{ w: 1.0, h: \"x\" }}}} #{{C(1.0) == E}}\")\nend\n");
        check_src(&src).unwrap();
    }

    #[test]
    fn symbols_and_ranges() {
        let info = check_src("def main
  let s = :a
  let r = 1..3
  ()
end
").unwrap();
        let types: Vec<String> = info.expr_types.values().map(|t| t.to_string()).collect();
        assert!(types.iter().any(|t| t == "Symbol"), "{types:?}");
        assert!(types.iter().any(|t| t == "Range[Int]"), "{types:?}");
        assert_eq!(err("def main
  let r = 1..\"a\"
end
"), "type mismatch: expected Int, found String");
        assert!(err("def main
  case :a
  in :a then 1
  in :b then 2
  end
  ()
end
").starts_with("non-exhaustive `case`"));
    }
}
