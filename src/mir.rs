//! Mid-level IR: a control-flow graph per function body, and lowering from the typed AST.

use std::collections::HashMap;
use std::fmt::Write;

use crate::ast::*;
use crate::diag::Diagnostic;
use crate::types::{DotRes, GlobalKind, MethodRes, Type, TypeInfo};

pub type LocalId = u32;
pub type BlockId = u32;

#[derive(Debug, Clone, PartialEq)]
pub struct Local {
    pub name: String,
    pub ty: Type,
}

/// `locals[0]` is the return slot, `locals[1..=n_params]` are the parameters, `blocks[0]` is the entry.
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
pub enum Proj {
    Field(usize),
    /// `(variant index, field index)`
    Downcast(usize, usize),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Place {
    pub local: LocalId,
    pub proj: Vec<Proj>,
}

impl Place {
    pub fn local(id: LocalId) -> Place {
        Place { local: id, proj: vec![] }
    }
    pub fn field(&self, i: usize) -> Place {
        let mut p = self.clone();
        p.proj.push(Proj::Field(i));
        p
    }
    pub fn downcast(&self, v: usize, i: usize) -> Place {
        let mut p = self.clone();
        p.proj.push(Proj::Downcast(v, i));
        p
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Statement {
    Assign(Place, Rvalue),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Agg {
    Struct(Type),
    Tuple(Type),
    Variant(Type, usize),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Rvalue {
    Use(Operand),
    Binary(BinOp, Operand, Operand),
    Unary(UnOp, Operand),
    Call(Callee, Vec<Operand>),
    Aggregate(Agg, Vec<Operand>),
    Discriminant(Place),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Callee {
    Def { name: String, targs: Vec<Type> },
    Extern(String),
    Trait { trait_name: String, method: String, self_ty: Type },
}

#[derive(Debug, Clone, PartialEq)]
pub enum Operand {
    Place(Place),
    Const(Const),
}

impl Operand {
    pub fn local(id: LocalId) -> Operand {
        Operand::Place(Place::local(id))
    }
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

/// Lowers every user def, impl method, and trait default method.
pub fn lower(prog: &Program, info: &TypeInfo) -> Result<Vec<Body>, Diagnostic> {
    let mut out = Vec::new();
    for item in &prog.items {
        match item {
            Item::Def(d) => out.push(lower_def(&d.name, d, info)?),
            Item::Impl(imp) => {
                // Impls are numbered in source order, matching `info.impls`.
                let id = out_impl_index(prog, imp);
                for m in &imp.methods {
                    let global = info.impls[id].methods[&m.name].clone();
                    out.push(lower_def(&global, m, info)?);
                }
            }
            Item::Trait(t) => {
                for m in &t.methods {
                    if !m.body.stmts.is_empty() {
                        out.push(lower_def(&format!("{}::{}", t.name, m.name), m, info)?);
                    }
                }
            }
            _ => {}
        }
    }
    Ok(out)
}

fn out_impl_index(prog: &Program, target: &ImplDef) -> usize {
    prog.items.iter().filter_map(|i| if let Item::Impl(x) = i { Some(x) } else { None }).position(|x| std::ptr::eq(x, target)).unwrap()
}

struct Lowerer<'a> {
    body: Body,
    cur: BlockId,
    scopes: Vec<HashMap<String, LocalId>>,
    info: &'a TypeInfo,
}

fn lower_def(global: &str, d: &Def, info: &TypeInfo) -> Result<Body, Diagnostic> {
    let g = &info.globals[global];
    let (params, ret) = g.scheme.ty.uncurry_n(g.n_params);
    let mut l = Lowerer {
        body: Body {
            name: global.to_string(),
            locals: vec![Local { name: "_ret".into(), ty: ret }],
            n_params: params.len(),
            blocks: vec![BasicBlock { stmts: vec![], term: Terminator::Unreachable }],
        },
        cur: 0,
        scopes: vec![HashMap::new()],
        info,
    };
    let mut params = params.into_iter();
    if d.self_param.is_some() {
        let id = l.new_local("self", params.next().unwrap());
        l.scopes[0].insert("self".into(), id);
    }
    for (p, t) in d.params.iter().zip(params) {
        let id = l.new_local(&p.name, t);
        l.scopes[0].insert(p.name.clone(), id);
    }
    let v = l.block(&d.body)?;
    l.push(Statement::Assign(Place::local(0), Rvalue::Use(v)));
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
    fn assign(&mut self, target: LocalId, rv: Rvalue) {
        self.push(Statement::Assign(Place::local(target), rv));
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
    /// Evaluates into a fresh temp and returns it as an operand.
    fn eval_to_temp(&mut self, ty: Type, rv: Rvalue) -> Operand {
        let t = self.temp(ty);
        self.assign(t, rv);
        Operand::local(t)
    }
    /// Materializes an operand as a place (constants are stored in a temp).
    fn as_place(&mut self, op: Operand, ty: Type) -> Place {
        match op {
            Operand::Place(p) => p,
            c => {
                let t = self.temp(ty);
                self.assign(t, Rvalue::Use(c));
                Place::local(t)
            }
        }
    }

    fn block(&mut self, b: &Block) -> Result<Operand, Diagnostic> {
        self.scopes.push(HashMap::new());
        let mut last = Operand::Const(Const::Unit);
        for (i, s) in b.stmts.iter().enumerate() {
            match s {
                Stmt::Let { pat, init, .. } => {
                    let v = self.expr(init)?;
                    let ty = self.ty(init);
                    if let PatKind::Bind(name) = &pat.kind {
                        let id = self.new_local(name, ty);
                        self.assign(id, Rvalue::Use(v));
                        self.scopes.last_mut().unwrap().insert(name.clone(), id);
                    } else {
                        let place = self.as_place(v, ty);
                        self.bind_irrefutable(pat, &place);
                    }
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

    /// Binds the names of an irrefutable pattern to projections of `place`.
    fn bind_irrefutable(&mut self, pat: &Pattern, place: &Place) {
        let ty = self.info.pat_types[&pat.id].clone();
        match &pat.kind {
            PatKind::Wild | PatKind::Lit(_) => {}
            PatKind::Bind(name) => {
                let id = self.new_local(name, ty);
                self.assign(id, Rvalue::Use(Operand::Place(place.clone())));
                self.scopes.last_mut().unwrap().insert(name.clone(), id);
            }
            PatKind::At(name, inner) => {
                let id = self.new_local(name, ty);
                self.assign(id, Rvalue::Use(Operand::Place(place.clone())));
                self.scopes.last_mut().unwrap().insert(name.clone(), id);
                self.bind_irrefutable(inner, place);
            }
            PatKind::Tuple(ps) => {
                for (i, p) in ps.iter().enumerate() {
                    self.bind_irrefutable(p, &place.field(i));
                }
            }
            PatKind::Variant { name, fields } => {
                let (_, idx) = self.info.variant_names[name];
                for (i, p) in fields.iter().enumerate() {
                    self.bind_irrefutable(p, &place.downcast(idx, i));
                }
            }
            PatKind::Struct { name, fields } => {
                for (fname, p) in fields {
                    let sub = self.field_place(name, fname, place);
                    self.bind_irrefutable(p, &sub);
                }
            }
            PatKind::Or(alts) => self.bind_irrefutable(&alts[0], place),
        }
    }

    /// Place of named field `fname` of struct or named-variant `name`.
    fn field_place(&self, name: &str, fname: &str, place: &Place) -> Place {
        if let Some(s) = self.info.structs.get(name) {
            let i = s.fields.iter().position(|(f, _)| f == fname).unwrap();
            return place.field(i);
        }
        let (en, idx) = &self.info.variant_names[name];
        let v = &self.info.enums[en].variants[*idx];
        let i = v.fields.iter().position(|(f, _)| f.as_deref() == Some(fname)).unwrap();
        place.downcast(*idx, i)
    }

    fn callee_for_global(&self, e: &Expr, name: &str) -> Callee {
        let g = &self.info.globals[name];
        match g.kind {
            GlobalKind::Extern => Callee::Extern(name.to_string()),
            _ => Callee::Def { name: name.to_string(), targs: self.info.insts.get(&e.id).cloned().unwrap_or_default() },
        }
    }

    fn expr(&mut self, e: &Expr) -> Result<Operand, Diagnostic> {
        Ok(match &e.kind {
            ExprKind::Int(v) => Operand::Const(Const::Int(*v)),
            ExprKind::Float(v) => Operand::Const(Const::Float(*v)),
            ExprKind::Str(s) => Operand::Const(Const::Str(s.clone())),
            ExprKind::Bool(b) => Operand::Const(Const::Bool(*b)),
            ExprKind::Unit => Operand::Const(Const::Unit),
            ExprKind::Var(n) => match self.lookup(n) {
                Some(id) => Operand::local(id),
                None => {
                    let g = &self.info.globals[n];
                    if g.n_params != 0 {
                        return Err(Diagnostic::new(e.span, "functions as values are not supported in this version"));
                    }
                    let ty = self.ty(e);
                    if let GlobalKind::Variant { index, .. } = g.kind {
                        return Ok(self.eval_to_temp(ty.clone(), Rvalue::Aggregate(Agg::Variant(ty, index), vec![])));
                    }
                    let callee = self.callee_for_global(e, n);
                    self.eval_to_temp(ty, Rvalue::Call(callee, vec![]))
                }
            },
            ExprKind::Tuple(items) => {
                let mut ops = Vec::new();
                for i in items {
                    ops.push(self.expr(i)?);
                }
                let ty = self.ty(e);
                self.eval_to_temp(ty.clone(), Rvalue::Aggregate(Agg::Tuple(ty), ops))
            }
            ExprKind::StructLit { name, fields } => {
                let ty = self.ty(e);
                // Evaluate in source order, then reorder to declaration order.
                let mut by_name: HashMap<&str, Operand> = HashMap::new();
                for (fname, value) in fields {
                    let v = self.expr(value)?;
                    by_name.insert(fname, v);
                }
                if let Some(s) = self.info.structs.get(name) {
                    let ops = s.fields.iter().map(|(f, _)| by_name.remove(f.as_str()).unwrap()).collect();
                    self.eval_to_temp(ty.clone(), Rvalue::Aggregate(Agg::Struct(ty), ops))
                } else {
                    let (en, idx) = &self.info.variant_names[name];
                    let v = &self.info.enums[en].variants[*idx];
                    let ops = v.fields.iter().map(|(f, _)| by_name.remove(f.as_deref().unwrap()).unwrap()).collect();
                    self.eval_to_temp(ty.clone(), Rvalue::Aggregate(Agg::Variant(ty, *idx), ops))
                }
            }
            ExprKind::Dot { recv, name, args } => {
                let rv = self.expr(recv)?;
                let rty = self.ty(recv);
                match self.info.dots[&e.id].clone() {
                    DotRes::Field(i) => {
                        let place = self.as_place(rv, rty);
                        Operand::Place(place.field(i))
                    }
                    DotRes::Method(m) => {
                        let (callee, n_params) = match m {
                            MethodRes::Direct { global, targs } => (Callee::Def { name: global.clone(), targs }, self.info.globals[&global].n_params),
                            MethodRes::Trait { trait_name, method, self_ty } => {
                                let n = self.info.traits[&trait_name].methods[&method].n_params;
                                (Callee::Trait { trait_name, method, self_ty }, n)
                            }
                        };
                        let args = args.as_deref().unwrap_or(&[]);
                        if args.len() + 1 != n_params {
                            let msg = if args.len() + 1 < n_params { "partial application is not supported in this version" } else { "too many arguments" };
                            return Err(Diagnostic::new(e.span, msg));
                        }
                        let mut ops = vec![rv];
                        for a in args {
                            ops.push(self.expr(a)?);
                        }
                        let ty = self.ty(e);
                        self.eval_to_temp(ty, Rvalue::Call(callee, ops))
                    }
                }
            }
            ExprKind::TupleIndex(recv, i) => {
                let rv = self.expr(recv)?;
                let rty = self.ty(recv);
                let place = self.as_place(rv, rty);
                Operand::Place(place.field(*i))
            }
            ExprKind::Unary(op, x) => {
                let v = self.expr(x)?;
                let ty = self.ty(e);
                self.eval_to_temp(ty, Rvalue::Unary(*op, v))
            }
            ExprKind::Binary(op @ (BinOp::And | BinOp::Or), a, b) => {
                let t = self.temp(Type::con("Bool"));
                let va = self.expr(a)?;
                self.assign(t, Rvalue::Use(va));
                let rhs_bb = self.new_block();
                let join = self.new_block();
                let term = match op {
                    BinOp::And => Terminator::If(Operand::local(t), rhs_bb, join),
                    _ => Terminator::If(Operand::local(t), join, rhs_bb),
                };
                self.terminate(term);
                self.cur = rhs_bb;
                let vb = self.expr(b)?;
                self.assign(t, Rvalue::Use(vb));
                self.terminate(Terminator::Goto(join));
                self.cur = join;
                Operand::local(t)
            }
            ExprKind::Binary(op @ (BinOp::Eq | BinOp::Ne), a, b) if !self.ty(a).is_primitive() => {
                let va = self.expr(a)?;
                let vb = self.expr(b)?;
                let callee = Callee::Trait { trait_name: "Eq".into(), method: "eq".into(), self_ty: self.ty(a) };
                let eq = self.eval_to_temp(Type::con("Bool"), Rvalue::Call(callee, vec![va, vb]));
                match op {
                    BinOp::Eq => eq,
                    _ => self.eval_to_temp(Type::con("Bool"), Rvalue::Unary(UnOp::Not, eq)),
                }
            }
            ExprKind::Binary(op, a, b) => {
                let va = self.expr(a)?;
                let vb = self.expr(b)?;
                let ty = self.ty(e);
                self.eval_to_temp(ty, Rvalue::Binary(*op, va, vb))
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
                let mut ops = Vec::new();
                for a in args {
                    ops.push(self.expr(a)?);
                }
                let ty = self.ty(e);
                if let GlobalKind::Variant { index, .. } = g.kind {
                    return Ok(self.eval_to_temp(ty.clone(), Rvalue::Aggregate(Agg::Variant(ty, index), ops)));
                }
                let callee = self.callee_for_global(f, &name);
                self.eval_to_temp(ty, Rvalue::Call(callee, ops))
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
                self.assign(t, Rvalue::Use(v));
                self.terminate(Terminator::Goto(join));
                self.cur = else_bb;
                let v = match els {
                    Some(b) => self.block(b)?,
                    None => Operand::Const(Const::Unit),
                };
                self.assign(t, Rvalue::Use(v));
                self.terminate(Terminator::Goto(join));
                self.cur = join;
                Operand::local(t)
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
            ExprKind::Case { scrutinee, arms } => self.case(e, scrutinee, arms)?,
            ExprKind::Interp(parts) => {
                let mut acc: Option<Operand> = None;
                for part in parts {
                    let piece = match part {
                        InterpPart::Lit(s) => Operand::Const(Const::Str(s.clone())),
                        InterpPart::Expr(x) => {
                            let v = self.expr(x)?;
                            let ty = self.ty(x);
                            if ty.is_primitive() && ty.head() == Some("String") {
                                v
                            } else {
                                let callee = Callee::Trait { trait_name: "Show".into(), method: "to_s".into(), self_ty: ty };
                                self.eval_to_temp(Type::con("String"), Rvalue::Call(callee, vec![v]))
                            }
                        }
                    };
                    acc = Some(match acc {
                        None => piece,
                        Some(prev) => self.eval_to_temp(Type::con("String"), Rvalue::Call(Callee::Extern("str_concat".into()), vec![prev, piece])),
                    });
                }
                acc.unwrap_or(Operand::Const(Const::Str(String::new())))
            }
            ExprKind::Assign(lhs, rhs) => {
                let v = self.expr(rhs)?;
                let place = self.place_of(lhs)?;
                self.push(Statement::Assign(place, Rvalue::Use(v)));
                Operand::Const(Const::Unit)
            }
            ExprKind::Return(v) => {
                let val = match v {
                    Some(x) => self.expr(x)?,
                    None => Operand::Const(Const::Unit),
                };
                self.assign(0, Rvalue::Use(val));
                self.terminate(Terminator::Return);
                self.cur = self.new_block();
                Operand::Const(Const::Unit)
            }
        })
    }

    /// Place denoted by an assignment target (checked by the type checker).
    fn place_of(&mut self, lhs: &Expr) -> Result<Place, Diagnostic> {
        match &lhs.kind {
            ExprKind::Var(n) => Ok(Place::local(self.lookup(n).expect("checked local"))),
            ExprKind::Dot { recv, .. } => {
                let DotRes::Field(i) = self.info.dots[&lhs.id] else { unreachable!("checker allows only fields") };
                Ok(self.place_of(recv)?.field(i))
            }
            ExprKind::TupleIndex(recv, i) => Ok(self.place_of(recv)?.field(*i)),
            _ => unreachable!("checker rejects other targets"),
        }
    }

    fn case(&mut self, e: &Expr, scrutinee: &Expr, arms: &[Arm]) -> Result<Operand, Diagnostic> {
        let sv = self.expr(scrutinee)?;
        let sty = self.ty(scrutinee);
        let splace = self.as_place(sv, sty);
        let result = self.temp(self.ty(e));
        let join = self.new_block();
        let mut next_test = self.new_block();
        self.terminate(Terminator::Goto(next_test));
        for arm in arms {
            self.cur = next_test;
            next_test = self.new_block();
            self.scopes.push(HashMap::new());
            // Allocate one local per bound name, shared by or-alternatives.
            let mut names = Vec::new();
            collect_binders(&arm.pat, &mut names);
            let mut binds: HashMap<String, LocalId> = HashMap::new();
            for (name, pid) in names {
                let ty = self.info.pat_types[&pid].clone();
                let id = self.new_local(&name, ty);
                binds.insert(name.clone(), id);
                self.scopes.last_mut().unwrap().insert(name, id);
            }
            self.test_pat(&arm.pat, &splace, next_test, &binds);
            if let Some(g) = &arm.guard {
                let gv = self.expr(g)?;
                let body_bb = self.new_block();
                self.terminate(Terminator::If(gv, body_bb, next_test));
                self.cur = body_bb;
            }
            let v = self.block(&arm.body)?;
            self.assign(result, Rvalue::Use(v));
            self.terminate(Terminator::Goto(join));
            self.scopes.pop();
        }
        // Exhaustiveness guarantees the final failure block is dead.
        self.cur = next_test;
        self.terminate(Terminator::Unreachable);
        self.cur = join;
        Ok(Operand::local(result))
    }

    /// Emits tests for `pat` against `place`; on failure control goes to `fail`.
    /// On return, `self.cur` is the success block. Bound names are assigned into `binds`.
    fn test_pat(&mut self, pat: &Pattern, place: &Place, fail: BlockId, binds: &HashMap<String, LocalId>) {
        match &pat.kind {
            PatKind::Wild => {}
            PatKind::Bind(name) => {
                self.assign(binds[name], Rvalue::Use(Operand::Place(place.clone())));
            }
            PatKind::At(name, inner) => {
                self.assign(binds[name], Rvalue::Use(Operand::Place(place.clone())));
                self.test_pat(inner, place, fail, binds);
            }
            PatKind::Lit(l) => {
                let c = match l {
                    Lit::Int(v) => Const::Int(*v),
                    Lit::Float(v) => Const::Float(*v),
                    Lit::Str(s) => Const::Str(s.clone()),
                    Lit::Bool(b) => Const::Bool(*b),
                    Lit::Unit => return,
                };
                let ok = self.eval_to_temp(Type::con("Bool"), Rvalue::Binary(BinOp::Eq, Operand::Place(place.clone()), Operand::Const(c)));
                let next = self.new_block();
                self.terminate(Terminator::If(ok, next, fail));
                self.cur = next;
            }
            PatKind::Tuple(ps) => {
                for (i, p) in ps.iter().enumerate() {
                    self.test_pat(p, &place.field(i), fail, binds);
                }
            }
            PatKind::Variant { name, fields } => {
                let (en, idx) = self.info.variant_names[name].clone();
                if self.info.enums[&en].variants.len() > 1 {
                    let d = self.eval_to_temp(Type::con("Int"), Rvalue::Discriminant(place.clone()));
                    let ok = self.eval_to_temp(Type::con("Bool"), Rvalue::Binary(BinOp::Eq, d, Operand::Const(Const::Int(idx as i64))));
                    let next = self.new_block();
                    self.terminate(Terminator::If(ok, next, fail));
                    self.cur = next;
                }
                for (i, p) in fields.iter().enumerate() {
                    self.test_pat(p, &place.downcast(idx, i), fail, binds);
                }
            }
            PatKind::Struct { name, fields } => {
                if let Some((en, idx)) = self.info.variant_names.get(name).cloned() {
                    if self.info.enums[&en].variants.len() > 1 {
                        let d = self.eval_to_temp(Type::con("Int"), Rvalue::Discriminant(place.clone()));
                        let ok = self.eval_to_temp(Type::con("Bool"), Rvalue::Binary(BinOp::Eq, d, Operand::Const(Const::Int(idx as i64))));
                        let next = self.new_block();
                        self.terminate(Terminator::If(ok, next, fail));
                        self.cur = next;
                    }
                }
                for (fname, p) in fields {
                    let sub = self.field_place(name, fname, place);
                    self.test_pat(p, &sub, fail, binds);
                }
            }
            PatKind::Or(alts) => {
                let success = self.new_block();
                for (i, alt) in alts.iter().enumerate() {
                    let next_alt = if i + 1 < alts.len() { self.new_block() } else { fail };
                    self.test_pat(alt, place, next_alt, binds);
                    self.terminate(Terminator::Goto(success));
                    if i + 1 < alts.len() {
                        self.cur = next_alt;
                    }
                }
                self.cur = success;
            }
        }
    }
}

fn collect_binders(p: &Pattern, out: &mut Vec<(String, PatId)>) {
    match &p.kind {
        PatKind::Bind(n) => out.push((n.clone(), p.id)),
        PatKind::At(n, inner) => {
            out.push((n.clone(), p.id));
            collect_binders(inner, out);
        }
        PatKind::Tuple(ps) | PatKind::Variant { fields: ps, .. } => ps.iter().for_each(|q| collect_binders(q, out)),
        PatKind::Struct { fields, .. } => fields.iter().for_each(|(_, q)| collect_binders(q, out)),
        PatKind::Or(alts) => collect_binders(&alts[0], out),
        PatKind::Wild | PatKind::Lit(_) => {}
    }
}

// ----- printing -----

pub fn fmt_place(p: &Place) -> String {
    let mut s = format!("_{}", p.local);
    for pr in &p.proj {
        match pr {
            Proj::Field(i) => s = format!("{s}.{i}"),
            Proj::Downcast(v, i) => s = format!("({s} as {v}).{i}"),
        }
    }
    s
}

#[cfg_attr(not(test), allow(dead_code))]
fn fmt_operand(o: &Operand) -> String {
    match o {
        Operand::Place(p) => fmt_place(p),
        Operand::Const(Const::Int(v)) => v.to_string(),
        Operand::Const(Const::Float(v)) => format!("{v:?}"),
        Operand::Const(Const::Bool(v)) => v.to_string(),
        Operand::Const(Const::Str(s)) => format!("{s:?}"),
        Operand::Const(Const::Unit) => "()".to_string(),
    }
}

fn fmt_targs(targs: &[Type]) -> String {
    if targs.is_empty() {
        String::new()
    } else {
        format!("[{}]", targs.iter().map(|t| t.to_string()).collect::<Vec<_>>().join(", "))
    }
}

/// Human-readable MIR, used by tests and later by a `--dump-mir` flag.
#[cfg_attr(not(test), allow(dead_code))]
pub fn dump(b: &Body) -> String {
    let mut s = String::new();
    let params: Vec<String> = (1..=b.n_params).map(|i| format!("_{i}: {}", b.locals[i].ty)).collect();
    writeln!(s, "fn {}({}) -> {}", b.name, params.join(", "), b.locals[0].ty).unwrap();
    for (i, bb) in b.blocks.iter().enumerate() {
        writeln!(s, "bb{i}:").unwrap();
        for st in &bb.stmts {
            let Statement::Assign(place, rv) = st;
            let args = |ops: &[Operand]| ops.iter().map(fmt_operand).collect::<Vec<_>>().join(", ");
            let rhs = match rv {
                Rvalue::Use(o) => fmt_operand(o),
                Rvalue::Binary(op, a, c) => format!("{op:?} {} {}", fmt_operand(a), fmt_operand(c)),
                Rvalue::Unary(op, a) => format!("{op:?} {}", fmt_operand(a)),
                Rvalue::Call(callee, ops) => match callee {
                    Callee::Def { name, targs } => format!("call {name}{}({})", fmt_targs(targs), args(ops)),
                    Callee::Extern(n) => format!("call extern {n}({})", args(ops)),
                    Callee::Trait { trait_name, method, self_ty } => format!("call {trait_name}::{method}[{self_ty}]({})", args(ops)),
                },
                Rvalue::Aggregate(agg, ops) => match agg {
                    Agg::Struct(t) => format!("{t} {{ {} }}", args(ops)),
                    Agg::Tuple(_) => format!("({})", args(ops)),
                    Agg::Variant(t, i) => format!("{t}::{i}({})", args(ops)),
                },
                Rvalue::Discriminant(p) => format!("discr({})", fmt_place(p)),
            };
            writeln!(s, "  {} = {rhs}", fmt_place(place)).unwrap();
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::lex;
    use crate::parser::parse;
    use crate::types::check;

    fn lower_src(s: &str) -> Result<Vec<Body>, Diagnostic> {
        let prelude = include_str!("../std/prelude.rush");
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

    const MAIN: &str = "def main\n  ()\nend\n";

    #[test]
    fn straight_line() {
        assert_eq!(
            dump_fn(&format!("def add(a: Int, b: Int) -> Int\n  let c = a + b\n  c * 2\nend\n{MAIN}"), "add"),
            "fn add(_1: Int, _2: Int) -> Int\n\
             bb0:\n  _3 = Add _1 _2\n  _4 = _3\n  _5 = Mul _4 2\n  _0 = _5\n  return\n"
        );
    }

    #[test]
    fn if_expression_joins() {
        assert_eq!(
            dump_fn(&format!("def f(n: Int) -> Int\n  if n < 2\n    n\n  else\n    f(n - 1)\n  end\nend\n{MAIN}"), "f"),
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
            dump_fn(&format!("def f(a: Bool, b: Bool) -> Bool\n  a and b\nend\n{MAIN}"), "f"),
            "fn f(_1: Bool, _2: Bool) -> Bool\n\
             bb0:\n  _3 = _1\n  if _3 then bb1 else bb2\n\
             bb1:\n  _3 = _2\n  goto bb2\n\
             bb2:\n  _0 = _3\n  return\n"
        );
    }

    #[test]
    fn early_return_leaves_dead_block() {
        assert_eq!(
            dump_fn(&format!("def f(a: Int) -> Int\n  return a\n  0\nend\n{MAIN}"), "f"),
            "fn f(_1: Int) -> Int\n\
             bb0:\n  _0 = _1\n  return\n\
             bb1:\n  _0 = 0\n  return\n"
        );
    }

    #[test]
    fn partial_application_rejected_for_now() {
        let err = lower_src(&format!("def add(a: Int, b: Int) -> Int\n  a + b\nend\ndef main\n  add(1)\n  ()\nend\n")).unwrap_err();
        assert_eq!(err.msg, "partial application is not supported in this version");
    }

    #[test]
    fn function_value_rejected_for_now() {
        let err = lower_src("def add(a: Int, b: Int) -> Int\n  a + b\nend\ndef main\n  let f = add\n  ()\nend\n").unwrap_err();
        assert_eq!(err.msg, "functions as values are not supported in this version");
    }

    // ----- Plan 2 -----

    #[test]
    fn struct_literal_field_read_and_write() {
        assert_eq!(
            dump_fn("struct P\n  x: Int\n  y: Int\nend\ndef main\n  let mut p = P { y: 2, x: 1 }\n  p.x = p.y\n  ()\nend\n", "main"),
            "fn main() -> Unit\n\
             bb0:\n  _1 = P { 1, 2 }\n  _2 = _1\n  _2.0 = _2.1\n  _0 = ()\n  return\n"
        );
    }

    #[test]
    fn tuple_and_index_and_destructure() {
        assert_eq!(
            dump_fn("def main\n  let t = (1, true)\n  let (a, b) = t\n  let n = t.0 + a\n  ()\nend\n", "main"),
            "fn main() -> Unit\n\
             bb0:\n  _1 = (1, true)\n  _2 = _1\n  _3 = _2.0\n  _4 = _2.1\n  _5 = Add _2.0 _3\n  _6 = _5\n  _0 = ()\n  return\n"
        );
    }

    #[test]
    fn variant_construction_and_case() {
        assert_eq!(
            dump_fn(&format!("enum S\n  C(Float)\n  R(Float, Float)\nend\ndef area(s: S) -> Float\n  case s\n  in C(r) then r * r\n  in R(w, h) then w * h\n  end\nend\n{MAIN}"), "area"),
            "fn area(_1: S) -> Float\n\
             bb0:\n  goto bb2\n\
             bb1:\n  _0 = _2\n  return\n\
             bb2:\n  _4 = discr(_1)\n  _5 = Eq _4 0\n  if _5 then bb4 else bb3\n\
             bb3:\n  _9 = discr(_1)\n  _10 = Eq _9 1\n  if _10 then bb6 else bb5\n\
             bb4:\n  _3 = (_1 as 0).0\n  _6 = Mul _3 _3\n  _2 = _6\n  goto bb1\n\
             bb5:\n  unreachable\n\
             bb6:\n  _7 = (_1 as 1).0\n  _8 = (_1 as 1).1\n  _11 = Mul _7 _8\n  _2 = _11\n  goto bb1\n"
        );
        assert_eq!(
            dump_fn(&format!("enum S\n  C(Float)\n  R(Float, Float)\nend\ndef main\n  let s = R(1.0, 2.0)\n  let n = None\n  let m = Some(1)\n  n == m\n  ()\nend\n"), "main"),
            "fn main() -> Unit\n\
             bb0:\n  _1 = S::1(1.0, 2.0)\n  _2 = _1\n  _3 = Option[Int]::1()\n  _4 = _3\n  _5 = Option[Int]::0(1)\n  _6 = _5\n  _7 = call Eq::eq[Option[Int]](_4, _6)\n  _0 = ()\n  return\n"
        );
    }

    #[test]
    fn or_pattern_guard_and_literal() {
        assert_eq!(
            dump_fn(&format!("def f(n: Int) -> Int\n  case n\n  in 1 | 2 if n > 0 then 10\n  in x then x\n  end\nend\n{MAIN}"), "f"),
            "fn f(_1: Int) -> Int\n\
             bb0:\n  goto bb2\n\
             bb1:\n  _0 = _2\n  return\n\
             bb2:\n  _3 = Eq _1 1\n  if _3 then bb6 else bb5\n\
             bb3:\n  _6 = _1\n  _2 = _6\n  goto bb1\n\
             bb4:\n  _5 = Gt _1 0\n  if _5 then bb8 else bb3\n\
             bb5:\n  _4 = Eq _1 2\n  if _4 then bb7 else bb3\n\
             bb6:\n  goto bb4\n\
             bb7:\n  goto bb4\n\
             bb8:\n  _2 = 10\n  goto bb1\n\
             bb9:\n  unreachable\n"
        );
    }

    #[test]
    fn generic_call_records_targs_and_method_calls() {
        let src = "struct P\n  x: Int\nend\nimpl P\n  def get(&self) -> Int\n    self.x\n  end\nend\ndef id[T](x: T) -> T\n  x\nend\ndef main\n  let a = id(1)\n  let b = id(P { x: 2 }).get\n  let s = \"#{b} and #{\"x\"}\"\n  ()\nend\n";
        let d = dump_fn(src, "main");
        assert!(d.contains("_1 = call id[Int](1)"), "{d}");
        assert!(d.contains("call id[P](_3)"), "{d}");
        assert!(d.contains("::get(_4)"), "{d}");
        assert!(d.contains("call Show::to_s[Int](_6)"), "{d}");
        assert!(d.contains("call extern str_concat("), "{d}");
    }

    #[test]
    fn impl_methods_and_defaults_are_lowered() {
        let src = "trait A\n  def a(&self) -> Int\n  def b(&self) -> Int\n    self.a + 1\n  end\nend\nstruct S\n  f: Int\nend\nimpl A for S\n  def a(&self)\n    self.f\n  end\nend\ndef main\n  ()\nend\n";
        let bodies = lower_src(src).unwrap();
        let names: Vec<&str> = bodies.iter().map(|b| b.name.as_str()).collect();
        assert!(names.contains(&"A::b"), "{names:?}");
        assert!(names.iter().any(|n| n.starts_with("A#") && n.ends_with("::a")), "{names:?}");
        let d = dump(bodies.iter().find(|b| b.name == "A::b").unwrap());
        assert!(d.contains("call A::a[Self](_1)"), "{d}");
    }
}
