//! Mid-level IR: a control-flow graph per function body, and lowering from the typed AST.

use std::collections::HashMap;
use std::fmt::Write;

use crate::ast::*;
use crate::diag::{Diagnostic, Span};
use crate::types::{subst, Adjust, CaptureMode, ClosureInfo, DotRes, GlobalKind, MethodRes, Type, TypeInfo};

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
    /// A closure body's captured names, in environment order (`_1` is the environment).
    pub captures: Vec<String>,
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
    /// Through a reference or Gc handle.
    Deref,
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
    pub fn deref(&self) -> Place {
        let mut p = self.clone();
        p.proj.push(Proj::Deref);
        p
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Statement {
    Assign(Place, Rvalue, Span),
    /// Runs the drop glue of the value in the place (a no-op for types with nothing to free).
    Drop(Place, Span),
    /// The local's scope ends here: ownck drops it if still owned, borrowck ends its loans.
    StorageDead(LocalId, Span),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Agg {
    Struct(Type),
    Tuple(Type),
    Variant(Type, usize),
    /// A function value; the operands are its environment (captures or bound arguments).
    Fn { code: FnCode, alloc: Alloc },
}

#[derive(Debug, Clone, PartialEq)]
pub enum FnCode {
    /// Closure body `name`; the environment holds its captures.
    Closure { name: String, targs: Vec<Type> },
    /// A def, method, associated function, or trait method; the environment holds the first arguments.
    Global(Callee),
    /// A variant constructor of the enum type; the environment holds the first fields.
    Variant(Type, usize),
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Alloc {
    /// Nothing captured or bound: one static object.
    Static,
    /// A borrowing closure: the environment lives in the creating function's frame.
    Stack,
    /// On the GC heap.
    Heap,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Rvalue {
    Use(Operand),
    /// Moves a field out of a value being destructured by a pattern.
    MoveOut(Place),
    Ref(bool, Place),
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
    /// Calls the function value in the first operand (or behind it, for `&(A -> B)`) with the
    /// rest. Fewer arguments than its arity make a partial application.
    Value,
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
    Symbol(String),
    Unit,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Terminator {
    Goto(BlockId),
    If(Operand, BlockId, BlockId),
    Return,
    Unreachable,
}

/// Type of a place inside `body`.
pub fn place_type(info: &TypeInfo, body: &Body, p: &Place) -> Type {
    let mut ty = body.locals[p.local as usize].ty.clone();
    for pr in &p.proj {
        ty = match pr {
            Proj::Deref => match &ty {
                Type::Con(n, args) if n == "&" || n == "&mut" || n == "Gc" => args[0].clone(),
                other => panic!("place_type: deref of {other}"),
            },
            Proj::Field(i) => match &ty {
                Type::Con(n, items) if n == "Tuple" => items[*i].clone(),
                Type::Con(n, targs) => {
                    let s = &info.structs[n];
                    let map: HashMap<String, Type> = s.generics.iter().cloned().zip(targs.iter().cloned()).collect();
                    subst(&s.fields[*i].1, &map)
                }
                other => panic!("place_type: field of {other}"),
            },
            Proj::Downcast(v, i) => match &ty {
                Type::Con(n, targs) => {
                    let e = &info.enums[n];
                    let map: HashMap<String, Type> = e.generics.iter().cloned().zip(targs.iter().cloned()).collect();
                    subst(&e.variants[*v].fields[*i].1, &map)
                }
                other => panic!("place_type: downcast of {other}"),
            },
        };
    }
    ty
}

/// Emits a chain of blocks that replaces one original block (used by passes that insert
/// guarded statements).
pub(crate) struct Emit {
    pub chunks: Vec<(BlockId, Vec<Statement>, Terminator)>,
    pub cur_id: BlockId,
    pub cur: Vec<Statement>,
    pub next: BlockId,
}

impl Emit {
    pub fn alloc(&mut self) -> BlockId {
        let id = self.next;
        self.next += 1;
        id
    }
    /// `if flag then stmts`; continues in a fresh block.
    pub fn guarded(&mut self, flag: LocalId, stmts: Vec<Statement>) {
        let then_bb = self.alloc();
        let cont_bb = self.alloc();
        let before = std::mem::take(&mut self.cur);
        self.chunks.push((self.cur_id, before, Terminator::If(Operand::local(flag), then_bb, cont_bb)));
        self.chunks.push((then_bb, stmts, Terminator::Goto(cont_bb)));
        self.cur_id = cont_bb;
    }
    pub fn finish(mut self, term: Terminator) -> Vec<(BlockId, Vec<Statement>, Terminator)> {
        let stmts = std::mem::take(&mut self.cur);
        self.chunks.push((self.cur_id, stmts, term));
        self.chunks
    }
}

/// Source-like path of a place for messages: `p.name`, `t.0`, `*r`. Field access through a
/// reference is shown auto-dereferenced, as it is written.
pub fn describe_place(info: &TypeInfo, body: &Body, p: &Place) -> String {
    let mut s = body.locals[p.local as usize].name.clone();
    if s.is_empty() || s == "_ret" {
        s = "value".into();
    }
    let mut ty = body.locals[p.local as usize].ty.clone();
    for (i, pr) in p.proj.iter().enumerate() {
        let name = |fields: Option<&str>, k: usize| fields.map(str::to_string).unwrap_or(k.to_string());
        match pr {
            Proj::Deref if i + 1 == p.proj.len() => s = format!("*{s}"),
            Proj::Deref => {}
            Proj::Field(k) => {
                let f = match &ty {
                    Type::Con(n, _) => info.structs.get(n).map(|st| st.fields[*k].0.as_str()),
                    _ => None,
                };
                s = format!("{s}.{}", name(f, *k));
            }
            Proj::Downcast(v, k) => {
                let f = match &ty {
                    Type::Con(n, _) => info.enums.get(n).and_then(|e| e.variants[*v].fields[*k].0.as_deref()),
                    _ => None,
                };
                s = format!("{s}.{}", name(f, *k));
            }
        }
        ty = place_type(info, body, &Place { local: p.local, proj: p.proj[..=i].to_vec() });
    }
    s
}

/// Lowers every user def, impl method, and trait default method.
pub fn lower(prog: &Program, info: &TypeInfo) -> Result<Vec<Body>, Diagnostic> {
    let mut out = Vec::new();
    for item in &prog.items {
        match item {
            Item::Def(d) => out.extend(lower_def(&d.name, d, info)?),
            Item::Impl(imp) => {
                let id = impl_index(prog, imp, info);
                for m in &imp.methods {
                    let global = info.impls[id].methods.get(&m.name).or_else(|| info.impls[id].assoc.get(&m.name)).cloned().unwrap();
                    out.extend(lower_def(&global, m, info)?);
                }
            }
            Item::Trait(t) => {
                for m in &t.methods {
                    if !m.body.stmts.is_empty() {
                        out.extend(lower_def(&format!("{}::{}", t.name, m.name), m, info)?);
                    }
                }
            }
            _ => {}
        }
    }
    Ok(out)
}

/// Impls are numbered in source order after the built-in ones.
fn impl_index(prog: &Program, target: &ImplDef, info: &TypeInfo) -> usize {
    let builtin = info.impls.iter().take_while(|i| i.span == Span::default() && i.self_ty.is_gc()).count();
    builtin + prog.items.iter().filter_map(|i| if let Item::Impl(x) = i { Some(x) } else { None }).position(|x| std::ptr::eq(x, target)).unwrap()
}

struct Lowerer<'a> {
    body: Body,
    cur: BlockId,
    scopes: Vec<HashMap<String, LocalId>>,
    info: &'a TypeInfo,
    span: Span,
    copy_params: Vec<String>,
    /// Or-pattern -> local holding the index of the alternative that matched.
    or_sel: HashMap<PatId, LocalId>,
    /// Locals created in each open scope, in creation order; parallel to `scopes`.
    owned: Vec<Vec<LocalId>>,
    /// Enclosing loops, innermost last.
    loops: Vec<LoopCtx>,
    /// In a closure body: captured name -> its place through the environment `_1`.
    captured: HashMap<String, Place>,
    /// Closure bodies lowered so far.
    extra: Vec<Body>,
}

#[derive(Clone)]
struct LoopCtx {
    break_bb: BlockId,
    next_bb: BlockId,
    /// Receives `break e` in a `loop`.
    value: Option<LocalId>,
    /// `owned.len()` outside the loop: scopes at this depth and deeper end on `break`/`next`.
    depth: usize,
}

/// The body of `d` followed by the bodies of its closures.
fn lower_def(global: &str, d: &Def, info: &TypeInfo) -> Result<Vec<Body>, Diagnostic> {
    let g = &info.globals[global];
    let (params, ret) = g.scheme.ty.uncurry_n(g.n_params);
    let copy_params: Vec<String> = g.scheme.bounds.iter().filter(|(_, t)| info.trait_closure(t).iter().any(|x| x == "Copy")).map(|(p, _)| p.clone()).collect();
    let mut l = Lowerer {
        body: Body {
            name: global.to_string(),
            locals: vec![Local { name: "_ret".into(), ty: ret }],
            n_params: params.len(),
            blocks: vec![BasicBlock { stmts: vec![], term: Terminator::Unreachable }],
            captures: vec![],
        },
        cur: 0,
        scopes: vec![HashMap::new()],
        info,
        span: d.span,
        copy_params,
        or_sel: HashMap::new(),
        owned: vec![vec![]],
        loops: vec![],
        captured: HashMap::new(),
        extra: vec![],
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
    l.assign(0, Rvalue::Use(v));
    l.terminate(Terminator::Return);
    let mut out = vec![l.body];
    out.extend(l.extra);
    Ok(out)
}

impl<'a> Lowerer<'a> {
    fn new_local(&mut self, name: &str, ty: Type) -> LocalId {
        self.body.locals.push(Local { name: name.to_string(), ty });
        let id = self.body.locals.len() as LocalId - 1;
        self.owned.last_mut().unwrap().push(id);
        id
    }
    fn push_scope(&mut self) {
        self.scopes.push(HashMap::new());
        self.owned.push(vec![]);
    }
    /// Ends a scope: its locals die in reverse creation order, except the scope's value `v`,
    /// which is handed to the parent scope.
    fn pop_scope(&mut self, v: Operand) -> Operand {
        self.scopes.pop();
        let owned = self.owned.pop().unwrap();
        let v = self.detach(v, &owned);
        self.kill(&owned, &v);
        v
    }
    /// Makes a scope's value independent of the scope's locals: a plain temp moves to the
    /// parent scope; a named local or a projection is copied (or moved) into a parent temp.
    fn detach(&mut self, v: Operand, owned: &[LocalId]) -> Operand {
        let Operand::Place(p) = &v else { return v };
        if !owned.contains(&p.local) {
            return v;
        }
        if p.proj.is_empty() && self.body.locals[p.local as usize].name.is_empty() {
            self.owned.last_mut().unwrap().push(p.local);
            return v;
        }
        let ty = self.place_ty(p);
        self.eval_to_temp(ty, Rvalue::Use(v))
    }
    /// Emits `StorageDead` for `locals` in reverse order, skipping the local behind `keep`.
    fn kill(&mut self, locals: &[LocalId], keep: &Operand) {
        let keep = match keep {
            Operand::Place(p) if p.proj.is_empty() => Some(p.local),
            _ => None,
        };
        for &l in locals.iter().rev() {
            if Some(l) != keep {
                let span = self.span;
                self.push(Statement::StorageDead(l, span));
            }
        }
    }
    /// Ends every scope from `depth` inward, innermost first, before a jump out of them.
    fn exit_scopes(&mut self, depth: usize) {
        for i in (depth..self.owned.len()).rev() {
            let locals = self.owned[i].clone();
            self.kill(&locals, &Operand::Const(Const::Unit));
        }
    }
    /// A loop body's value is unused: its temp dies at the end of the body.
    fn discard(&mut self, v: Operand) {
        if let Operand::Place(p) = &v {
            let owned = self.owned.last_mut().unwrap();
            if p.proj.is_empty() && owned.last() == Some(&p.local) {
                owned.pop();
                self.kill(&[p.local], &Operand::Const(Const::Unit));
            }
        }
    }
    /// `for var in r` over a `Range[Int]`. The end test comes before the increment, so an
    /// inclusive range ending at the largest Int does not overflow.
    fn for_range(&mut self, var: &str, iter: &Expr, body: &Block) -> Result<(), Diagnostic> {
        let (int, bool_) = (Type::con("Int"), Type::con("Bool"));
        let it = self.expr(iter)?;
        let r = self.as_place(it, self.ty(iter));
        let i = self.eval_to_temp(int.clone(), Rvalue::Use(Operand::Place(r.field(0))));
        let stop = self.eval_to_temp(int.clone(), Rvalue::Use(Operand::Place(r.field(1))));
        let ex = self.eval_to_temp(bool_.clone(), Rvalue::Use(Operand::Place(r.field(2))));
        let (head, body_bb, step, inc, exit) = (self.new_block(), self.new_block(), self.new_block(), self.new_block(), self.new_block());
        self.terminate(Terminator::Goto(head));
        self.cur = head;
        let lt = self.eval_to_temp(bool_.clone(), Rvalue::Binary(BinOp::Lt, i.clone(), stop.clone()));
        let le = self.eval_to_temp(bool_.clone(), Rvalue::Binary(BinOp::Le, i.clone(), stop.clone()));
        let open = self.eval_to_temp(bool_.clone(), Rvalue::Binary(BinOp::And, ex.clone(), lt));
        let not_ex = self.eval_to_temp(bool_.clone(), Rvalue::Unary(UnOp::Not, ex.clone()));
        let closed = self.eval_to_temp(bool_.clone(), Rvalue::Binary(BinOp::And, not_ex, le));
        let go = self.eval_to_temp(bool_.clone(), Rvalue::Binary(BinOp::Or, open, closed));
        self.terminate(Terminator::If(go, body_bb, exit));
        self.cur = body_bb;
        self.loops.push(LoopCtx { break_bb: exit, next_bb: step, value: None, depth: self.owned.len() });
        self.push_scope();
        if var != "_" {
            let id = self.new_local(var, int.clone());
            self.assign(id, Rvalue::Use(i.clone()));
            self.scopes.last_mut().unwrap().insert(var.to_string(), id);
        }
        let v = self.block(body)?;
        self.discard(v);
        self.pop_scope(Operand::Const(Const::Unit));
        self.loops.pop();
        self.terminate(Terminator::Goto(step));
        self.cur = step;
        let at_stop = self.eval_to_temp(bool_.clone(), Rvalue::Binary(BinOp::Eq, i.clone(), stop));
        let not_ex = self.eval_to_temp(bool_.clone(), Rvalue::Unary(UnOp::Not, ex));
        let last = self.eval_to_temp(bool_, Rvalue::Binary(BinOp::And, not_ex, at_stop));
        self.terminate(Terminator::If(last, exit, inc));
        self.cur = inc;
        let Operand::Place(ip) = i.clone() else { unreachable!() };
        self.assign_place(ip, Rvalue::Binary(BinOp::Add, i, Operand::Const(Const::Int(1))));
        self.terminate(Terminator::Goto(head));
        self.cur = exit;
        Ok(())
    }
    /// A `&mut` place passed to a call is reborrowed (`&mut *r`) instead of moved.
    fn reborrow(&mut self, op: Operand, ty: &Type) -> Operand {
        match (&op, ty.as_ref()) {
            (Operand::Place(p), Some((true, inner))) if !p.proj.is_empty() || !self.body.locals[p.local as usize].name.is_empty() => {
                let t = Type::r#ref(true, inner.clone());
                let place = p.deref();
                self.eval_to_temp(t, Rvalue::Ref(true, place))
            }
            _ => op,
        }
    }
    /// Lowers a call argument, reborrowing `&mut` places.
    fn arg(&mut self, a: &Expr) -> Result<Operand, Diagnostic> {
        let v = self.expr(a)?;
        if self.info.derefs.contains(&a.id) || self.info.autorefs.contains_key(&a.id) {
            return Ok(v);
        }
        let ty = self.ty(a);
        Ok(self.reborrow(v, &ty))
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
    fn assign_place(&mut self, target: Place, rv: Rvalue) {
        let span = self.span;
        self.push(Statement::Assign(target, rv, span));
    }
    fn assign(&mut self, target: LocalId, rv: Rvalue) {
        self.assign_place(Place::local(target), rv);
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
    fn is_copy(&self, t: &Type) -> bool {
        let cps = &self.copy_params;
        self.info.is_copy(t, &|p| cps.iter().any(|c| c == p))
    }
    fn place_ty(&self, p: &Place) -> Type {
        place_type(self.info, &self.body, p)
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
    /// Borrows the value of an operand of type `ty` (references pass through).
    fn borrow(&mut self, op: Operand, ty: &Type, mutable: bool) -> Operand {
        if ty.as_ref().is_some() {
            return op;
        }
        let place = self.as_place(op, ty.clone());
        self.eval_to_temp(Type::r#ref(mutable, ty.clone()), Rvalue::Ref(mutable, place))
    }
    /// Reads the value behind an operand of type `ty` (references are dereferenced).
    fn value(&mut self, op: Operand, ty: &Type) -> Operand {
        if ty.as_ref().is_none() {
            return op;
        }
        let place = self.as_place(op, ty.clone());
        Operand::Place(place.deref())
    }

    fn block(&mut self, b: &Block) -> Result<Operand, Diagnostic> {
        self.push_scope();
        let mut last = Operand::Const(Const::Unit);
        for (i, s) in b.stmts.iter().enumerate() {
            match s {
                Stmt::Let { pat, init, span, .. } => {
                    let v = self.expr(init)?;
                    self.span = *span;
                    let ty = self.ty(init);
                    if let PatKind::Bind(name) = &pat.kind {
                        let id = self.new_local(name, ty);
                        self.assign(id, Rvalue::Use(v));
                        self.scopes.last_mut().unwrap().insert(name.clone(), id);
                    } else {
                        // Irrefutable: the failure block stays unreachable.
                        let place = self.as_place(v, ty);
                        let binds = self.declare_binders(pat);
                        let fail = self.new_block();
                        self.test_pat(pat, &place, fail);
                        self.bind_case(pat, &place, &binds);
                        self.drop_uncovered(pat, &place);
                    }
                    last = Operand::Const(Const::Unit);
                }
                Stmt::Expr(e) => {
                    let mark = self.owned.last().unwrap().len();
                    let v = self.expr(e)?;
                    if i + 1 == b.stmts.len() {
                        last = v;
                    } else {
                        // Temporaries of an expression statement die at its end.
                        self.span = e.span;
                        let temps = self.owned.last_mut().unwrap().split_off(mark);
                        self.kill(&temps, &Operand::Const(Const::Unit));
                        last = Operand::Const(Const::Unit);
                    }
                }
            }
        }
        self.span = b.span;
        Ok(self.pop_scope(last))
    }

    /// Allocates one local per bound name (shared by or-alternatives) in the current scope.
    fn declare_binders(&mut self, pat: &Pattern) -> HashMap<String, LocalId> {
        let mut names = Vec::new();
        collect_binders(pat, &mut names);
        let mut binds = HashMap::new();
        for (name, pid) in names {
            let ty = self.info.pat_types[&pid].clone();
            let id = self.new_local(&name, ty);
            binds.insert(name.clone(), id);
            self.scopes.last_mut().unwrap().insert(name, id);
        }
        binds
    }

    /// Assigns the bindings of a pattern whose tests (`test_pat`) already passed. Runs after all
    /// tests so that moving a binding out never precedes a read of the scrutinee.
    fn bind_case(&mut self, pat: &Pattern, place: &Place, binds: &HashMap<String, LocalId>) {
        let place = if self.info.pat_deref.contains(&pat.id) { place.deref() } else { place.clone() };
        match &pat.kind {
            PatKind::Wild | PatKind::Lit(_) => {}
            PatKind::Bind(name) => self.assign_binding(binds[name], pat, &place),
            PatKind::At(name, inner) => {
                self.assign_binding(binds[name], pat, &place);
                self.bind_case(inner, &place, binds);
            }
            PatKind::Tuple(ps) => {
                for (i, p) in ps.iter().enumerate() {
                    self.bind_case(p, &place.field(i), binds);
                }
            }
            PatKind::Variant { name, fields } => {
                let (_, idx) = self.info.variant_names[name];
                for (i, p) in fields.iter().enumerate() {
                    self.bind_case(p, &place.downcast(idx, i), binds);
                }
            }
            PatKind::Struct { name, fields } => {
                for (fname, p) in fields {
                    let sub = self.field_place(name, fname, &place);
                    self.bind_case(p, &sub, binds);
                }
            }
            PatKind::Or(alts) => self.on_alt(pat, alts.len(), &mut |this, i| this.bind_case(&alts[i], &place, binds)),
        }
    }

    /// Runs `f` for the alternative of or-pattern `pat` that `test_pat` recorded as matching.
    fn on_alt(&mut self, pat: &Pattern, n: usize, f: &mut dyn FnMut(&mut Self, usize)) {
        let sel = self.or_sel[&pat.id];
        let join = self.new_block();
        for i in 0..n {
            if i + 1 < n {
                let ok = self.eval_to_temp(Type::con("Bool"), Rvalue::Binary(BinOp::Eq, Operand::local(sel), Operand::Const(Const::Int(i as i64))));
                let (yes, no) = (self.new_block(), self.new_block());
                self.terminate(Terminator::If(ok, yes, no));
                self.cur = yes;
                f(self, i);
                self.terminate(Terminator::Goto(join));
                self.cur = no;
            } else {
                f(self, i);
                self.terminate(Terminator::Goto(join));
            }
        }
        self.cur = join;
    }

    fn assign_binding(&mut self, id: LocalId, pat: &Pattern, place: &Place) {
        let rv = if let Some(&m) = self.info.pat_by_ref.get(&pat.id) {
            Rvalue::Ref(m, place.clone())
        } else if self.info.pat_moves.contains(&pat.id) || !place.proj.is_empty() {
            // Field reads inside a pattern are `MoveOut` even for Copy fields, so a partially
            // moved scrutinee can still supply its other fields.
            Rvalue::MoveOut(place.clone())
        } else {
            Rvalue::Use(Operand::Place(place.clone()))
        };
        self.assign(id, rv);
    }

    fn pattern_moves(&self, pat: &Pattern) -> bool {
        match &pat.kind {
            PatKind::Bind(_) => self.info.pat_moves.contains(&pat.id),
            PatKind::At(_, inner) => self.info.pat_moves.contains(&pat.id) || self.pattern_moves(inner),
            PatKind::Tuple(ps) | PatKind::Variant { fields: ps, .. } => ps.iter().any(|q| self.pattern_moves(q)),
            PatKind::Struct { fields, .. } => fields.iter().any(|(_, q)| self.pattern_moves(q)),
            PatKind::Or(alts) => alts.iter().any(|a| self.pattern_moves(a)),
            PatKind::Wild | PatKind::Lit(_) => false,
        }
    }

    /// After a pattern moved parts out of `place`, drops the parts it left behind.
    fn drop_uncovered(&mut self, pat: &Pattern, place: &Place) {
        if self.pattern_moves(pat) {
            self.drop_rest(pat, place);
        }
    }

    fn drop_rest(&mut self, pat: &Pattern, place: &Place) {
        if self.info.pat_deref.contains(&pat.id) {
            return;
        }
        match &pat.kind {
            PatKind::Bind(_) | PatKind::At(..) => {}
            PatKind::Wild | PatKind::Lit(_) => {
                let ty = self.place_ty(place);
                if !self.is_copy(&ty) {
                    let span = self.span;
                    self.push(Statement::Drop(place.clone(), span));
                }
            }
            PatKind::Tuple(ps) => {
                for (i, p) in ps.iter().enumerate() {
                    self.drop_rest(p, &place.field(i));
                }
            }
            PatKind::Variant { name, fields } => {
                let (_, idx) = self.info.variant_names[name];
                for (i, p) in fields.iter().enumerate() {
                    self.drop_rest(p, &place.downcast(idx, i));
                }
            }
            PatKind::Struct { name, fields } => {
                // Named fields not mentioned are dropped too.
                let all: Vec<String> = if let Some(s) = self.info.structs.get(name) {
                    s.fields.iter().map(|(f, _)| f.clone()).collect()
                } else {
                    let (en, idx) = &self.info.variant_names[name];
                    self.info.enums[en].variants[*idx].fields.iter().map(|(f, _)| f.clone().unwrap()).collect()
                };
                for f in all {
                    let sub = self.field_place(name, &f, place);
                    match fields.iter().find(|(n, _)| *n == f) {
                        Some((_, p)) => self.drop_rest(p, &sub),
                        None => {
                            let ty = self.place_ty(&sub);
                            if !self.is_copy(&ty) {
                                let span = self.span;
                                self.push(Statement::Drop(sub, span));
                            }
                        }
                    }
                }
            }
            PatKind::Or(alts) => self.on_alt(pat, alts.len(), &mut |this, i| this.drop_rest(&alts[i], place)),
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

    /// Place of local variable `n`: a local of this body, or a capture reached through `_1`.
    fn var_place(&self, n: &str) -> Option<Place> {
        match self.lookup(n) {
            Some(id) => Some(Place::local(id)),
            None => self.captured.get(n).cloned(),
        }
    }

    /// Type of global `name` instantiated with `targs`.
    fn instantiated(&self, name: &str, targs: &[Type]) -> Type {
        let s = &self.info.globals[name].scheme;
        let map: HashMap<String, Type> = s.vars.iter().cloned().zip(targs.iter().cloned()).collect();
        subst(&s.ty, &map)
    }

    /// `code` (taking `n` arguments, of instantiated type `full`) applied to lowered `ops`:
    /// fewer make a function value, exactly `n` call it, more call it and apply the rest to
    /// the result. `ty` is the type of the whole application.
    fn apply_code(&mut self, code: FnCode, n: usize, mut ops: Vec<Operand>, full: &Type, ty: Type) -> Operand {
        if ops.len() < n {
            let alloc = if ops.is_empty() { Alloc::Static } else { Alloc::Heap };
            return self.eval_to_temp(ty, Rvalue::Aggregate(Agg::Fn { code, alloc }, ops));
        }
        let rest = ops.split_off(n);
        let rty = if rest.is_empty() { ty.clone() } else { full.uncurry_n(n).1 };
        let v = match code {
            FnCode::Global(c) => self.eval_to_temp(rty, Rvalue::Call(c, ops)),
            FnCode::Variant(t, i) => self.eval_to_temp(rty, Rvalue::Aggregate(Agg::Variant(t, i), ops)),
            FnCode::Closure { .. } => unreachable!("closures are applied as values"),
        };
        if rest.is_empty() {
            return v;
        }
        let mut vops = vec![v];
        vops.extend(rest);
        self.eval_to_temp(ty, Rvalue::Call(Callee::Value, vops))
    }

    /// A closure literal: lowers its body as a separate `Body` and builds its environment here.
    fn closure(&mut self, e: &Expr, params: &[ClosureParam], body: &Block) -> Result<Operand, Diagnostic> {
        let ci = self.info.closures[&e.id].clone();
        self.lower_closure_body(&ci, params, body)?;
        let mut env = Vec::new();
        for (c, fty) in ci.captures.iter().zip(ci.env_fields()) {
            let place = self.var_place(&c.name).expect("checked: captured variable is in scope");
            let op = match c.mode {
                CaptureMode::Shared => self.eval_to_temp(fty, Rvalue::Ref(false, place)),
                CaptureMode::Mut => self.eval_to_temp(fty, Rvalue::Ref(true, place)),
                CaptureMode::Reborrow => self.eval_to_temp(fty, Rvalue::Ref(true, place.deref())),
                CaptureMode::Move => Operand::Place(place),
            };
            env.push(op);
        }
        let alloc = match (env.is_empty(), ci.is_move) {
            (true, _) => Alloc::Static,
            (false, true) => Alloc::Heap,
            (false, false) => Alloc::Stack,
        };
        let targs = self.info.globals[&ci.name].scheme.vars.iter().map(|v| Type::Param(v.clone())).collect();
        let fn_ty = Type::func(&ci.params, ci.ret.clone());
        let f = self.eval_to_temp(fn_ty.clone(), Rvalue::Aggregate(Agg::Fn { code: FnCode::Closure { name: ci.name.clone(), targs }, alloc }, env));
        if alloc == Alloc::Stack {
            let Operand::Place(p) = f else { unreachable!() };
            return Ok(self.eval_to_temp(Type::r#ref(false, fn_ty), Rvalue::Ref(false, p)));
        }
        Ok(f)
    }

    fn lower_closure_body(&mut self, ci: &ClosureInfo, params: &[ClosureParam], body: &Block) -> Result<(), Diagnostic> {
        let mut l = Lowerer {
            body: Body {
                name: ci.name.clone(),
                locals: vec![Local { name: "_ret".into(), ty: ci.ret.clone() }],
                n_params: 1 + ci.params.len(),
                blocks: vec![BasicBlock { stmts: vec![], term: Terminator::Unreachable }],
                captures: ci.captures.iter().map(|c| c.name.clone()).collect(),
            },
            cur: 0,
            scopes: vec![HashMap::new()],
            info: self.info,
            span: ci.span,
            copy_params: self.copy_params.clone(),
            or_sel: HashMap::new(),
            owned: vec![vec![]],
            loops: vec![],
            captured: HashMap::new(),
            extra: vec![],
        };
        let env = l.new_local("env", ci.env_type());
        for (k, c) in ci.captures.iter().enumerate() {
            let place = Place::local(env).deref().field(k);
            let place = if c.mode == CaptureMode::Move { place } else { place.deref() };
            l.captured.insert(c.name.clone(), place);
        }
        if params.is_empty() {
            l.new_local("_unit", Type::unit());
        }
        for (p, t) in params.iter().zip(&ci.params) {
            let id = l.new_local(&p.name, t.clone());
            l.scopes[0].insert(p.name.clone(), id);
        }
        let v = l.block(body)?;
        l.assign(0, Rvalue::Use(v));
        l.terminate(Terminator::Return);
        self.extra.push(l.body);
        self.extra.extend(l.extra);
        Ok(())
    }

    fn callee_for_global(&self, e: &Expr, name: &str) -> Callee {
        let g = &self.info.globals[name];
        match g.kind {
            GlobalKind::Extern => Callee::Extern(name.to_string()),
            _ => Callee::Def { name: name.to_string(), targs: self.info.insts.get(&e.id).cloned().unwrap_or_default() },
        }
    }

    /// Applies the receiver adjustment recorded for `recv`.
    fn adjusted_recv(&mut self, recv: &Expr, op: Operand) -> Operand {
        let ty = self.ty(recv);
        match self.info.adjust.get(&recv.id) {
            Some(Adjust::AutoRef(m)) => self.borrow(op, &ty, *m),
            Some(Adjust::AutoDeref) => self.value(op, &ty),
            None => op,
        }
    }

    /// Type of a receiver after its adjustment.
    fn adjusted_ty(&self, recv: &Expr) -> Type {
        let ty = self.ty(recv);
        match self.info.adjust.get(&recv.id) {
            Some(Adjust::AutoDeref) => ty.peel().clone(),
            Some(Adjust::AutoRef(m)) => Type::r#ref(*m, ty),
            None => ty,
        }
    }

    /// Lowers an expression, then applies auto-deref or auto-borrow recorded on it.
    fn expr(&mut self, e: &Expr) -> Result<Operand, Diagnostic> {
        let saved = self.span;
        self.span = e.span;
        let op = self.expr_inner(e)?;
        let op = if self.info.derefs.contains(&e.id) {
            let ty = self.ty(e);
            self.value(op, &ty)
        } else if let Some(&m) = self.info.autorefs.get(&e.id) {
            let ty = self.ty(e);
            self.borrow(op, &ty, m)
        } else {
            op
        };
        self.span = saved;
        Ok(op)
    }

    fn expr_inner(&mut self, e: &Expr) -> Result<Operand, Diagnostic> {
        Ok(match &e.kind {
            ExprKind::Int(v) => Operand::Const(Const::Int(*v)),
            ExprKind::Float(v) => Operand::Const(Const::Float(*v)),
            ExprKind::Str(s) => Operand::Const(Const::Str(s.clone())),
            ExprKind::Symbol(s) => Operand::Const(Const::Symbol(s.clone())),
            ExprKind::Range(a, b, exclusive) => {
                let va = self.expr(a)?;
                let vb = self.expr(b)?;
                let ty = self.ty(e);
                self.eval_to_temp(ty.clone(), Rvalue::Aggregate(Agg::Struct(ty), vec![va, vb, Operand::Const(Const::Bool(*exclusive))]))
            }
            ExprKind::Bool(b) => Operand::Const(Const::Bool(*b)),
            ExprKind::Unit => Operand::Const(Const::Unit),
            ExprKind::Var(n) => match self.var_place(n) {
                Some(p) => Operand::Place(p),
                None => {
                    let g = &self.info.globals[n];
                    if g.n_params != 0 {
                        // A named function or constructor as a value.
                        let ty = self.ty(e);
                        let n_params = g.n_params;
                        let code = match g.kind {
                            GlobalKind::Variant { index, .. } => FnCode::Variant(ty.uncurry_n(n_params).1, index),
                            _ => FnCode::Global(self.callee_for_global(e, n)),
                        };
                        return Ok(self.apply_code(code, n_params, vec![], &ty.clone(), ty));
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
            ExprKind::Dot { recv, args, .. } => {
                let res = self.info.dots[&e.id].clone();
                // `Type.function(..)` and `Type.method(..)`: the receiver is a type, not evaluated.
                let named = match &res {
                    DotRes::Assoc { global, targs } | DotRes::MethodValue(MethodRes::Direct { global, targs }) => {
                        let full = self.instantiated(global, targs);
                        Some((Callee::Def { name: global.clone(), targs: targs.clone() }, self.info.globals[global].n_params, full))
                    }
                    DotRes::MethodValue(MethodRes::Trait { trait_name, method, self_ty }) => {
                        let n = self.info.traits[trait_name].methods[method].n_params;
                        let callee = Callee::Trait { trait_name: trait_name.clone(), method: method.clone(), self_ty: self_ty.clone() };
                        Some((callee, n, self.ty(e)))
                    }
                    _ => None,
                };
                if let Some((callee, n, full)) = named {
                    let args = args.as_deref().unwrap_or(&[]);
                    if args.len() > n && matches!(callee, Callee::Trait { .. }) {
                        return Err(Diagnostic::new(e.span, "too many arguments"));
                    }
                    let mut ops = Vec::new();
                    for a in args {
                        ops.push(self.arg(a)?);
                    }
                    let ty = self.ty(e);
                    return Ok(self.apply_code(FnCode::Global(callee), n, ops, &full, ty));
                }
                let rv = self.expr(recv)?;
                // Two-phase: a `&mut self` auto-borrow is taken after the arguments are evaluated.
                let two_phase = matches!(res, DotRes::Method(_)) && self.info.adjust.get(&recv.id) == Some(&Adjust::AutoRef(true));
                let rv = if two_phase { rv } else { self.adjusted_recv(recv, rv) };
                match res {
                    DotRes::Field(i) => {
                        let rty = self.adjusted_ty(recv);
                        let place = self.as_place(rv, rty);
                        Operand::Place(place.field(i))
                    }
                    DotRes::Method(m) => {
                        let (callee, n_params, full) = match m {
                            MethodRes::Direct { global, targs } => {
                                let full = self.instantiated(&global, &targs);
                                (Callee::Def { name: global.clone(), targs }, self.info.globals[&global].n_params, Some(full))
                            }
                            MethodRes::Trait { trait_name, method, self_ty } => {
                                let n = self.info.traits[&trait_name].methods[&method].n_params;
                                (Callee::Trait { trait_name, method, self_ty }, n, None)
                            }
                        };
                        let args = args.as_deref().unwrap_or(&[]);
                        if args.len() + 1 > n_params && full.is_none() {
                            return Err(Diagnostic::new(e.span, "too many arguments"));
                        }
                        let mut ops = vec![Operand::Const(Const::Unit)];
                        for a in args {
                            ops.push(self.arg(a)?);
                        }
                        ops[0] = if two_phase {
                            self.adjusted_recv(recv, rv)
                        } else {
                            let rty = self.adjusted_ty(recv);
                            self.reborrow(rv, &rty)
                        };
                        let ty = self.ty(e);
                        let full = full.unwrap_or_else(|| ty.clone());
                        self.apply_code(FnCode::Global(callee), n_params, ops, &full, ty)
                    }
                    DotRes::Assoc { .. } | DotRes::MethodValue(_) => unreachable!(),
                }
            }
            ExprKind::TupleIndex(recv, i) => {
                let rv = self.expr(recv)?;
                let rv = self.adjusted_recv(recv, rv);
                let rty = self.adjusted_ty(recv);
                let place = self.as_place(rv, rty);
                Operand::Place(place.field(*i))
            }
            ExprKind::Ref(m, x) => {
                let v = self.expr(x)?;
                let xt = self.ty(x);
                let place = self.as_place(v, xt);
                let ty = self.ty(e);
                self.eval_to_temp(ty, Rvalue::Ref(*m, place))
            }
            ExprKind::Deref(x) => {
                let v = self.expr(x)?;
                let xt = self.ty(x);
                let place = self.as_place(v, xt);
                Operand::Place(place.deref())
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
            ExprKind::Binary(op @ (BinOp::Eq | BinOp::Ne), a, b) => {
                let va = self.expr(a)?;
                let vb = self.expr(b)?;
                let (ta, tb) = (self.ty(a), self.ty(b));
                let base = ta.peel().clone();
                let eq = if base.is_primitive() {
                    let va = self.value(va, &ta);
                    let vb = self.value(vb, &tb);
                    self.eval_to_temp(Type::con("Bool"), Rvalue::Binary(BinOp::Eq, va, vb))
                } else {
                    let ra = self.borrow(va, &ta, false);
                    let rb = self.borrow(vb, &tb, false);
                    let callee = Callee::Trait { trait_name: "Eq".into(), method: "eq".into(), self_ty: base };
                    self.eval_to_temp(Type::con("Bool"), Rvalue::Call(callee, vec![ra, rb]))
                };
                match op {
                    BinOp::Eq => eq,
                    _ => self.eval_to_temp(Type::con("Bool"), Rvalue::Unary(UnOp::Not, eq)),
                }
            }
            ExprKind::Binary(BinOp::Add, a, b) if self.ty(a).peel().head() == Some("String") => {
                let va = self.expr(a)?;
                let vb = self.expr(b)?;
                let (ta, tb) = (self.ty(a), self.ty(b));
                let ra = self.borrow(va, &ta, false);
                let rb = self.borrow(vb, &tb, false);
                self.eval_to_temp(Type::con("String"), Rvalue::Call(Callee::Extern("str_concat".into()), vec![ra, rb]))
            }
            ExprKind::Binary(op, a, b) => {
                let va = self.expr(a)?;
                let vb = self.expr(b)?;
                let ty = self.ty(e);
                self.eval_to_temp(ty, Rvalue::Binary(*op, va, vb))
            }
            ExprKind::Call(f, args) => {
                let ty = self.ty(e);
                let global = match &f.kind {
                    ExprKind::Var(n) if self.var_place(n).is_none() => Some(n.clone()),
                    _ => None,
                };
                let Some(name) = global else {
                    // A function value (or a reference to one).
                    let mut ops = vec![self.expr(f)?];
                    for a in args {
                        ops.push(self.arg(a)?);
                    }
                    if args.is_empty() {
                        ops.push(Operand::Const(Const::Unit));
                    }
                    return Ok(self.eval_to_temp(ty, Rvalue::Call(Callee::Value, ops)));
                };
                let g = &self.info.globals[&name];
                let n_params = g.n_params;
                let variant = match g.kind {
                    GlobalKind::Variant { index, .. } => Some(index),
                    _ => None,
                };
                let mut ops = Vec::new();
                for a in args {
                    ops.push(if variant.is_some() { self.expr(a)? } else { self.arg(a)? });
                }
                let full = self.ty(f);
                if args.is_empty() && n_params > 0 {
                    ops.push(Operand::Const(Const::Unit));
                }
                let code = match variant {
                    Some(index) => FnCode::Variant(full.uncurry_n(n_params).1, index),
                    None => FnCode::Global(self.callee_for_global(f, &name)),
                };
                self.apply_code(code, n_params, ops, &full, ty)
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
                self.loops.push(LoopCtx { break_bb: exit, next_bb: head, value: None, depth: self.owned.len() });
                let v = self.block(body)?;
                self.discard(v);
                self.loops.pop();
                self.terminate(Terminator::Goto(head));
                self.cur = exit;
                Operand::Const(Const::Unit)
            }
            ExprKind::Case { scrutinee, arms } => self.case(e, scrutinee, arms)?,
            ExprKind::Interp(parts) => {
                let mut acc: Option<Operand> = None;
                // The owned String temp behind `acc` once a concat has happened.
                let mut owned_acc: Option<Operand> = None;
                for part in parts {
                    let piece = match part {
                        InterpPart::Lit(s) => {
                            let t = self.temp(Type::con("String"));
                            self.assign(t, Rvalue::Use(Operand::Const(Const::Str(s.clone()))));
                            self.eval_to_temp(Type::r#ref(false, Type::con("String")), Rvalue::Ref(false, Place::local(t)))
                        }
                        InterpPart::Expr(x) => {
                            let v = self.expr(x)?;
                            let ty = self.ty(x);
                            if ty.peel().head() == Some("String") {
                                self.borrow(v, &ty, false)
                            } else {
                                let r = self.borrow(v, &ty, false);
                                let callee = Callee::Trait { trait_name: "Show".into(), method: "to_s".into(), self_ty: ty.peel().clone() };
                                let owned = self.eval_to_temp(Type::con("String"), Rvalue::Call(callee, vec![r]));
                                self.borrow(owned, &Type::con("String"), false)
                            }
                        }
                    };
                    acc = Some(match acc {
                        None => piece,
                        Some(prev) => {
                            let owned = self.eval_to_temp(Type::con("String"), Rvalue::Call(Callee::Extern("str_concat".into()), vec![prev, piece]));
                            owned_acc = Some(owned.clone());
                            self.borrow(owned, &Type::con("String"), false)
                        }
                    });
                }
                // The result must be an owned String: the last concat result, or a clone of a
                // single borrowed piece.
                match (owned_acc, acc) {
                    (Some(owned), _) => owned,
                    (None, None) => Operand::Const(Const::Str(String::new())),
                    (None, Some(r)) => self.eval_to_temp(Type::con("String"), Rvalue::Call(Callee::Extern("str_clone".into()), vec![r])),
                }
            }
            ExprKind::Assign(lhs, rhs) => {
                let v = self.expr(rhs)?;
                let place = self.place_of(lhs)?;
                if !place.proj.is_empty() {
                    let ty = self.place_ty(&place);
                    if !self.is_copy(&ty) {
                        let span = self.span;
                        self.push(Statement::Drop(place.clone(), span));
                    }
                }
                self.assign_place(place, Rvalue::Use(v));
                Operand::Const(Const::Unit)
            }
            ExprKind::Loop(body) => {
                let t = self.temp(self.ty(e));
                let (head, exit) = (self.new_block(), self.new_block());
                self.terminate(Terminator::Goto(head));
                self.cur = head;
                self.loops.push(LoopCtx { break_bb: exit, next_bb: head, value: Some(t), depth: self.owned.len() });
                let v = self.block(body)?;
                self.discard(v);
                self.loops.pop();
                self.terminate(Terminator::Goto(head));
                self.cur = exit;
                Operand::local(t)
            }
            ExprKind::For { var, iter, body, .. } => {
                self.for_range(var, iter, body)?;
                Operand::Const(Const::Unit)
            }
            ExprKind::Break(v) => {
                let ctx = self.loops.last().cloned().expect("checked: break inside a loop");
                if let Some(t) = ctx.value {
                    let val = match v {
                        Some(x) => self.expr(x)?,
                        None => Operand::Const(Const::Unit),
                    };
                    self.assign(t, Rvalue::Use(val));
                }
                self.exit_scopes(ctx.depth);
                self.terminate(Terminator::Goto(ctx.break_bb));
                self.cur = self.new_block();
                Operand::Const(Const::Unit)
            }
            ExprKind::Closure { params, body, .. } => self.closure(e, params, body)?,
            ExprKind::Next => {
                let ctx = self.loops.last().cloned().expect("checked: next inside a loop");
                self.exit_scopes(ctx.depth);
                self.terminate(Terminator::Goto(ctx.next_bb));
                self.cur = self.new_block();
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
            ExprKind::Var(n) => Ok(self.var_place(n).expect("checked local")),
            ExprKind::Dot { recv, .. } => {
                let DotRes::Field(i) = self.info.dots[&lhs.id] else { unreachable!("checker allows only fields") };
                let mut p = self.place_of(recv)?;
                if self.info.adjust.get(&recv.id) == Some(&Adjust::AutoDeref) {
                    p = p.deref();
                }
                Ok(p.field(i))
            }
            ExprKind::TupleIndex(recv, i) => {
                let mut p = self.place_of(recv)?;
                if self.info.adjust.get(&recv.id) == Some(&Adjust::AutoDeref) {
                    p = p.deref();
                }
                Ok(p.field(*i))
            }
            ExprKind::Deref(inner) => {
                let v = self.expr(inner)?;
                let it = self.ty(inner);
                Ok(self.as_place(v, it).deref())
            }
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
            self.push_scope();
            let binds = self.declare_binders(&arm.pat);
            self.test_pat(&arm.pat, &splace, next_test);
            self.bind_case(&arm.pat, &splace, &binds);
            if let Some(g) = &arm.guard {
                let gv = self.expr(g)?;
                let body_bb = self.new_block();
                self.terminate(Terminator::If(gv, body_bb, next_test));
                self.cur = body_bb;
            }
            self.drop_uncovered(&arm.pat, &splace);
            let v = self.block(&arm.body)?;
            self.assign(result, Rvalue::Use(v));
            self.pop_scope(Operand::Const(Const::Unit));
            self.terminate(Terminator::Goto(join));
        }
        // Exhaustiveness guarantees the final failure block is dead.
        self.cur = next_test;
        self.terminate(Terminator::Unreachable);
        self.cur = join;
        Ok(Operand::local(result))
    }

    /// Emits tests for `pat` against `place`; on failure control goes to `fail`.
    /// On return, `self.cur` is the success block. Binds nothing (see `bind_case`).
    fn test_pat(&mut self, pat: &Pattern, place: &Place, fail: BlockId) {
        let place = if self.info.pat_deref.contains(&pat.id) { place.deref() } else { place.clone() };
        match &pat.kind {
            PatKind::Wild => {}
            PatKind::Bind(_) => {}
            PatKind::At(_, inner) => self.test_pat(inner, &place, fail),
            PatKind::Lit(l) => {
                let c = match l {
                    Lit::Int(v) => Const::Int(*v),
                    Lit::Float(v) => Const::Float(*v),
                    Lit::Str(s) => Const::Str(s.clone()),
                    Lit::Symbol(s) => Const::Symbol(s.clone()),
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
                    self.test_pat(p, &place.field(i), fail);
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
                    self.test_pat(p, &place.downcast(idx, i), fail);
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
                    let sub = self.field_place(name, fname, &place);
                    self.test_pat(p, &sub, fail);
                }
            }
            PatKind::Or(alts) => {
                let success = self.new_block();
                let sel = self.temp(Type::con("Int"));
                self.or_sel.insert(pat.id, sel);
                for (i, alt) in alts.iter().enumerate() {
                    let next_alt = if i + 1 < alts.len() { self.new_block() } else { fail };
                    self.test_pat(alt, &place, next_alt);
                    self.assign(sel, Rvalue::Use(Operand::Const(Const::Int(i as i64))));
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
            Proj::Deref => s = format!("(*{s})"),
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
        Operand::Const(Const::Symbol(s)) => format!(":{s}"),
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
            let args = |ops: &[Operand]| ops.iter().map(fmt_operand).collect::<Vec<_>>().join(", ");
            match st {
                Statement::Drop(p, _) => writeln!(s, "  drop({})", fmt_place(p)).unwrap(),
                Statement::StorageDead(l, _) => writeln!(s, "  dead(_{l})").unwrap(),
                Statement::Assign(place, rv, _) => {
                    let rhs = match rv {
                        Rvalue::Use(o) => fmt_operand(o),
                        Rvalue::MoveOut(p) => format!("move {}", fmt_place(p)),
                        Rvalue::Ref(m, p) => format!("&{}{}", if *m { "mut " } else { "" }, fmt_place(p)),
                        Rvalue::Binary(op, a, c) => format!("{op:?} {} {}", fmt_operand(a), fmt_operand(c)),
                        Rvalue::Unary(op, a) => format!("{op:?} {}", fmt_operand(a)),
                        Rvalue::Call(callee, ops) => match callee {
                            Callee::Def { name, targs } => format!("call {name}{}({})", fmt_targs(targs), args(ops)),
                            Callee::Extern(n) => format!("call extern {n}({})", args(ops)),
                            Callee::Trait { trait_name, method, self_ty } => format!("call {trait_name}::{method}[{self_ty}]({})", args(ops)),
                            Callee::Value => format!("call value {}({})", fmt_operand(&ops[0]), args(&ops[1..])),
                        },
                        Rvalue::Aggregate(agg, ops) => match agg {
                            Agg::Struct(t) => format!("{t} {{ {} }}", args(ops)),
                            Agg::Tuple(_) => format!("({})", args(ops)),
                            Agg::Variant(t, i) => format!("{t}::{i}({})", args(ops)),
                            Agg::Fn { code, alloc } => {
                                let code = match code {
                                    FnCode::Closure { name, targs } => format!("closure {name}{}", fmt_targs(targs)),
                                    FnCode::Global(Callee::Def { name, targs }) => format!("global {name}{}", fmt_targs(targs)),
                                    FnCode::Global(Callee::Extern(n)) => format!("global extern {n}"),
                                    FnCode::Global(Callee::Trait { trait_name, method, self_ty }) => format!("global {trait_name}::{method}[{self_ty}]"),
                                    FnCode::Global(Callee::Value) => unreachable!("values are applied, not wrapped"),
                                    FnCode::Variant(t, i) => format!("variant {t}::{i}"),
                                };
                                format!("make_fn {code} [{}] {}", args(ops), format!("{alloc:?}").to_lowercase())
                            }
                        },
                        Rvalue::Discriminant(p) => format!("discr({})", fmt_place(p)),
                    };
                    writeln!(s, "  {} = {rhs}", fmt_place(place)).unwrap();
                }
            }
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

    pub fn lower_src(s: &str) -> Result<Vec<Body>, Diagnostic> {
        let prelude = include_str!("../std/prelude.rush");
        let mut id = 0;
        let mut p = parse(lex(prelude).unwrap(), &mut id).unwrap();
        p.items.extend(parse(lex(s).unwrap(), &mut id).unwrap().items);
        crate::derive::expand(&mut p, &mut id)?;
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
             bb0:\n  _3 = Add _1 _2\n  _4 = _3\n  _5 = Mul _4 2\n  dead(_4)\n  dead(_3)\n  _0 = _5\n  return\n"
        );
    }

    #[test]
    fn if_expression_joins() {
        assert_eq!(
            dump_fn(&format!("def f(n: Int) -> Int\n  if n < 2\n    n\n  else\n    f(n - 1)\n  end\nend\n{MAIN}"), "f"),
            "fn f(_1: Int) -> Int\n\
             bb0:\n  _2 = Lt _1 2\n  if _2 then bb1 else bb2\n\
             bb1:\n  _3 = _1\n  goto bb3\n\
             bb2:\n  _4 = Sub _1 1\n  _5 = call f(_4)\n  dead(_4)\n  _3 = _5\n  goto bb3\n\
             bb3:\n  dead(_5)\n  dead(_2)\n  _0 = _3\n  return\n"
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
    fn struct_literal_field_read_and_write() {
        assert_eq!(
            dump_fn("struct P\n  x: Int\n  y: Int\nend\ndef main\n  let mut p = P { y: 2, x: 1 }\n  p.x = p.y\n  ()\nend\n", "main"),
            "fn main() -> Unit\n\
             bb0:\n  _1 = P { 1, 2 }\n  _2 = _1\n  _2.0 = _2.1\n  dead(_2)\n  dead(_1)\n  _0 = ()\n  return\n"
        );
    }

    #[test]
    fn variant_construction_and_case_by_value() {
        assert_eq!(
            dump_fn(&format!("enum S\n  C(Float)\n  R(Float, Float)\nend\ndef area(s: S) -> Float\n  case s\n  in C(r) then r * r\n  in R(w, h) then w * h\n  end\nend\n{MAIN}"), "area"),
            "fn area(_1: S) -> Float\n\
             bb0:\n  goto bb2\n\
             bb1:\n  _0 = _2\n  return\n\
             bb2:\n  _4 = discr(_1)\n  _5 = Eq _4 0\n  if _5 then bb4 else bb3\n\
             bb3:\n  _9 = discr(_1)\n  _10 = Eq _9 1\n  if _10 then bb6 else bb5\n\
             bb4:\n  _3 = move (_1 as 0).0\n  _6 = Mul _3 _3\n  _2 = _6\n  dead(_6)\n  dead(_5)\n  dead(_4)\n  dead(_3)\n  goto bb1\n\
             bb5:\n  unreachable\n\
             bb6:\n  _7 = move (_1 as 1).0\n  _8 = move (_1 as 1).1\n  _11 = Mul _7 _8\n  _2 = _11\n  dead(_11)\n  dead(_10)\n  dead(_9)\n  dead(_8)\n  dead(_7)\n  goto bb1\n"
        );
    }

    // ----- Plan 3b -----

    #[test]
    fn scope_locals_die_in_reverse_order_and_arm_locals_at_arm_end() {
        let d = dump_fn(&format!("def f(c: Bool) -> Int\n  let a = 1\n  let b = 2\n  if c\n    let x = 3\n    x\n  else\n    0\n  end\nend\n{MAIN}"), "f");
        assert_eq!(
            d,
            "fn f(_1: Bool) -> Int\nbb0:\n  _2 = 1\n  _3 = 2\n  if _1 then bb1 else bb2\n\
             bb1:\n  _5 = 3\n  _6 = _5\n  dead(_5)\n  _4 = _6\n  goto bb3\n\
             bb2:\n  _4 = 0\n  goto bb3\n\
             bb3:\n  dead(_6)\n  dead(_3)\n  dead(_2)\n  _0 = _4\n  return\n"
        );
    }

    #[test]
    fn two_phase_receiver_borrows_after_arguments() {
        let src = format!("struct P\n  age: Int\nend\nimpl P\n  def set(&mut self, a: Int)\n    @age = a\n  end\nend\ndef main\n  let mut p = P {{ age: 1 }}\n  p.set(p.age + 1)\n  ()\nend\n");
        let d = dump_fn(&src, "main");
        let add = d.find("= Add ").unwrap();
        let borrow = d.find("= &mut _").unwrap();
        assert!(add < borrow, "{d}");
    }

    #[test]
    fn mut_reference_arguments_are_reborrowed() {
        let src = format!("def bump(r: &mut Int)\n  *r = *r + 1\nend\ndef twice(r: &mut Int)\n  bump(r)\n  bump(r)\nend\n{MAIN}");
        let d = dump_fn(&src, "twice");
        assert_eq!(d.matches("= &mut (*_1)").count(), 2, "{d}");
    }

    // ----- Plan 3a -----

    #[test]
    fn references_deref_and_auto_borrow() {
        let src = "def add(a: &Int, b: &Int) -> Int\n  a + b\nend\ndef main\n  let x = 1\n  let r = &x\n  let y = add(&x, r) + *r\n  puts(int_to_s(y))\nend\n";
        assert_eq!(
            dump_fn(src, "add"),
            "fn add(_1: &Int, _2: &Int) -> Int\n\
             bb0:\n  _3 = Add (*_1) (*_2)\n  _0 = _3\n  return\n"
        );
        let d = dump_fn(src, "main");
        assert!(d.contains("_2 = &_1\n  _3 = _2\n"), "{d}");
        assert!(d.contains("_4 = &_1\n  _5 = call add(_4, _3)\n"), "{d}");
        assert!(d.contains("Add _5 (*_3)"), "{d}");
        assert!(d.contains("call extern int_to_s("), "{d}");
        assert!(d.contains("call extern puts(_"), "{d}");
    }

    #[test]
    fn method_receiver_adjustments_and_match_ergonomics() {
        let src = "enum S\n  C(Float)\n  R(String, Float)\nend\nimpl S\n  def size(&self) -> Float\n    case self\n    in C(r) then r * r\n    in R(n, h) then h\n    end\n  end\nend\ndef main\n  let s = C(1.0)\n  let f = s.size + s.size\n  ()\nend\n";
        let d = dump_fn(src, "main");
        assert!(d.contains("_3 = &_2\n  _4 = call S#"), "{d}");
        let bodies = lower_src(src).unwrap();
        let size = bodies.iter().find(|b| b.name.ends_with("::size")).unwrap();
        let ds = dump(size);
        assert!(ds.contains("discr((*_1))"), "{ds}");
        assert!(ds.contains("= &((*_1) as 0).0\n"), "{ds}");
        assert!(ds.contains("Mul (*_3) (*_3)"), "{ds}");
    }

    #[test]
    fn destructuring_moves_and_drops_uncovered() {
        let src = "def main\n  let t = (\"a\", \"b\", 1)\n  let (a, _, n) = t\n  ()\nend\n";
        let d = dump_fn(src, "main");
        assert!(d.contains("= move _2.0\n"), "{d}");
        assert!(d.contains("drop(_2.1)\n"), "{d}");
        assert!(d.contains("= move _2.2\n"), "{d}");
    }

    #[test]
    fn string_ops_borrow_and_interpolation_clones_result() {
        let src = "def main\n  let a = \"x\"\n  let b = a + \"y\"\n  let c = \"#{a}!\"\n  let d = \"#{a}\"\n  let e = a == b\n  ()\nend\n";
        let d = dump_fn(src, "main");
        assert!(d.contains("call extern str_concat(_"), "{d}");
        assert_eq!(d.matches("call extern str_clone(_").count(), 1, "{d}");
        assert!(d.contains("= Eq _1 _"), "{d}");
        assert!(!d.contains("= _1\n"), "{d}");
    }

    #[test]
    fn field_reassignment_drops_old_value_and_assoc_calls() {
        let src = "struct P\n  name: String\nend\nimpl P\n  def make(n: String) -> P\n    P { name: n }\n  end\nend\ndef main\n  let mut p = P.make(\"a\")\n  p.name = \"b\"\n  let g = Gc.new(p)\n  let n = g.borrow.name.clone\n  ()\nend\n";
        let d = dump_fn(src, "main");
        assert!(d.contains("drop(_2.0)\n  _2.0 = "), "{d}");
        assert!(d.contains("::make("), "{d}");
        assert!(d.contains("call Gc::new[P](_2)"), "{d}");
        assert!(d.contains("call Gc::borrow[P](_"), "{d}");
        assert!(d.contains("= &(*_"), "{d}");
    }

    #[test]
    fn break_ends_inner_scopes_first_and_next_goes_to_the_step() {
        let f = dump_fn(&format!("def f -> Int
  loop
    let a = 1
    if true
      let b = 2
      break b
    end
  end
end
{MAIN}"), "f");
        // b, then the `if` temp, then a; then the loop's exit.
        assert!(f.contains("bb3:
  _4 = 2
  _1 = _4
  dead(_4)
  dead(_3)
  dead(_2)
  goto bb2
"), "{f}");
        assert!(f.contains("bb2:
  _0 = _1
  return
"), "{f}");
        let g = dump_fn(&format!("def g
  for i in 1..3
    next
  end
end
{MAIN}"), "g");
        assert!(g.contains("bb2:
  _11 = _2
  dead(_11)
  goto bb3
"), "{g}");
        assert!(g.contains("bb3:
  _12 = Eq _2 _3
"), "{g}");
    }

    /// Dumps of every body whose name starts with `prefix`, joined.
    fn dumps(src: &str, prefix: &str) -> String {
        lower_src(src).unwrap().iter().filter(|b| b.name.starts_with(prefix)).map(dump).collect::<Vec<_>>().join("\n")
    }

    #[test]
    fn borrowing_closure_is_a_stack_value_behind_a_reference() {
        let d = dumps("def main\n  let mut total = 0\n  let f = { |i: Int| total += i }\n  f(1)\n  ()\nend\n", "main");
        assert!(d.contains("  _2 = &mut _1\n  _3 = make_fn closure main#c0 [_2] stack\n  _4 = &_3\n"), "{d}");
        assert!(d.contains("call value _5(1)"), "{d}");
        assert!(d.contains("fn main#c0(_1: &(&mut Int), _2: Int) -> Unit\nbb0:\n  _3 = Add (*(*_1).0) _2\n  (*(*_1).0) = _3\n"), "{d}");
    }

    #[test]
    fn move_closure_moves_its_capture_into_a_heap_environment() {
        let d = dumps("def mk(s: String) -> Unit -> String\n  move { || s.clone }\nend\ndef main\n  ()\nend\n", "mk");
        assert!(d.contains("  _2 = make_fn closure mk#c0 [_1] heap\n  _0 = _2\n"), "{d}");
        assert!(d.contains("fn mk#c0(_1: &(String), _2: Unit) -> String\nbb0:\n  _3 = &(*_1).0\n"), "{d}");
    }

    #[test]
    fn function_values_partial_and_over_application() {
        let d = dumps("def add(a: Int, b: Int) -> Int\n  a + b\nend\ndef adder(k: Int) -> Int -> Int\n  move { |x| x + k }\nend\n\
                       def main\n  let g = add(1)\n  let h = add\n  let w = Some\n  let o = w(1)\n  let r = adder(1)(2)\n  let q = adder(1, 2)\n  let v = g(3)\n  ()\nend\n", "main");
        for want in [
            "_1 = make_fn global add [1] heap",
            "_3 = make_fn global add [] static",
            "_5 = make_fn variant Option[Int]::0 [] static",
            "_7 = call value _6(1)",
            "_9 = call adder(1)\n  _10 = call value _9(2)",
            "_12 = call adder(1)\n  _13 = call value _12(2)",
            "_15 = call value _2(3)",
        ] {
            assert!(d.contains(want), "missing {want:?} in\n{d}");
        }
    }

    #[test]
    fn methods_as_values_and_partially_applied_method_calls() {
        let src = "struct P\n  x: Int\nend\nimpl P\n  def plus(&self, k: Int) -> Int\n    @x + k\n  end\nend\n\
                   def main\n  let p = P { x: 1 }\n  let m = P.plus\n  let a = m(&p, 2)\n  let s = p.plus\n  let b = s(3)\n  ()\nend\n";
        let d = dumps(src, "main");
        assert!(d.contains("make_fn global P#") && d.contains("::plus [] static"), "{d}");
        assert!(d.contains("::plus [_") && d.contains("] heap"), "{d}");
        assert!(d.contains("call value"), "{d}");
    }

    #[test]
    fn nested_closure_builds_its_environment_from_the_outer_one() {
        let d = dumps("def main\n  let mut n = 0\n  let f = { |y: Int|\n    let g = { |x: Int| n += x }\n    g(y)\n  }\n  ()\nend\n", "main#c1");
        assert!(d.contains("  _3 = &mut (*(*_1).0)\n  _4 = make_fn closure main#c0 [_3] stack\n  _5 = &_4\n"), "{d}");
    }
}
