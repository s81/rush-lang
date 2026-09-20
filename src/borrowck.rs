//! Borrow checking on the MIR with non-lexical lifetimes. Runs after `ownck`, before `mono`.
//!
//! A loan is created by each `&`/`&mut` (a place loan), by each parameter whose type holds a
//! reference (an entry loan: whatever the caller lent), and by each `Gc` borrow call (a runtime
//! loan). `holds[l]` is the set of loans local `l` may carry, a forward dataflow. A loan is live
//! where some local holding it is live, a backward dataflow. Every place access is checked
//! against the place loans live just before it.

use std::collections::HashMap;

use crate::diag::{Diagnostic, Span};
use crate::mir::*;
use crate::types::{GlobalKind, Type, TypeInfo};

#[derive(Clone, PartialEq, Debug)]
struct Bits(Vec<u64>);

impl Bits {
    fn new(n: usize) -> Bits {
        Bits(vec![0; n.div_ceil(64)])
    }
    fn insert(&mut self, i: usize) {
        self.0[i / 64] |= 1 << (i % 64);
    }
    fn contains(&self, i: usize) -> bool {
        self.0[i / 64] >> (i % 64) & 1 == 1
    }
    fn union(&mut self, o: &Bits) -> bool {
        let mut changed = false;
        for (a, b) in self.0.iter_mut().zip(&o.0) {
            let n = *a | b;
            changed |= n != *a;
            *a = n;
        }
        changed
    }
    fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        (0..self.0.len() * 64).filter(|&i| self.contains(i))
    }
}

#[derive(Debug)]
enum Origin {
    /// `&place` or `&mut place` (the bool).
    Place(Place, bool),
    /// What the caller lent through this parameter.
    Entry(LocalId),
    /// `g.borrow` (false) or `g.borrow_mut` (true); released at runtime, no compile-time place.
    Gc(bool),
}

#[derive(Debug)]
struct Loan {
    origin: Origin,
    span: Span,
}

#[derive(Clone, Copy, PartialEq)]
enum Access {
    Read,
    Borrow(bool),
    Assign,
    Move,
    /// The storage ends (scope exit, drop, or return).
    Kill,
}

struct Bc<'a> {
    info: &'a TypeInfo,
    body: &'a Body,
    loans: Vec<Loan>,
    /// (block, statement index) -> the loan that statement creates.
    created: HashMap<(usize, usize), usize>,
    /// Locals whose type may hold a reference.
    carries: Vec<bool>,
}

fn root_uses_op(op: &Operand, out: &mut Vec<LocalId>) {
    if let Operand::Place(p) = op {
        out.push(p.local);
    }
}

/// Locals a statement reads, and the local it overwrites whole (for liveness).
fn uses_and_kill(info: &TypeInfo, body: &Body, s: &Statement) -> (Vec<LocalId>, Option<LocalId>) {
    let mut used = Vec::new();
    match s {
        Statement::Assign(target, rv, _) => {
            match rv {
                Rvalue::Use(op) | Rvalue::Unary(_, op) => root_uses_op(op, &mut used),
                Rvalue::MoveOut(p) | Rvalue::Ref(_, p) | Rvalue::Discriminant(p) => used.push(p.local),
                Rvalue::Binary(_, a, b) => {
                    root_uses_op(a, &mut used);
                    root_uses_op(b, &mut used);
                }
                Rvalue::Call(_, ops) | Rvalue::Aggregate(_, ops) => ops.iter().for_each(|o| root_uses_op(o, &mut used)),
            }
            if target.proj.contains(&Proj::Deref) {
                used.push(target.local);
            }
            let kill = if target.proj.is_empty() { Some(target.local) } else { None };
            (used, kill)
        }
        Statement::Drop(p, _) => {
            // A drop that runs code (a `Drop` impl) may read the references inside.
            let t = place_type(info, body, p);
            if t.has_param() || info.needs_drop(&t) {
                used.push(p.local);
            }
            (used, None)
        }
        Statement::StorageDead(..) => (used, None),
    }
}

fn term_uses(t: &Terminator) -> Vec<LocalId> {
    match t {
        Terminator::If(op, _, _) => {
            let mut v = Vec::new();
            root_uses_op(op, &mut v);
            v
        }
        Terminator::Return => vec![0],
        _ => vec![],
    }
}

fn successors(t: &Terminator) -> Vec<BlockId> {
    match t {
        Terminator::Goto(b) => vec![*b],
        Terminator::If(_, a, b) => vec![*a, *b],
        Terminator::Return | Terminator::Unreachable => vec![],
    }
}

/// Two places overlap when one's projections are a prefix of the other's.
fn overlaps(a: &Place, b: &Place) -> bool {
    a.local == b.local && a.proj.iter().zip(&b.proj).all(|(x, y)| x == y)
}

impl<'a> Bc<'a> {
    fn n(&self) -> usize {
        self.loans.len()
    }

    fn name(&self, p: &Place) -> String {
        describe_place(self.info, self.body, p)
    }

    fn operand_loans(&self, holds: &[Bits], op: &Operand) -> Bits {
        match op {
            // A value read out of a place carries the place's loans only if it can hold one:
            // an `Int` copied out of a capture environment borrows nothing.
            Operand::Place(p) if self.info.may_borrow(&place_type(self.info, self.body, p)) => holds[p.local as usize].clone(),
            _ => Bits::new(self.n()),
        }
    }

    /// Loans carried by the value an rvalue produces.
    fn rvalue_loans(&self, holds: &[Bits], key: (usize, usize), rv: &Rvalue, target_ty: &Type) -> Bits {
        let mut out = Bits::new(self.n());
        match rv {
            Rvalue::Ref(_, p) => {
                out.insert(self.created[&key]);
                out.union(&holds[p.local as usize]);
            }
            Rvalue::Use(op) => {
                out.union(&self.operand_loans(holds, op));
            }
            Rvalue::MoveOut(p) => {
                out.union(&holds[p.local as usize]);
            }
            Rvalue::Aggregate(_, ops) => {
                for op in ops {
                    out.union(&self.operand_loans(holds, op));
                }
            }
            Rvalue::Call(c, ops) => {
                if self.info.may_borrow(target_ty) {
                    let key_name = match c {
                        Callee::Def { name, .. } | Callee::Extern(name) => name.clone(),
                        Callee::Trait { trait_name, method, .. } => format!("{trait_name}::{method}"),
                        // No elision for function values: every operand's loans flow in.
                        Callee::Value => String::new(),
                    };
                    match self.info.elided.get(&key_name) {
                        Some(&i) => {
                            out.union(&self.operand_loans(holds, &ops[i]));
                        }
                        // A generic result instantiated with references: any argument may flow in.
                        None => {
                            for op in ops {
                                out.union(&self.operand_loans(holds, op));
                            }
                        }
                    }
                }
                if let Some(&l) = self.created.get(&key) {
                    out.insert(l);
                }
            }
            Rvalue::Binary(..) | Rvalue::Unary(..) | Rvalue::Discriminant(_) => {}
        }
        out
    }

    /// A function value of type `ty` holding `held` loans is passed where it could escape.
    /// Names a borrowed variable when one is known, preferring named places over temporaries.
    fn escaping_fn(&self, held: &Bits, ty: &Type, span: Span) -> Diagnostic {
        let named = |l: &usize| match &self.loans[*l].origin {
            Origin::Place(p, _) => !self.body.locals[p.local as usize].name.is_empty() || capture_of(self.info, self.body, p).is_some(),
            _ => true,
        };
        let l = held.iter().find(named).or_else(|| held.iter().next()).unwrap();
        let (who, note) = match &self.loans[l].origin {
            Origin::Place(p, _) => (self.name(p), Some(self.loans[l].span)),
            Origin::Entry(param) => (self.name(&Place::local(*param)), None),
            Origin::Gc(_) => ("a `Gc` value".to_string(), Some(self.loans[l].span)),
        };
        let r = Type::r#ref(false, ty.clone());
        let d = Diagnostic::new(span, format!("function value borrows `{who}` and cannot be passed as an owned function; use `move` or take `{r}`"));
        match note {
            Some(sp) => d.with_note(sp, format!("`{who}` is borrowed here")),
            None => d,
        }
    }

    /// A value carrying `loans` is stored behind the references `r` holds.
    fn write_through(&self, holds: &mut [Bits], r: LocalId, loans: &Bits, span: Span) -> Result<(), Diagnostic> {
        let held: Vec<usize> = holds[r as usize].iter().collect();
        for l in held {
            match &self.loans[l].origin {
                Origin::Place(p, _) => {
                    if self.carries[p.local as usize] {
                        holds[p.local as usize].union(loans);
                    }
                }
                Origin::Entry(param) => {
                    if loans.iter().any(|x| x != l) {
                        let who = self.name(&Place::local(*param));
                        return Err(Diagnostic::new(span, format!("cannot store a borrowed value behind `{who}`; it may outlive the borrow")));
                    }
                }
                Origin::Gc(_) => {}
            }
        }
        Ok(())
    }

    /// Applies one statement to `holds`.
    fn step(&self, holds: &mut [Bits], key: (usize, usize), s: &Statement) -> Result<(), Diagnostic> {
        match s {
            Statement::Assign(target, rv, span) => {
                let tty = place_type(self.info, self.body, target);
                let loans = self.rvalue_loans(holds, key, rv, &tty);
                // A function value holding loans cannot go where it could be stored or returned.
                if let Rvalue::Call(c, ops) = rv {
                    let args = if *c == Callee::Value { &ops[1..] } else { &ops[..] };
                    for op in args {
                        let Operand::Place(p) = op else { continue };
                        let ty = place_type(self.info, self.body, p);
                        let held = self.operand_loans(holds, op);
                        if self.info.holds_owned_fn(&ty) && held.iter().next().is_some() {
                            return Err(self.escaping_fn(&held, &ty, *span));
                        }
                    }
                }
                // Arguments may be stored behind a `&mut` argument whose pointee holds references.
                if let Rvalue::Call(_, ops) = rv {
                    for (i, op) in ops.iter().enumerate() {
                        let Operand::Place(p) = op else { continue };
                        let ty = place_type(self.info, self.body, p);
                        if let Some((true, inner)) = ty.as_ref() {
                            if self.info.may_borrow(inner) {
                                let mut others = Bits::new(self.n());
                                for (j, o) in ops.iter().enumerate() {
                                    if j != i {
                                        others.union(&self.operand_loans(holds, o));
                                    }
                                }
                                self.write_through(holds, p.local, &others, *span)?;
                            }
                        }
                    }
                }
                if target.proj.contains(&Proj::Deref) {
                    self.write_through(holds, target.local, &loans, *span)?;
                }
                let t = target.local as usize;
                if self.carries[t] {
                    if target.proj.is_empty() {
                        holds[t] = loans;
                    } else {
                        holds[t].union(&loans);
                    }
                }
            }
            Statement::StorageDead(l, _) => holds[*l as usize] = Bits::new(self.n()),
            Statement::Drop(..) => {}
        }
        Ok(())
    }

    /// The accesses a statement makes, in order.
    fn accesses(&self, s: &Statement, next: Option<&Statement>) -> Vec<(Place, Access)> {
        let mut out = Vec::new();
        let is_copy = |p: &Place| self.info.is_copy(&place_type(self.info, self.body, p), &|_| false);
        let op_access = |op: &Operand, out: &mut Vec<(Place, Access)>| {
            if let Operand::Place(p) = op {
                out.push((p.clone(), if is_copy(p) { Access::Read } else { Access::Move }));
            }
        };
        match s {
            Statement::Assign(target, rv, _) => {
                match rv {
                    Rvalue::Use(op) => op_access(op, &mut out),
                    Rvalue::MoveOut(p) => out.push((p.clone(), if is_copy(p) { Access::Read } else { Access::Move })),
                    Rvalue::Ref(m, p) => out.push((p.clone(), Access::Borrow(*m))),
                    Rvalue::Discriminant(p) => out.push((p.clone(), Access::Read)),
                    Rvalue::Binary(_, a, b) => {
                        for op in [a, b] {
                            if let Operand::Place(p) = op {
                                out.push((p.clone(), Access::Read));
                            }
                        }
                    }
                    Rvalue::Unary(_, a) => {
                        if let Operand::Place(p) = a {
                            out.push((p.clone(), Access::Read));
                        }
                    }
                    Rvalue::Call(_, ops) | Rvalue::Aggregate(_, ops) => ops.iter().for_each(|o| op_access(o, &mut out)),
                }
                out.push((target.clone(), Access::Assign));
            }
            Statement::StorageDead(l, _) => out.push((Place::local(*l), Access::Kill)),
            Statement::Drop(p, _) => {
                // A whole-local drop is always followed by that local's scope end, reassignment,
                // or return, which report the conflict with a better message; so is a field
                // drop followed by the field's reassignment.
                let reassigned = matches!(next, Some(Statement::Assign(t, _, _)) if t == p);
                if !p.proj.is_empty() && !reassigned {
                    out.push((p.clone(), Access::Kill));
                }
            }
        }
        out
    }

    fn conflict(&self, place: &Place, access: Access, l: usize, span: Span) -> Option<Diagnostic> {
        let Origin::Place(lp, mutable) = &self.loans[l].origin else { return None };
        let hit = match access {
            Access::Read | Access::Borrow(false) => *mutable && overlaps(place, lp),
            Access::Borrow(true) | Access::Assign | Access::Move => overlaps(place, lp),
            Access::Kill => lp.local == place.local && !lp.proj.contains(&Proj::Deref),
        };
        if !hit {
            return None;
        }
        let borrowed = |p: &Place| {
            if self.body.locals[p.local as usize].name.is_empty() {
                "a temporary is borrowed here".to_string()
            } else {
                format!("`{}` is borrowed here", self.name(p))
            }
        };
        if access == Access::Kill && self.body.locals[place.local as usize].name.is_empty() {
            // A borrowing closure's environment lives in the frame that creates it.
            if matches!(self.body.locals[place.local as usize].ty, Type::Fn(..)) {
                let d = Diagnostic::new(span, "borrowing closure does not live long enough; use `move` to give it its own environment");
                return Some(d.with_note(self.loans[l].span, "the closure is borrowed here"));
            }
            return Some(Diagnostic::new(span, "temporary value dropped while borrowed").with_note(self.loans[l].span, borrowed(lp)));
        }
        let x = self.name(place);
        let msg = match access {
            Access::Read => format!("cannot use `{x}` because it is mutably borrowed"),
            Access::Borrow(false) => format!("cannot borrow `{x}` as shared because it is mutably borrowed"),
            Access::Borrow(true) => format!("cannot borrow `{x}` as mutable because it is already borrowed"),
            Access::Assign => format!("cannot assign to `{x}` because it is borrowed"),
            Access::Move => format!("cannot move out of `{x}` because it is borrowed"),
            Access::Kill => format!("`{x}` does not live long enough"),
        };
        Some(Diagnostic::new(span, msg).with_note(self.loans[l].span, borrowed(lp)))
    }
}

/// Checks every body.
pub fn check(bodies: &mut [Body], info: &TypeInfo) -> Result<(), Diagnostic> {
    for body in bodies.iter_mut() {
        check_body(body, info)?;
    }
    Ok(())
}

fn check_body(body: &mut Body, info: &TypeInfo) -> Result<(), Diagnostic> {
    let n_locals = body.locals.len();
    // Function values are tracked too: closures and partial applications can hold loans.
    let carries: Vec<bool> = body.locals.iter().map(|l| info.may_borrow(&l.ty)).collect();
    let mut bc = Bc { info, body, loans: Vec::new(), created: HashMap::new(), carries };
    for (bi, bb) in body.blocks.iter().enumerate() {
        for (si, s) in bb.stmts.iter().enumerate() {
            let Statement::Assign(_, rv, span) = s else { continue };
            let origin = match rv {
                Rvalue::Ref(m, p) => Origin::Place(p.clone(), *m),
                Rvalue::Call(Callee::Def { name, .. }, _) if name == "Gc::borrow" || name == "Gc::borrow_mut" => Origin::Gc(name == "Gc::borrow_mut"),
                _ => continue,
            };
            bc.created.insert((bi, si), bc.loans.len());
            bc.loans.push(Loan { origin, span: *span });
        }
    }
    let mut entry_state: Vec<Bits> = vec![Bits::new(0); n_locals];
    let mut entry_loans: HashMap<LocalId, usize> = HashMap::new();
    for l in 1..=body.n_params {
        // An owned function parameter holds no loans: callers cannot pass a borrowing one.
        if info.contains_ref(&body.locals[l].ty) {
            entry_loans.insert(l as LocalId, bc.loans.len());
            bc.loans.push(Loan { origin: Origin::Entry(l as LocalId), span: Span::default() });
        }
    }
    let n = bc.n();
    for (l, b) in entry_state.iter_mut().enumerate() {
        *b = Bits::new(n);
        if let Some(&e) = entry_loans.get(&(l as LocalId)) {
            b.insert(e);
        }
    }

    // Forward: loans each local may hold at each block entry.
    let nb = body.blocks.len();
    let mut holds_in: Vec<Option<Vec<Bits>>> = vec![None; nb];
    holds_in[0] = Some(entry_state);
    let mut work = vec![0usize];
    while let Some(b) = work.pop() {
        let mut h = holds_in[b].clone().unwrap();
        for (si, s) in body.blocks[b].stmts.iter().enumerate() {
            bc.step(&mut h, (b, si), s)?;
        }
        for succ in successors(&body.blocks[b].term) {
            let succ = succ as usize;
            match &mut holds_in[succ] {
                None => {
                    holds_in[succ] = Some(h.clone());
                    work.push(succ);
                }
                Some(e) => {
                    let mut changed = false;
                    for (a, x) in e.iter_mut().zip(&h) {
                        changed |= a.union(x);
                    }
                    if changed {
                        work.push(succ);
                    }
                }
            }
        }
    }

    // Backward: locals live at each block exit.
    let mut live_out: Vec<Vec<bool>> = vec![vec![false; n_locals]; nb];
    let live_in_of = |b: usize, live_out: &Vec<Vec<bool>>| -> Vec<bool> {
        let mut live = live_out[b].clone();
        for u in term_uses(&body.blocks[b].term) {
            live[u as usize] = true;
        }
        for s in body.blocks[b].stmts.iter().rev() {
            let (used, kill) = uses_and_kill(info, body, s);
            if let Some(k) = kill {
                live[k as usize] = false;
            }
            for u in used {
                live[u as usize] = true;
            }
        }
        live
    };
    loop {
        let mut changed = false;
        for b in (0..nb).rev() {
            let mut out = vec![false; n_locals];
            for succ in successors(&body.blocks[b].term) {
                let li = live_in_of(succ as usize, &live_out);
                for (o, x) in out.iter_mut().zip(li) {
                    *o |= x;
                }
            }
            if out != live_out[b] {
                live_out[b] = out;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    // Check every reachable block, recording where each runtime (`Gc`) loan dies.
    let is_rt = |l: usize| matches!(bc.loans[l].origin, Origin::Gc(_));
    let mut start_live: Vec<Bits> = vec![Bits::new(n); nb];
    let mut end_live: Vec<Bits> = vec![Bits::new(n); nb];
    let mut dies_after: Vec<Vec<Vec<usize>>> = body.blocks.iter().map(|bb| vec![Vec::new(); bb.stmts.len()]).collect();
    for b in 0..nb {
        let Some(mut h) = holds_in[b].clone() else { continue };
        let bb = &body.blocks[b];
        // Live locals just before each statement, and before the terminator.
        let mut live = live_out[b].clone();
        for u in term_uses(&bb.term) {
            live[u as usize] = true;
        }
        let live_at_term = live.clone();
        let mut live_before: Vec<Vec<bool>> = vec![Vec::new(); bb.stmts.len()];
        for (si, s) in bb.stmts.iter().enumerate().rev() {
            let (used, kill) = uses_and_kill(info, body, s);
            if let Some(k) = kill {
                live[k as usize] = false;
            }
            for u in used {
                live[u as usize] = true;
            }
            live_before[si] = live.clone();
        }
        let live_loans_of = |live: &[bool], h: &[Bits]| {
            let mut out = Bits::new(n);
            for (l, &is_live) in live.iter().enumerate() {
                if is_live {
                    out.union(&h[l]);
                }
            }
            out
        };
        let mut prev: Option<Bits> = None;
        for (si, s) in bb.stmts.iter().enumerate() {
            let live_loans = live_loans_of(&live_before[si], &h);
            if si == 0 {
                start_live[b] = live_loans.clone();
            }
            if let Some(p) = prev.take() {
                dies_after[b][si - 1] = deaths(&p, bc.created.get(&(b, si - 1)), &live_loans, &is_rt);
            }
            let span = match s {
                Statement::Assign(_, _, sp) | Statement::Drop(_, sp) | Statement::StorageDead(_, sp) => *sp,
            };
            for (place, access) in bc.accesses(s, bb.stmts.get(si + 1)) {
                for l in live_loans.iter() {
                    if let Some(d) = bc.conflict(&place, access, l, span) {
                        return Err(d);
                    }
                }
            }
            if let Some(&k) = bc.created.get(&(b, si)) {
                if is_rt(k) && live_loans.contains(k) {
                    return Err(Diagnostic::new(span, "this `Gc` borrow is still in use from an earlier loop iteration"));
                }
            }
            bc.step(&mut h, (b, si), s)?;
            prev = Some(live_loans);
        }
        let at_end = live_loans_of(&live_at_term, &h);
        match prev {
            Some(p) => {
                let last = bb.stmts.len() - 1;
                dies_after[b][last] = deaths(&p, bc.created.get(&(b, last)), &at_end, &is_rt);
            }
            None => start_live[b] = at_end.clone(),
        }
        end_live[b] = at_end;
        if matches!(bb.term, Terminator::Return) {
            check_return(&bc, &h[0], bb)?;
        }
    }
    let runtime: Vec<usize> = (0..n).filter(|&l| is_rt(l)).collect();
    if runtime.is_empty() {
        return Ok(());
    }
    // A runtime loan live at the end of a predecessor but not at a block's start dies on entry.
    let mut dies_on_entry: Vec<Vec<usize>> = vec![Vec::new(); nb];
    for b in 0..nb {
        if holds_in[b].is_none() {
            continue;
        }
        for succ in successors(&body.blocks[b].term) {
            let succ = succ as usize;
            for &k in &runtime {
                if end_live[b].contains(k) && !start_live[succ].contains(k) && !dies_on_entry[succ].contains(&k) {
                    dies_on_entry[succ].push(k);
                }
            }
        }
    }
    let created: Vec<((usize, usize), usize)> = bc.created.iter().filter(|(_, &l)| is_rt(l)).map(|(&key, &l)| (key, l)).collect();
    let mutable: HashMap<usize, bool> = runtime.iter().map(|&k| (k, matches!(bc.loans[k].origin, Origin::Gc(true)))).collect();
    let spans: HashMap<usize, Span> = runtime.iter().map(|&k| (k, bc.loans[k].span)).collect();
    insert_releases(body, info, &runtime, &created, &mutable, &spans, &dies_on_entry, &dies_after);
    Ok(())
}

/// Runtime loans live before a statement (or created by it) that are dead after it.
fn deaths(before: &Bits, created: Option<&usize>, after: &Bits, is_rt: &dyn Fn(usize) -> bool) -> Vec<usize> {
    let mut all = before.clone();
    if let Some(&k) = created {
        all.insert(k);
    }
    all.iter().filter(|&l| is_rt(l) && !after.contains(l)).collect()
}

/// Gives each `Gc` borrow a payload copy and a held flag, and releases it where its last holder
/// dies and before every return.
#[allow(clippy::too_many_arguments)]
fn insert_releases(
    body: &mut Body,
    info: &TypeInfo,
    runtime: &[usize],
    created: &[((usize, usize), usize)],
    mutable: &HashMap<usize, bool>,
    spans: &HashMap<usize, Span>,
    dies_on_entry: &[Vec<usize>],
    dies_after: &[Vec<Vec<usize>>],
) {
    let mut ptr_of: HashMap<usize, LocalId> = HashMap::new();
    let mut held_of: HashMap<usize, LocalId> = HashMap::new();
    let mut target_of: HashMap<(usize, usize), (usize, Place)> = HashMap::new();
    let unit = body.locals.len() as LocalId;
    body.locals.push(Local { name: String::new(), ty: Type::unit() });
    for &(key, k) in created {
        let Statement::Assign(target, _, _) = &body.blocks[key.0].stmts[key.1] else { unreachable!() };
        let ty = place_type(info, body, target);
        target_of.insert(key, (k, target.clone()));
        ptr_of.insert(k, body.locals.len() as LocalId);
        body.locals.push(Local { name: "gc_borrow".into(), ty });
        held_of.insert(k, body.locals.len() as LocalId);
        body.locals.push(Local { name: "gc_borrow_held".into(), ty: Type::con("Bool") });
    }
    let set = |flag: LocalId, v: bool, span: Span| Statement::Assign(Place::local(flag), Rvalue::Use(Operand::Const(Const::Bool(v))), span);
    let release = |k: usize, body: &Body| -> Vec<Statement> {
        let p = ptr_of[&k];
        let pointee = body.locals[p as usize].ty.as_ref().unwrap().1.clone();
        let call = Rvalue::Call(Callee::Def { name: "Gc::release".into(), targs: vec![pointee] }, vec![Operand::local(p), Operand::Const(Const::Bool(mutable[&k]))]);
        vec![Statement::Assign(Place::local(unit), call, spans[&k]), set(held_of[&k], false, spans[&k])]
    };
    let mut next = body.blocks.len() as BlockId;
    let mut chunks = Vec::new();
    for (b, bb) in body.blocks.iter().enumerate() {
        let mut em = Emit { chunks: vec![], cur_id: b as BlockId, cur: vec![], next };
        if b == 0 {
            for &k in runtime {
                em.cur.push(set(held_of[&k], false, spans[&k]));
            }
        }
        for &k in &dies_on_entry[b] {
            em.guarded(held_of[&k], release(k, body));
        }
        for (si, s) in bb.stmts.iter().enumerate() {
            em.cur.push(s.clone());
            if let Some((k, target)) = target_of.get(&(b, si)) {
                em.cur.push(Statement::Assign(Place::local(ptr_of[k]), Rvalue::Use(Operand::Place(target.clone())), spans[k]));
                em.cur.push(set(held_of[k], true, spans[k]));
            }
            for &k in dies_after[b].get(si).map(|v| v.as_slice()).unwrap_or(&[]) {
                em.guarded(held_of[&k], release(k, body));
            }
        }
        if matches!(bb.term, Terminator::Return) {
            for &k in runtime {
                em.guarded(held_of[&k], release(k, body));
            }
        }
        next = em.next;
        chunks.extend(em.finish(bb.term.clone()));
    }
    let mut blocks: Vec<BasicBlock> = (0..next).map(|_| BasicBlock { stmts: vec![], term: Terminator::Unreachable }).collect();
    for (id, stmts, term) in chunks {
        blocks[id as usize] = BasicBlock { stmts, term };
    }
    body.blocks = blocks;
}

/// At `Return` every local's storage ends while `_0` lives on in the caller.
fn check_return(bc: &Bc, ret_loans: &Bits, bb: &BasicBlock) -> Result<(), Diagnostic> {
    let span = bb.stmts.iter().rev().find_map(|s| match s {
        Statement::Assign(p, _, sp) if p.local == 0 && p.proj.is_empty() => Some(*sp),
        _ => None,
    });
    let elided = bc.info.elided.get(&bc.body.name).map(|&i| i as LocalId + 1);
    for l in ret_loans.iter() {
        match &bc.loans[l].origin {
            Origin::Place(p, _) if !p.proj.contains(&Proj::Deref) => {
                let x = bc.name(&Place::local(p.local));
                return Err(Diagnostic::new(bc.loans[l].span, format!("`{x}` does not live long enough; the returned value borrows it")));
            }
            Origin::Gc(_) => {
                return Err(Diagnostic::new(span.unwrap_or_default(), "cannot return a reference obtained from a `Gc` borrow; its runtime borrow ends here"));
            }
            Origin::Entry(param) if Some(*param) != elided => {
                let span = span.unwrap_or_default();
                if *param == 1 && matches!(bc.info.globals.get(&bc.body.name).map(|g| &g.kind), Some(GlobalKind::Closure { .. })) {
                    return Err(Diagnostic::new(span, "cannot return a reference to a captured variable"));
                }
                let who = bc.name(&Place::local(*param));
                let msg = match elided {
                    Some(e) => format!("returned reference must borrow from `{}`", bc.name(&Place::local(e))),
                    None => format!("cannot return a value that borrows `{who}`; return an owned value instead"),
                };
                return Err(Diagnostic::new(span, msg));
            }
            _ => {}
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::lex;
    use crate::parser::parse;
    use crate::types::check as typecheck;

    fn run(s: &str) -> Result<(), Diagnostic> {
        let prelude = include_str!("../std/prelude.rush");
        let mut id = 0;
        let mut p = parse(lex(prelude).unwrap(), &mut id).unwrap();
        p.items.extend(parse(lex(s).unwrap(), &mut id).unwrap().items);
        crate::derive::expand(&mut p, &mut id)?;
        let info = typecheck(&p)?;
        let mut bodies = lower(&p, &info)?;
        crate::ownck::check_and_insert_drops(&mut bodies, &info)?;
        check(&mut bodies, &info)
    }

    fn ok(s: &str) {
        if let Err(d) = run(s) {
            panic!("rejected: {}\n{s}", d.msg);
        }
    }

    fn err(s: &str) -> String {
        run(s).expect_err(s).msg
    }

    const P: &str = "struct P\n  name: String\n  age: Int\nend\nimpl P\n  def set(&mut self, a: Int)\n    @age = a\n  end\n  def name_ref(&self) -> &String\n    &@name\n  end\nend\nstruct Words\n  first: &String\n  rest: &String\nend\n";

    fn prog(main: &str) -> String {
        format!("{P}def main\n{main}end\n")
    }

    #[test]
    fn accepts_nll_and_disjoint_and_two_phase() {
        ok(&prog("  let mut x = 1\n  let r = &mut x\n  *r = 2\n  x = 3\n  ()\n"));
        ok(&prog("  let mut p = P { name: \"a\", age: 1 }\n  let a = &mut p.age\n  let n = &p.name\n  *a = 2\n  puts(n)\n"));
        ok(&prog("  let mut p = P { name: \"a\", age: 1 }\n  p.set(p.age + 1)\n  ()\n"));
        ok(&prog("  let mut p = P { name: \"a\", age: 1 }\n  let n = p.name_ref\n  puts(n)\n  p.set(3)\n  ()\n"));
    }

    #[test]
    fn accepts_reborrows_returns_and_borrowing_structs() {
        ok(&format!("def bump(r: &mut Int)\n  *r = *r + 1\nend\ndef twice(r: &mut Int)\n  bump(r)\n  bump(r)\nend\n{}", prog("  ()\n")));
        ok(&format!("def first(s: &String) -> &String\n  s\nend\ndef pick(s: &String) -> Words\n  Words {{ first: s, rest: s }}\nend\n{}", prog("  let s = int_to_s(1)\n  let w = pick(&s)\n  puts(w.first)\n")));
        ok(&prog("  let mut i = 0\n  let s = int_to_s(1)\n  while i < 3\n    let r = &s\n    puts(r)\n    i += 1\n  end\n"));
    }

    #[test]
    fn rejects_conflicts() {
        assert_eq!(err(&prog("  let mut x = 1\n  let r = &mut x\n  let y = x\n  *r = 2\n  ()\n")), "cannot use `x` because it is mutably borrowed");
        assert_eq!(err(&prog("  let mut x = 1\n  let r = &x\n  let m = &mut x\n  puts(&int_to_s(*r))\n  ()\n")), "cannot borrow `x` as mutable because it is already borrowed");
        assert_eq!(err(&prog("  let mut x = 1\n  let m = &mut x\n  let r = &x\n  *m = 2\n  ()\n")), "cannot borrow `x` as shared because it is mutably borrowed");
        assert_eq!(err(&prog("  let mut x = 1\n  let r = &x\n  x = 2\n  puts(&int_to_s(*r))\n")), "cannot assign to `x` because it is borrowed");
        assert_eq!(err(&prog("  let s = int_to_s(1)\n  let r = &s\n  let t = s\n  puts(r)\n")), "cannot move out of `s` because it is borrowed");
        assert_eq!(err(&prog("  let mut p = P { name: \"a\", age: 1 }\n  let n = p.name_ref\n  p.set(3)\n  puts(n)\n")), "cannot borrow `p` as mutable because it is already borrowed");
    }

    #[test]
    fn rejects_references_outliving_their_target() {
        assert_eq!(err(&format!("def f(a: &String) -> Words\n  let s = int_to_s(1)\n  Words {{ first: &s, rest: a }}\nend\n{}", prog("  ()\n"))), "`s` does not live long enough");
        let inner = prog("  let s = int_to_s(1)\n  let mut w = Words { first: &s, rest: &s }\n  if true\n    let t = int_to_s(2)\n    w = Words { first: &t, rest: &t }\n  end\n  puts(w.first)\n");
        assert_eq!(err(&inner), "`t` does not live long enough");
        assert_eq!(err(&format!("def f(a: &String, n: Int) -> &String\n  let s = int_to_s(n)\n  &s\nend\n{}", prog("  ()\n"))), "`s` does not live long enough");
    }

    #[test]
    fn rejects_values_stored_behind_parameters() {
        let msg = "cannot store a borrowed value behind `out`; it may outlive the borrow";
        assert_eq!(err(&format!("def f(out: &mut Option[&String])\n  let s = int_to_s(1)\n  *out = Some(&s)\nend\n{}", prog("  ()\n"))), msg);
        assert_eq!(err(&format!("def f(out: &mut Option[&String], s: &String)\n  *out = Some(s)\nend\n{}", prog("  ()\n"))), msg);
    }

    #[test]
    fn gc_borrows_cannot_be_returned_or_overlap_across_iterations() {
        let ret = format!("def name(g: &Gc[P]) -> &String
  &g.borrow.name
end
{}", prog("  ()
"));
        assert_eq!(err(&ret), "cannot return a reference obtained from a `Gc` borrow; its runtime borrow ends here");
        let lp = prog("  let g = Gc.new(1)
  let mut last = g.borrow
  let mut i = 0
  while i < 2
    let c = g.borrow
    puts(&int_to_s(*last))
    last = c
    i += 1
  end
");
        assert_eq!(err(&lp), "this `Gc` borrow is still in use from an earlier loop iteration");
        ok(&prog("  let g = Gc.new(1)
  let mut i = 0
  while i < 2
    let c = g.borrow
    puts(&int_to_s(*c))
    i += 1
  end
  let m = g.borrow_mut
  *m = 2
"));
    }

    #[test]
    fn generic_calls_tie_results_and_mut_arguments_to_all_borrows() {
        let set = "def set[T](o: &mut Option[T], v: T)\n  *o = Some(v)\nend\n";
        let src = format!("{set}{}", prog("  let mut o = None\n  if true\n    let t = int_to_s(1)\n    set(&mut o, &t)\n  end\n  case o\n  in Some(r) then puts(r)\n  in None then ()\n  end\n"));
        assert_eq!(err(&src), "`t` does not live long enough");
    }

    const FNS: &str = "def each_to(n: Int, f: &(Int -> Unit))\n  let mut i = 1\n  while i <= n\n    f(i)\n    i += 1\n  end\nend\n\
                       def keep(f: Int -> Int) -> Int -> Int\n  f\nend\ndef add(a: Int, b: Int) -> Int\n  a + b\nend\n\
                       def len_plus(s: &String, n: Int) -> Int\n  n\nend\n";

    fn fns(rest: &str) -> String {
        format!("{FNS}{rest}")
    }

    #[test]
    fn accepts_closures_used_within_their_borrows() {
        // The mutable capture ends at the closure's last use.
        ok(&fns("def main\n  let mut total = 0\n  let f = { |i: Int| total += i }\n  f(1)\n  f(2)\n  puts(&int_to_s(total))\nend\n"));
        ok(&fns("def main\n  let mut total = 0\n  let mut k = 0\n  while k < 3\n    each_to(3) { |i| total += i }\n    k += 1\n  end\n  puts(&int_to_s(total))\nend\n"));
        // Owned function values leave their function.
        ok(&fns("def adder(k: Int) -> Int -> Int\n  move { |x| x + k }\nend\ndef inc -> Int -> Int\n  add(1)\nend\ndef main\n  let a = adder(1)\n  let b = keep(inc)\n  ()\nend\n"));
        // A `move` closure nested in another copies `Copy` captures out of the outer
        // environment, so the inner value borrows nothing and can be returned.
        ok(&fns("def nested(base: Int) -> Int -> Int -> Int\n  move { |a| move { |b| base + a + b } }\nend\ndef main\n  ()\nend\n"));
        // A captured `&mut` is reborrowed for the closure's life, then usable again.
        ok(&fns("def bump(r: &mut Int) -> Int\n  let f = { || *r = *r + 1 }\n  f()\n  f()\n  *r\nend\ndef main\n  let mut x = 1\n  bump(&mut x)\n  ()\nend\n"));
        assert_eq!(
            err(&fns("def bump(r: &mut Int) -> Int\n  let f = { || *r = *r + 1 }\n  let v = *r\n  f()\n  v\nend\ndef main\n  ()\nend\n")),
            "cannot use `*r` because it is mutably borrowed"
        );
        // A closure may return a borrow of its one reference parameter.
        ok(&fns("def main\n  let f = { |s: &String| s }\n  let t = \"a\"\n  puts(f(&t))\nend\n"));
    }

    #[test]
    fn rejects_uses_that_conflict_with_a_live_closure() {
        assert_eq!(
            err(&fns("def main\n  let mut total = 0\n  let f = { |i: Int| total += i }\n  let x = total\n  f(1)\nend\n")),
            "cannot use `total` because it is mutably borrowed"
        );
    }

    #[test]
    fn rejects_borrowing_function_values_that_could_escape() {
        let msg = "function value borrows `total` and cannot be passed as an owned function; use `move` or take `&(Int -> Int)`";
        assert_eq!(err(&fns("def main\n  let total = 1\n  let f = { |i: Int| i + total }\n  keep(*f)\n  ()\nend\n")), msg);
        let d = run(&fns("def main\n  let total = 1\n  let f = { |i: Int| i + total }\n  let g = Gc.new(*f)\n  ()\nend\n")).unwrap_err();
        assert_eq!(d.msg, "function value borrows `total` and cannot be passed as an owned function; use `move` or take `&(Int -> Int)`");
        assert_eq!(d.notes[0].1, "`total` is borrowed here");
        // A borrowing closure copied out of its reference cannot be returned either.
        assert_eq!(
            err(&fns("def f -> Int -> Int\n  let t = 1\n  let g = { |x: Int| x + t }\n  *g\nend\ndef main\n  ()\nend\n")),
            "borrowing closure does not live long enough; use `move` to give it its own environment"
        );
        // A partial application holding a parameter's borrow.
        assert_eq!(
            err(&fns("def f(s: &String) -> Int -> Int\n  len_plus(s)\nend\ndef main\n  ()\nend\n")),
            "cannot return a value that borrows `s`; return an owned value instead"
        );
    }

    #[test]
    fn closure_bodies_cannot_move_or_return_their_captures() {
        assert_eq!(
            err(&fns("def main\n  let s = \"a\"\n  let f = move { || s }\n  ()\nend\n")),
            "cannot move captured `s` out of a closure; clone it instead"
        );
        assert_eq!(
            err(&fns("def take(s: String)\n  ()\nend\ndef main\n  let s = \"a\"\n  let f = { || take(s) }\n  ()\nend\n")),
            "cannot move captured `s` out of a closure; clone it instead"
        );
        assert_eq!(
            err(&fns("def main\n  let name = \"a\"\n  let f = { |s: &String| &name }\n  ()\nend\n")),
            "cannot return a reference to a captured variable"
        );
    }
}
