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
use crate::types::{Type, TypeInfo};

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
            Operand::Place(p) => holds[p.local as usize].clone(),
            Operand::Const(_) => Bits::new(self.n()),
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
                if self.info.contains_ref(target_ty) {
                    let key_name = match c {
                        Callee::Def { name, .. } | Callee::Extern(name) => name.clone(),
                        Callee::Trait { trait_name, method, .. } => format!("{trait_name}::{method}"),
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
                // Arguments may be stored behind a `&mut` argument whose pointee holds references.
                if let Rvalue::Call(_, ops) = rv {
                    for (i, op) in ops.iter().enumerate() {
                        let Operand::Place(p) = op else { continue };
                        let ty = place_type(self.info, self.body, p);
                        if let Some((true, inner)) = ty.as_ref() {
                            if self.info.contains_ref(inner) {
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
    let carries: Vec<bool> = body.locals.iter().map(|l| info.contains_ref(&l.ty)).collect();
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
        if bc.carries[l] {
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

    // Check every reachable block.
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
        for (si, s) in bb.stmts.iter().enumerate() {
            let mut live_loans = Bits::new(n);
            for (l, &is_live) in live_before[si].iter().enumerate() {
                if is_live {
                    live_loans.union(&h[l]);
                }
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
            bc.step(&mut h, (b, si), s)?;
        }
        if matches!(bb.term, Terminator::Return) {
            let _ = live_at_term;
            check_return(&bc, &h[0], bb)?;
        }
    }
    Ok(())
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
            Origin::Entry(param) if Some(*param) != elided => {
                let want = match elided {
                    Some(e) => bc.name(&Place::local(e)),
                    None => "a parameter".into(),
                };
                return Err(Diagnostic::new(span.unwrap_or_default(), format!("returned reference must borrow from `{want}`")));
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
    fn generic_calls_tie_results_and_mut_arguments_to_all_borrows() {
        let set = "def set[T](o: &mut Option[T], v: T)\n  *o = Some(v)\nend\n";
        let src = format!("{set}{}", prog("  let mut o = None\n  if true\n    let t = int_to_s(1)\n    set(&mut o, &t)\n  end\n  case o\n  in Some(r) then puts(r)\n  in None then ()\n  end\n"));
        assert_eq!(err(&src), "`t` does not live long enough");
    }
}
