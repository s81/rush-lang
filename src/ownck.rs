//! Ownership checking on the MIR: use after move, moves out of places, and drop insertion
//! with drop flags. Runs on generic bodies before monomorphization.

use std::collections::HashMap;

use crate::diag::{Diagnostic, Span};
use crate::mir::*;
use crate::types::{Type, TypeInfo};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum St {
    /// Holds no value (never initialized or moved out entirely).
    Dead,
    Live,
    /// Some fields were moved out by a pattern; the rest were dropped by the MIR.
    Partial,
}

/// May-states per local: a local can be in several states on different paths.
#[derive(Clone, PartialEq, Debug)]
struct State {
    live: Vec<bool>,
    dead: Vec<bool>,
    partial: Vec<bool>,
}

impl State {
    fn new(n: usize) -> State {
        State { live: vec![false; n], dead: vec![true; n], partial: vec![false; n] }
    }
    fn merge(&mut self, other: &State) -> bool {
        let mut changed = false;
        for i in 0..self.live.len() {
            for (a, b) in [(&mut self.live[i], other.live[i]), (&mut self.dead[i], other.dead[i]), (&mut self.partial[i], other.partial[i])] {
                if b && !*a {
                    *a = true;
                    changed = true;
                }
            }
        }
        changed
    }
    fn set(&mut self, l: usize, st: St) {
        self.live[l] = st == St::Live;
        self.dead[l] = st == St::Dead;
        self.partial[l] = st == St::Partial;
    }
}

struct Ck<'a> {
    info: &'a TypeInfo,
    body: &'a Body,
    copy_params: Vec<String>,
    /// Locals that own a non-Copy value, excluding the return slot.
    tracked: Vec<bool>,
    move_spans: HashMap<LocalId, Span>,
}

fn describe_place(body: &Body, p: &Place) -> String {
    let mut s = body.locals[p.local as usize].name.clone();
    if s.is_empty() {
        s = "value".into();
    }
    for pr in &p.proj {
        match pr {
            Proj::Field(i) | Proj::Downcast(_, i) => s = format!("{s}.{i}"),
            Proj::Deref => s = format!("*{s}"),
        }
    }
    s
}

impl<'a> Ck<'a> {
    fn is_copy(&self, t: &Type) -> bool {
        let cps = &self.copy_params;
        self.info.is_copy(t, &|p| cps.iter().any(|c| c == p))
    }

    fn name(&self, l: LocalId) -> String {
        let n = &self.body.locals[l as usize].name;
        if n.is_empty() || n == "_ret" { "value".to_string() } else { format!("`{n}`") }
    }

    /// Checks a read of a place; errors if its root may have been moved.
    fn read(&self, st: &State, p: &Place, span: Span) -> Result<(), Diagnostic> {
        let l = p.local as usize;
        if self.tracked[l] && (st.dead[l] || st.partial[l]) {
            return Err(Diagnostic::new(span, format!("use of moved value {}", self.name(p.local))));
        }
        Ok(())
    }

    /// A pattern binding reads one field of the scrutinee; other fields may already be moved.
    fn read_for_move_out(&self, st: &State, p: &Place, span: Span) -> Result<(), Diagnostic> {
        let l = p.local as usize;
        if self.tracked[l] && (st.dead[l] || (st.partial[l] && p.proj.is_empty())) {
            return Err(Diagnostic::new(span, format!("use of moved value {}", self.name(p.local))));
        }
        Ok(())
    }

    /// Effect of using an operand as a value: a move when the whole local is non-Copy.
    fn use_operand(&mut self, st: &mut State, op: &Operand, span: Span) -> Result<(), Diagnostic> {
        let Operand::Place(p) = op else { return Ok(()) };
        self.read(st, p, span)?;
        let ty = place_type(self.info, self.body, p);
        if self.is_copy(&ty) {
            return Ok(());
        }
        if p.proj.is_empty() {
            st.set(p.local as usize, St::Dead);
            self.move_spans.insert(p.local, span);
            return Ok(());
        }
        if p.proj.contains(&Proj::Deref) {
            return Err(Diagnostic::new(span, "cannot move out of a reference; use `.clone`"));
        }
        Err(Diagnostic::new(span, format!("cannot move out of `{}`; use `.clone`", describe_place(self.body, p))))
    }

    fn read_operand(&self, st: &State, op: &Operand, span: Span) -> Result<(), Diagnostic> {
        if let Operand::Place(p) = op {
            self.read(st, p, span)?;
        }
        Ok(())
    }

    /// Applies a statement to the state, reporting errors.
    fn step(&mut self, st: &mut State, s: &Statement) -> Result<(), Diagnostic> {
        match s {
            Statement::Drop(..) => Ok(()),
            Statement::Assign(target, rv, span) => {
                match rv {
                    Rvalue::Use(op) => self.use_operand(st, op, *span)?,
                    Rvalue::MoveOut(p) => {
                        self.read_for_move_out(st, p, *span)?;
                        let ty = place_type(self.info, self.body, p);
                        if !self.is_copy(&ty) {
                            if p.proj.contains(&Proj::Deref) {
                                return Err(Diagnostic::new(*span, "cannot move out of a reference; use `.clone`"));
                            }
                            let l = p.local as usize;
                            if self.tracked[l] {
                                st.set(l, if p.proj.is_empty() { St::Dead } else { St::Partial });
                                self.move_spans.insert(p.local, *span);
                            }
                        }
                    }
                    Rvalue::Ref(_, p) | Rvalue::Discriminant(p) => self.read(st, p, *span)?,
                    Rvalue::Binary(_, a, b) => {
                        self.read_operand(st, a, *span)?;
                        self.read_operand(st, b, *span)?;
                    }
                    Rvalue::Unary(_, a) => self.read_operand(st, a, *span)?,
                    Rvalue::Call(_, ops) | Rvalue::Aggregate(_, ops) => {
                        for op in ops {
                            self.use_operand(st, op, *span)?;
                        }
                    }
                }
                if target.proj.is_empty() {
                    st.set(target.local as usize, St::Live);
                } else {
                    self.read(st, target, *span)?;
                }
                Ok(())
            }
        }
    }
}

fn successors(t: &Terminator) -> Vec<BlockId> {
    match t {
        Terminator::Goto(b) => vec![*b],
        Terminator::If(_, a, b) => vec![*a, *b],
        Terminator::Return | Terminator::Unreachable => vec![],
    }
}

/// Emits a chain of blocks that replaces one original block.
struct Emit {
    chunks: Vec<(BlockId, Vec<Statement>, Terminator)>,
    cur_id: BlockId,
    cur: Vec<Statement>,
    next: BlockId,
}

impl Emit {
    fn alloc(&mut self) -> BlockId {
        let id = self.next;
        self.next += 1;
        id
    }
    /// `if flag then drop(place)`; continues in a fresh block.
    fn guarded_drop(&mut self, flag: LocalId, place: Place, span: Span) {
        let drop_bb = self.alloc();
        let cont_bb = self.alloc();
        let stmts = std::mem::take(&mut self.cur);
        self.chunks.push((self.cur_id, stmts, Terminator::If(Operand::local(flag), drop_bb, cont_bb)));
        self.chunks.push((drop_bb, vec![Statement::Drop(place, span)], Terminator::Goto(cont_bb)));
        self.cur_id = cont_bb;
    }
    fn finish(mut self, term: Terminator) -> Vec<(BlockId, Vec<Statement>, Terminator)> {
        let stmts = std::mem::take(&mut self.cur);
        self.chunks.push((self.cur_id, stmts, term));
        self.chunks
    }
}

/// Checks moves and inserts drops into every body.
pub fn check_and_insert_drops(bodies: &mut [Body], info: &TypeInfo) -> Result<(), Diagnostic> {
    for body in bodies.iter_mut() {
        check_body(body, info)?;
    }
    Ok(())
}

fn check_body(body: &mut Body, info: &TypeInfo) -> Result<(), Diagnostic> {
    let g = &info.globals[&body.name];
    let copy_params: Vec<String> = g.scheme.bounds.iter().filter(|(_, t)| info.trait_closure(t).iter().any(|x| x == "Copy")).map(|(p, _)| p.clone()).collect();
    let n = body.locals.len();
    let mut ck = Ck { info, body, copy_params, tracked: vec![false; n], move_spans: HashMap::new() };
    for (i, l) in body.locals.iter().enumerate() {
        ck.tracked[i] = i != 0 && !ck.is_copy(&l.ty);
    }
    // Forward dataflow for the entry state of each block.
    let mut entry: Vec<Option<State>> = vec![None; body.blocks.len()];
    let mut init = State::new(n);
    for i in 1..=body.n_params {
        init.set(i, St::Live);
    }
    entry[0] = Some(init);
    let mut work = vec![0u32];
    while let Some(b) = work.pop() {
        let mut st = entry[b as usize].clone().unwrap();
        for s in &body.blocks[b as usize].stmts {
            ck.step(&mut st, s)?;
        }
        for succ in successors(&body.blocks[b as usize].term) {
            match &mut entry[succ as usize] {
                None => {
                    entry[succ as usize] = Some(st.clone());
                    work.push(succ);
                }
                Some(e) => {
                    if e.merge(&st) {
                        work.push(succ);
                    }
                }
            }
        }
    }
    // Drop flags: one Bool per tracked local.
    let tracked: Vec<LocalId> = (0..n as LocalId).filter(|&i| ck.tracked[i as usize]).collect();
    let mut flag_of: HashMap<LocalId, LocalId> = HashMap::new();
    let mut locals = body.locals.clone();
    for &l in &tracked {
        let f = locals.len() as LocalId;
        locals.push(Local { name: format!("{}_live", body.locals[l as usize].name), ty: Type::con("Bool") });
        flag_of.insert(l, f);
    }
    let set_flag = |l: LocalId, v: bool, span: Span| Statement::Assign(Place::local(flag_of[&l]), Rvalue::Use(Operand::Const(Const::Bool(v))), span);
    let n_orig = body.blocks.len() as BlockId;
    let mut next = n_orig;
    let mut chunks: Vec<(BlockId, Vec<Statement>, Terminator)> = Vec::new();
    for (bi, bb) in body.blocks.iter().enumerate() {
        let Some(mut st) = entry[bi].clone() else {
            chunks.push((bi as BlockId, bb.stmts.clone(), bb.term.clone()));
            continue;
        };
        let mut em = Emit { chunks: vec![], cur_id: bi as BlockId, cur: vec![], next };
        let entry_span = bb.stmts.first().map(|s| match s {
            Statement::Assign(_, _, sp) | Statement::Drop(_, sp) => *sp,
        }).unwrap_or_default();
        if bi == 0 {
            for &l in &tracked {
                let live = l as usize >= 1 && l as usize <= body.n_params;
                em.cur.push(set_flag(l, live, entry_span));
            }
        }
        for s in &bb.stmts {
            match s {
                Statement::Assign(target, rv, span) => {
                    let moved: Vec<LocalId> = match rv {
                        Rvalue::Use(Operand::Place(p)) if p.proj.is_empty() && ck.tracked[p.local as usize] => vec![p.local],
                        Rvalue::MoveOut(p) if ck.tracked[p.local as usize] && !ck.is_copy(&place_type(ck.info, ck.body, p)) => vec![p.local],
                        Rvalue::Call(_, ops) | Rvalue::Aggregate(_, ops) => ops
                            .iter()
                            .filter_map(|o| match o {
                                Operand::Place(p) if p.proj.is_empty() && ck.tracked[p.local as usize] => Some(p.local),
                                _ => None,
                            })
                            .collect(),
                        _ => vec![],
                    };
                    let whole_tracked = target.proj.is_empty() && ck.tracked[target.local as usize];
                    let old_live = whole_tracked && (st.live[target.local as usize] || st.partial[target.local as usize]);
                    ck.step(&mut st, s)?;
                    if old_live {
                        em.guarded_drop(flag_of[&target.local], Place::local(target.local), *span);
                    }
                    em.cur.push(s.clone());
                    for m in moved {
                        em.cur.push(set_flag(m, false, *span));
                    }
                    if whole_tracked {
                        em.cur.push(set_flag(target.local, true, *span));
                    }
                }
                Statement::Drop(..) => {
                    ck.step(&mut st, s)?;
                    em.cur.push(s.clone());
                }
            }
        }
        if matches!(bb.term, Terminator::Return) {
            for &l in &tracked {
                em.guarded_drop(flag_of[&l], Place::local(l), entry_span);
            }
        }
        next = em.next;
        chunks.extend(em.finish(bb.term.clone()));
    }
    let mut blocks: Vec<BasicBlock> = (0..next).map(|_| BasicBlock { stmts: vec![], term: Terminator::Unreachable }).collect();
    for (id, stmts, term) in chunks {
        blocks[id as usize] = BasicBlock { stmts, term };
    }
    body.locals = locals;
    body.blocks = blocks;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::lex;
    use crate::parser::parse;
    use crate::types::check;

    fn run(s: &str) -> Result<Vec<Body>, Diagnostic> {
        let prelude = include_str!("../std/prelude.rush");
        let mut id = 0;
        let mut p = parse(lex(prelude).unwrap(), &mut id).unwrap();
        p.items.extend(parse(lex(s).unwrap(), &mut id).unwrap().items);
        crate::derive::expand(&mut p, &mut id)?;
        let info = check(&p)?;
        let mut bodies = lower(&p, &info)?;
        check_and_insert_drops(&mut bodies, &info)?;
        Ok(bodies)
    }

    fn err(s: &str) -> String {
        run(s).unwrap_err().msg
    }

    fn dump_fn(s: &str, name: &str) -> String {
        let bodies = run(s).unwrap();
        dump(bodies.iter().find(|b| b.name == name).unwrap())
    }

    #[test]
    fn use_after_move() {
        assert_eq!(err("def take(s: String) -> Int\n  1\nend\ndef main\n  let s = \"a\"\n  take(s)\n  take(s)\nend\n"), "use of moved value `s`");
    }

    #[test]
    fn conditional_move_is_tracked_by_flags() {
        let src = "def take(s: String) -> Unit\n  ()\nend\ndef main\n  let s = \"a\"\n  if true\n    take(s)\n  end\n  ()\nend\n";
        let d = dump_fn(src, "main");
        assert!(d.contains("_4 = true\n"), "{d}");
        assert!(d.contains("_4 = false\n"), "{d}");
        assert!(d.contains("if _4 then bb"), "{d}");
        assert!(d.contains("drop(_1)"), "{d}");
        assert_eq!(err("def take(s: String) -> Unit\n  ()\nend\ndef main\n  let s = \"a\"\n  if true\n    take(s)\n  end\n  take(s)\nend\n"), "use of moved value `s`");
    }

    #[test]
    fn reassignment_drops_old_value() {
        let d = dump_fn("def main\n  let mut s = \"a\"\n  s = \"b\"\n  ()\nend\n", "main");
        let first_drop = d.find("drop(_1)").unwrap();
        let second_assign = d.find("_1 = \"b\"").unwrap();
        assert!(first_drop < second_assign, "{d}");
    }

    #[test]
    fn copy_locals_are_untouched_and_params_dropped_at_exit() {
        let bodies = run("def f(s: String, n: Int) -> Int\n  n\nend\ndef main\n  ()\nend\n").unwrap();
        let f = bodies.iter().find(|b| b.name == "f").unwrap();
        assert!(f.locals.iter().any(|l| l.name == "s_live"));
        assert!(!f.locals.iter().any(|l| l.name == "n_live"));
        assert!(dump(f).contains("drop(_1)"));
    }

    #[test]
    fn move_out_of_field_and_reference() {
        assert_eq!(err("struct P\n  name: String\nend\ndef main\n  let p = P { name: \"a\" }\n  let n = p.name\n  ()\nend\n"), "cannot move out of `p.0`; use `.clone`");
        assert_eq!(err("def f(p: &String) -> String\n  *p\nend\ndef main\n  ()\nend\n"), "cannot move out of a reference; use `.clone`");
    }

    #[test]
    fn borrow_does_not_move_and_destructuring_partial_move() {
        run("def main\n  let s = \"a\"\n  puts(&s)\n  puts(&s)\nend\n").unwrap();
        assert_eq!(err("def main\n  let t = (\"a\", \"b\")\n  let (a, b) = t\n  let u = t\n  ()\nend\n"), "use of moved value `t`");
    }
}
