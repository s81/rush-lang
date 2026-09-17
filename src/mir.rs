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
