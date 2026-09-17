use std::collections::HashMap;
use std::fmt;

use crate::ast::*;
use crate::diag::{Diagnostic, Span};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Var(u32),
    Con(String, Vec<Type>),
    Fn(Box<Type>, Box<Type>),
}

impl Type {
    pub fn con(n: &str) -> Type {
        Type::Con(n.to_string(), vec![])
    }
    pub fn unit() -> Type {
        Type::con("Unit")
    }
    /// `func(&[A, B], R)` is `A -> B -> R`. `func(&[], R)` is `R`.
    pub fn func(params: &[Type], ret: Type) -> Type {
        params.iter().rev().fold(ret, |acc, p| Type::Fn(Box::new(p.clone()), Box::new(acc)))
    }
    /// Peels exactly `n` parameters off a curried function type.
    pub fn uncurry_n(&self, n: usize) -> (Vec<Type>, Type) {
        let mut ps = Vec::new();
        let mut t = self;
        for _ in 0..n {
            match t {
                Type::Fn(a, b) => {
                    ps.push((**a).clone());
                    t = b;
                }
                _ => panic!("uncurry_n: not enough parameters in {self}"),
            }
        }
        (ps, t.clone())
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Type::Var(v) => write!(f, "?{v}"),
            Type::Con(n, args) if args.is_empty() => write!(f, "{n}"),
            Type::Con(n, args) => {
                write!(f, "{n}[")?;
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{a}")?;
                }
                write!(f, "]")
            }
            Type::Fn(a, b) => match **a {
                Type::Fn(..) => write!(f, "({a}) -> {b}"),
                _ => write!(f, "{a} -> {b}"),
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Global {
    pub ty: Type,
    pub n_params: usize,
    pub is_extern: bool,
}

#[derive(Debug, Default)]
pub struct TypeInfo {
    pub expr_types: HashMap<ExprId, Type>,
    pub globals: HashMap<String, Global>,
}

struct Infer {
    subst: Vec<Option<Type>>,
}

fn occurs(v: u32, t: &Type) -> bool {
    match t {
        Type::Var(x) => *x == v,
        Type::Con(_, args) => args.iter().any(|a| occurs(v, a)),
        Type::Fn(a, b) => occurs(v, a) || occurs(v, b),
    }
}

impl Infer {
    fn fresh(&mut self) -> Type {
        self.subst.push(None);
        Type::Var(self.subst.len() as u32 - 1)
    }
    fn resolve(&self, t: &Type) -> Type {
        match t {
            Type::Var(v) => match &self.subst[*v as usize] {
                Some(t2) => self.resolve(t2),
                None => t.clone(),
            },
            Type::Con(n, args) => Type::Con(n.clone(), args.iter().map(|a| self.resolve(a)).collect()),
            Type::Fn(a, b) => Type::Fn(Box::new(self.resolve(a)), Box::new(self.resolve(b))),
        }
    }
    fn unify(&mut self, expected: &Type, found: &Type, span: Span) -> Result<(), Diagnostic> {
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

struct Checker {
    inf: Infer,
    globals: HashMap<String, Global>,
    /// Innermost scope last. Value is (type, mutable).
    scopes: Vec<HashMap<String, (Type, bool)>>,
    expr_types: HashMap<ExprId, Type>,
    ret_ty: Type,
}

const BUILTIN_TYPES: &[&str] = &["Int", "Float", "Bool", "String", "Unit"];

fn is_ground(t: &Type) -> bool {
    match t {
        Type::Var(_) => false,
        Type::Con(_, args) => args.iter().all(is_ground),
        Type::Fn(a, b) => is_ground(a) && is_ground(b),
    }
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

impl Checker {
    fn from_ast(&self, t: &TypeExpr) -> Result<Type, Diagnostic> {
        let TypeExpr::Name(name, args, span) = t;
        let name = match name.as_str() {
            "i64" => "Int",
            "f64" => "Float",
            n => n,
        };
        if !BUILTIN_TYPES.contains(&name) {
            return Err(Diagnostic::new(*span, format!("unknown type `{name}`")));
        }
        if !args.is_empty() {
            return Err(Diagnostic::new(*span, format!("type `{name}` takes no type arguments")));
        }
        Ok(Type::con(name))
    }

    fn lookup(&self, name: &str) -> Option<(Type, bool)> {
        for s in self.scopes.iter().rev() {
            if let Some(v) = s.get(name) {
                return Some(v.clone());
            }
        }
        self.globals.get(name).map(|g| (g.ty.clone(), false))
    }

    fn record(&mut self, e: &Expr, t: Type) -> Type {
        self.expr_types.insert(e.id, t.clone());
        t
    }

    fn block(&mut self, b: &Block) -> Result<Type, Diagnostic> {
        self.scopes.push(HashMap::new());
        let mut last = Type::unit();
        for (i, s) in b.stmts.iter().enumerate() {
            match s {
                Stmt::Let { name, mutable, init, .. } => {
                    let t = self.expr(init)?;
                    self.scopes.last_mut().unwrap().insert(name.clone(), (t, *mutable));
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

    /// Arithmetic operands must be Int or Float. An unresolved operand defaults to Int.
    fn numeric(&mut self, t: &Type, span: Span) -> Result<(), Diagnostic> {
        match self.inf.resolve(t) {
            Type::Var(_) => self.inf.unify(&Type::con("Int"), t, span),
            Type::Con(n, _) if n == "Int" || n == "Float" => Ok(()),
            other => Err(Diagnostic::new(span, format!("expected Int or Float, found {other}"))),
        }
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
                None => return Err(Diagnostic::new(e.span, format!("unknown variable `{n}`"))),
            },
            ExprKind::Unary(UnOp::Neg, x) => {
                let t = self.expr(x)?;
                self.numeric(&t, x.span)?;
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
                        Type::con("Bool")
                    }
                    BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                        self.inf.unify(&ta, &tb, b.span)?;
                        self.numeric(&ta, a.span)?;
                        Type::con("Bool")
                    }
                    _ => {
                        self.inf.unify(&ta, &tb, b.span)?;
                        self.numeric(&ta, a.span)?;
                        ta
                    }
                }
            }
            ExprKind::Call(f, args) => {
                let mut ft = self.expr(f)?;
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
                        _ => {
                            let name = match &f.kind {
                                ExprKind::Var(n) => n.clone(),
                                _ => "expression".to_string(),
                            };
                            return Err(Diagnostic::new(e.span, format!("too many arguments: `{name}` takes {i}")));
                        }
                    }
                }
                ft
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
                    None => {
                        self.inf.unify(&Type::unit(), &tt, last_span(then, then.span))?;
                    }
                }
                tt
            }
            ExprKind::While { cond, body } => {
                let ct = self.expr(cond)?;
                self.inf.unify(&Type::con("Bool"), &ct, cond.span)?;
                self.block(body)?;
                Type::unit()
            }
            ExprKind::Assign(lhs, rhs) => {
                let ExprKind::Var(name) = &lhs.kind else {
                    return Err(Diagnostic::new(lhs.span, "assignment target must be a variable"));
                };
                let (lt, mutable) = match self.lookup(name) {
                    Some(v) => v,
                    None => return Err(Diagnostic::new(lhs.span, format!("unknown variable `{name}`"))),
                };
                if !mutable {
                    return Err(Diagnostic::new(lhs.span, format!("cannot assign twice to immutable variable `{name}`")));
                }
                self.record(lhs, lt.clone());
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
}

pub fn check(prog: &Program) -> Result<TypeInfo, Diagnostic> {
    let mut cx = Checker {
        inf: Infer { subst: vec![] },
        globals: HashMap::new(),
        scopes: vec![],
        expr_types: HashMap::new(),
        ret_ty: Type::unit(),
    };
    for item in &prog.items {
        let (d, is_extern) = match item {
            Item::Def(d) => (d, false),
            Item::Extern(d) => (d, true),
        };
        let mut params = Vec::new();
        for p in &d.params {
            params.push(match &p.ty {
                Some(t) => cx.from_ast(t)?,
                None => cx.inf.fresh(),
            });
        }
        let ret = match &d.ret {
            Some(t) => cx.from_ast(t)?,
            None if is_extern => Type::unit(),
            None => cx.inf.fresh(),
        };
        if cx.globals.contains_key(&d.name) {
            return Err(Diagnostic::new(d.span, format!("duplicate definition of `{}`", d.name)));
        }
        cx.globals.insert(d.name.clone(), Global { ty: Type::func(&params, ret), n_params: params.len(), is_extern });
    }
    for item in &prog.items {
        let Item::Def(d) = item else { continue };
        let (params, ret) = cx.globals[&d.name].ty.uncurry_n(d.params.len());
        let mut scope = HashMap::new();
        for (p, t) in d.params.iter().zip(&params) {
            scope.insert(p.name.clone(), (t.clone(), false));
        }
        cx.scopes.push(scope);
        cx.ret_ty = ret.clone();
        let body_ty = cx.block(&d.body)?;
        cx.inf.unify(&ret, &body_ty, last_span(&d.body, d.span))?;
        cx.scopes.pop();
    }
    if !cx.globals.contains_key("main") {
        return Err(Diagnostic::new(Span::default(), "no `main` function defined"));
    }
    let mut info = TypeInfo::default();
    for item in &prog.items {
        let d = match item {
            Item::Def(d) | Item::Extern(d) => d,
        };
        let mut g = cx.globals[&d.name].clone();
        g.ty = cx.inf.resolve(&g.ty);
        let (params, ret) = g.ty.uncurry_n(g.n_params);
        for (p, t) in d.params.iter().zip(&params) {
            if !is_ground(t) {
                return Err(Diagnostic::new(
                    p.span,
                    format!("cannot infer the type of parameter `{}`; add an annotation", p.name),
                ));
            }
        }
        if !is_ground(&ret) {
            return Err(Diagnostic::new(d.span, format!("cannot infer the return type of `{}`; add an annotation", d.name)));
        }
        info.globals.insert(d.name.clone(), g);
    }
    for (id, t) in &cx.expr_types {
        info.expr_types.insert(*id, cx.inf.resolve(t));
    }
    Ok(info)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::lex;
    use crate::parser::parse;

    fn check_src(s: &str) -> Result<TypeInfo, Diagnostic> {
        let prelude = "extern \"C\" def puts(s: String) -> Unit\nextern \"C\" def int_to_s(v: Int) -> String\n";
        let mut id = 0;
        let mut p = parse(lex(prelude).unwrap(), &mut id).unwrap();
        p.items.extend(parse(lex(s).unwrap(), &mut id).unwrap().items);
        check(&p)
    }

    fn err(s: &str) -> String {
        check_src(s).unwrap_err().msg
    }

    #[test]
    fn display() {
        assert_eq!(Type::func(&[Type::con("Int"), Type::con("Bool")], Type::unit()).to_string(), "Int -> Bool -> Unit");
        let hof = Type::func(&[Type::func(&[Type::con("Int")], Type::con("Int"))], Type::con("Int"));
        assert_eq!(hof.to_string(), "(Int -> Int) -> Int");
        assert_eq!(Type::Con("List".into(), vec![Type::con("Int")]).to_string(), "List[Int]");
    }

    #[test]
    fn infers_recursive_function_with_annotations() {
        let info = check_src(
            "def fib(n: Int) -> Int\n  if n < 2\n    n\n  else\n    fib(n - 1) + fib(n - 2)\n  end\nend\ndef main\n  puts(int_to_s(fib(5)))\nend\n",
        )
        .unwrap();
        assert_eq!(info.globals["fib"].ty.to_string(), "Int -> Int");
        assert_eq!(info.globals["fib"].n_params, 1);
        assert_eq!(info.globals["main"], Global { ty: Type::unit(), n_params: 0, is_extern: false });
        assert!(info.globals["puts"].is_extern);
    }

    #[test]
    fn infers_unannotated_parameters_from_use() {
        let info = check_src("def inc(x)\n  x + 1\nend\ndef main\n  inc(2)\n  ()\nend\n").unwrap();
        assert_eq!(info.globals["inc"].ty.to_string(), "Int -> Int");
    }

    #[test]
    fn records_expression_types() {
        let info = check_src("def main\n  let x = 2.5 * 2.0\n  puts(\"a\")\nend\n").unwrap();
        let mut types: Vec<String> = info.expr_types.values().map(|t| t.to_string()).collect();
        types.sort();
        types.dedup();
        assert_eq!(types, vec!["Float", "String", "String -> Unit", "Unit"]);
    }

    #[test]
    fn mismatch_in_binary() {
        assert_eq!(err("def main\n  let x = 1 + true\nend\n"), "type mismatch: expected Int, found Bool");
    }

    #[test]
    fn if_branches_must_agree() {
        assert_eq!(
            err("def main\n  let x = if true\n    1\n  else\n    \"s\"\n  end\nend\n"),
            "type mismatch: expected Int, found String"
        );
    }

    #[test]
    fn if_without_else_is_unit() {
        assert_eq!(err("def main\n  let x = if true\n    1\n  end\nend\n"), "type mismatch: expected Unit, found Int");
    }

    #[test]
    fn condition_must_be_bool() {
        assert_eq!(err("def main\n  if 1\n    ()\n  end\nend\n"), "type mismatch: expected Bool, found Int");
    }

    #[test]
    fn assign_to_immutable() {
        assert_eq!(err("def main\n  let x = 1\n  x = 2\nend\n"), "cannot assign twice to immutable variable `x`");
    }

    #[test]
    fn assign_to_mutable_ok() {
        check_src("def main\n  let mut x = 1\n  x = 2\nend\n").unwrap();
    }

    #[test]
    fn unknown_variable() {
        assert_eq!(err("def main\n  y\nend\n"), "unknown variable `y`");
    }

    #[test]
    fn too_many_arguments() {
        assert_eq!(err("def main\n  puts(\"a\", \"b\")\nend\n"), "too many arguments: `puts` takes 1");
    }

    #[test]
    fn return_type_checked() {
        assert_eq!(
            err("def f() -> Int\n  return \"s\"\nend\ndef main\n  f\nend\n"),
            "type mismatch: expected Int, found String"
        );
    }

    #[test]
    fn missing_main() {
        assert_eq!(err("def f\n  1\nend\n"), "no `main` function defined");
    }

    #[test]
    fn unknown_type_name() {
        assert_eq!(err("def f(x: Strin) -> Int\n  1\nend\ndef main\n  ()\nend\n"), "unknown type `Strin`");
    }

    #[test]
    fn unconstrained_parameter_is_an_error() {
        assert_eq!(
            err("def f(x)\n  1\nend\ndef main\n  ()\nend\n"),
            "cannot infer the type of parameter `x`; add an annotation"
        );
    }
}
