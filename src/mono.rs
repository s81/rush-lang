//! Monomorphization: instantiates generic bodies reachable from `main` and resolves trait calls.

use std::collections::HashMap;

use crate::diag::{Diagnostic, Span};
use crate::mir::*;
use crate::types::{subst, GlobalKind, Type, TypeInfo};

/// C-identifier-safe encoding of a ground type.
pub fn mangle_type(t: &Type) -> String {
    match t {
        Type::Con(n, args) if args.is_empty() => n.clone(),
        Type::Con(n, args) => format!("{n}_L_{}_R", args.iter().map(mangle_type).collect::<Vec<_>>().join("__")),
        Type::Fn(a, b) => format!("Fn_L_{}__{}_R", mangle_type(a), mangle_type(b)),
        Type::Param(p) => panic!("mangle_type: unexpected type parameter {p}"),
        Type::Var(v) => panic!("mangle_type: unexpected inference variable ?{v}"),
    }
}

/// Mangled function name: `f`, `f__Int__String`, `Show_3_to_s__Point`.
pub fn mangle_fn(name: &str, targs: &[Type]) -> String {
    let base: String = name.chars().map(|c| if c.is_ascii_alphanumeric() || c == '_' { c } else { '_' }).collect();
    let base = base.replace("__", "_");
    if targs.is_empty() {
        base
    } else {
        format!("{base}__{}", targs.iter().map(mangle_type).collect::<Vec<_>>().join("__"))
    }
}

fn type_size(t: &Type) -> usize {
    match t {
        Type::Con(_, args) => 1 + args.iter().map(type_size).sum::<usize>(),
        Type::Fn(a, b) => 1 + type_size(a) + type_size(b),
        _ => 1,
    }
}

fn match_pattern(pat: &Type, ty: &Type, map: &mut HashMap<String, Type>) -> bool {
    match (pat, ty) {
        (Type::Param(p), _) => match map.get(p) {
            Some(bound) => bound == ty,
            None => {
                map.insert(p.clone(), ty.clone());
                true
            }
        },
        (Type::Con(n, a), Type::Con(m, b)) => n == m && a.len() == b.len() && a.iter().zip(b).all(|(x, y)| match_pattern(x, y, map)),
        (Type::Fn(a1, r1), Type::Fn(a2, r2)) => match_pattern(a1, a2, map) && match_pattern(r1, r2, map),
        _ => false,
    }
}

struct Mono<'a> {
    info: &'a TypeInfo,
    by_name: HashMap<String, &'a Body>,
    queue: Vec<(String, Vec<Type>)>,
    done: HashMap<String, ()>,
    counts: HashMap<String, usize>,
}

impl<'a> Mono<'a> {
    /// Resolves a trait method call on a concrete self type to (global name, type args).
    fn resolve_trait(&self, trait_name: &str, method: &str, self_ty: &Type) -> Result<(String, Vec<Type>), Diagnostic> {
        for imp in &self.info.impls {
            if imp.trait_name.as_deref() != Some(trait_name) {
                continue;
            }
            let mut map = HashMap::new();
            if !match_pattern(&imp.self_ty, self_ty, &mut map) {
                continue;
            }
            if let Some(global) = imp.methods.get(method) {
                let n_vars = self.info.globals[global].scheme.vars.len();
                if n_vars != imp.generics.len() {
                    return Err(Diagnostic::new(Span::default(), format!("generic trait methods are not supported in this version (`{method}`)")));
                }
                let targs = imp.generics.iter().map(|g| map[g].clone()).collect();
                return Ok((global.clone(), targs));
            }
            let global = format!("{trait_name}::{method}");
            return Ok((global, vec![self_ty.clone()]));
        }
        Err(Diagnostic::new(Span::default(), format!("no instance of `{trait_name}` for `{self_ty}`")))
    }

    fn request(&mut self, name: &str, targs: Vec<Type>) -> String {
        let mangled = mangle_fn(name, &targs);
        self.queue.push((name.to_string(), targs));
        mangled
    }

    fn callee(&mut self, c: &Callee, map: &HashMap<String, Type>) -> Result<Callee, Diagnostic> {
        Ok(match c {
            Callee::Extern(n) => Callee::Extern(n.clone()),
            Callee::Def { name, targs } => {
                let targs: Vec<Type> = targs.iter().map(|t| subst(t, map)).collect();
                Callee::Def { name: self.request(name, targs), targs: vec![] }
            }
            Callee::Trait { trait_name, method, self_ty } => {
                let self_ty = subst(self_ty, map);
                let (global, targs) = self.resolve_trait(trait_name, method, &self_ty)?;
                Callee::Def { name: self.request(&global, targs), targs: vec![] }
            }
        })
    }

    fn instantiate(&mut self, name: &str, targs: &[Type]) -> Result<Body, Diagnostic> {
        let body = *self.by_name.get(name).unwrap_or_else(|| panic!("mono: no body for {name}"));
        let vars = &self.info.globals[name].scheme.vars;
        assert_eq!(vars.len(), targs.len(), "mono: arity mismatch for {name}");
        let map: HashMap<String, Type> = vars.iter().cloned().zip(targs.iter().cloned()).collect();
        let mut out = Body {
            name: mangle_fn(name, targs),
            locals: body.locals.iter().map(|l| Local { name: l.name.clone(), ty: subst(&l.ty, &map) }).collect(),
            n_params: body.n_params,
            blocks: Vec::new(),
        };
        for bb in &body.blocks {
            let mut stmts = Vec::new();
            for Statement::Assign(place, rv) in &bb.stmts {
                let rv = match rv {
                    Rvalue::Call(c, ops) => Rvalue::Call(self.callee(c, &map)?, ops.clone()),
                    Rvalue::Aggregate(agg, ops) => {
                        let agg = match agg {
                            Agg::Struct(t) => Agg::Struct(subst(t, &map)),
                            Agg::Tuple(t) => Agg::Tuple(subst(t, &map)),
                            Agg::Variant(t, i) => Agg::Variant(subst(t, &map), *i),
                        };
                        Rvalue::Aggregate(agg, ops.clone())
                    }
                    other => other.clone(),
                };
                stmts.push(Statement::Assign(place.clone(), rv));
            }
            out.blocks.push(BasicBlock { stmts, term: bb.term.clone() });
        }
        Ok(out)
    }
}

pub fn monomorphize(bodies: Vec<Body>, info: &TypeInfo) -> Result<Vec<Body>, Diagnostic> {
    let by_name: HashMap<String, &Body> = bodies.iter().map(|b| (b.name.clone(), b)).collect();
    let mut m = Mono { info, by_name, queue: vec![("main".into(), vec![])], done: HashMap::new(), counts: HashMap::new() };
    let mut out = Vec::new();
    while let Some((name, targs)) = m.queue.pop() {
        let mangled = mangle_fn(&name, &targs);
        if m.done.contains_key(&mangled) {
            continue;
        }
        m.done.insert(mangled, ());
        let c = m.counts.entry(name.clone()).or_insert(0);
        *c += 1;
        // Polymorphic recursion grows the instantiation types without bound.
        if *c > 200 || targs.iter().map(type_size).sum::<usize>() > 256 {
            return Err(Diagnostic::new(Span::default(), "polymorphic recursion is not supported"));
        }
        if matches!(info.globals[&name].kind, GlobalKind::Extern) {
            continue;
        }
        out.push(m.instantiate(&name, &targs)?);
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::lex;
    use crate::parser::parse;
    use crate::types::check;

    fn mono_src(s: &str) -> Result<Vec<Body>, Diagnostic> {
        let prelude = include_str!("../std/prelude.rush");
        let mut id = 0;
        let mut p = parse(lex(prelude).unwrap(), &mut id).unwrap();
        p.items.extend(parse(lex(s).unwrap(), &mut id).unwrap().items);
        let info = check(&p)?;
        let bodies = lower(&p, &info)?;
        monomorphize(bodies, &info)
    }

    fn names(s: &str) -> Vec<String> {
        let mut n: Vec<String> = mono_src(s).unwrap().into_iter().map(|b| b.name).collect();
        n.sort();
        n
    }

    #[test]
    fn mangling() {
        assert_eq!(mangle_type(&Type::Con("Pair".into(), vec![Type::con("Int"), Type::tuple(vec![Type::con("Bool"), Type::con("String")])])), "Pair_L_Int__Tuple_L_Bool__String_R_R");
        assert_eq!(mangle_fn("Show#3::to_s", &[Type::con("Int")]), "Show_3_to_s__Int");
        assert_eq!(mangle_fn("main", &[]), "main");
    }

    #[test]
    fn generic_def_instantiated_per_use_and_unused_generic_dropped() {
        let src = "def id[T](x: T) -> T\n  x\nend\ndef unused[T](x: T) -> T\n  x\nend\ndef main\n  id(1)\n  id(\"a\")\n  ()\nend\n";
        assert_eq!(names(src), vec!["id__Int", "id__String", "main"]);
        let bodies = mono_src(src).unwrap();
        let b = bodies.iter().find(|b| b.name == "id__String").unwrap();
        assert_eq!(b.locals[1].ty, Type::con("String"));
    }

    #[test]
    fn trait_call_resolves_to_impl_and_pulls_dependencies() {
        let src = "struct P\n  x: Int\nend\nimpl Show for P\n  def to_s(&self)\n    \"p\"\n  end\nend\ndef main\n  puts(\"#{Some(P { x: 1 })}\")\nend\n";
        let n = names(src);
        assert!(n.iter().any(|x| x.starts_with("Show_") && x.ends_with("_to_s__P")), "{n:?}");
        assert!(n.contains(&"Show_5_to_s__P".to_string()) || n.iter().any(|x| x.contains("_to_s__P")), "{n:?}");
        let bodies = mono_src(src).unwrap();
        let main = bodies.iter().find(|b| b.name == "main").unwrap();
        let calls: Vec<String> = main.blocks.iter().flat_map(|bb| bb.stmts.iter()).filter_map(|Statement::Assign(_, rv)| match rv {
            Rvalue::Call(Callee::Def { name, .. }, _) => Some(name.clone()),
            _ => None,
        }).collect();
        assert!(calls.iter().any(|c| c.starts_with("Show_5_to_s__P") || c.ends_with("_to_s__P")), "{calls:?}");
        assert!(bodies.iter().all(|b| b.locals.iter().all(|l| !l.ty.has_param())));
    }

    #[test]
    fn default_method_instantiated_with_self() {
        let src = "trait A\n  def a(&self) -> Int\n  def b(&self) -> Int\n    self.a + 1\n  end\nend\nstruct S\n  f: Int\nend\nimpl A for S\n  def a(&self)\n    self.f\n  end\nend\ndef main\n  S { f: 1 }.b\n  ()\nend\n";
        let n = names(src);
        assert!(n.contains(&"A_b__S".to_string()), "{n:?}");
        assert!(n.iter().any(|x| x.starts_with("A_") && x.ends_with("_a__S") == false && x.ends_with("_a")), "{n:?}");
    }

    #[test]
    fn polymorphic_recursion_error() {
        let src = "def f[T](x: T) -> Int\n  f((x, x))\nend\ndef main\n  f(1)\n  ()\nend\n";
        assert_eq!(mono_src(src).unwrap_err().msg, "polymorphic recursion is not supported");
    }
}
