//! Monomorphization: instantiates generic bodies reachable from `main` and resolves trait calls.

use std::collections::{HashMap, HashSet};

use crate::diag::{Diagnostic, Span};
use crate::mir::*;
use crate::types::{match_pattern, subst, GlobalKind, Type, TypeInfo};

/// C-identifier-safe encoding of a ground type.
pub fn mangle_type(t: &Type) -> String {
    match t {
        Type::Con(n, args) if args.is_empty() => n.clone(),
        Type::Con(n, args) => {
            let n = match n.as_str() {
                "&" => "Ref",
                "&mut" => "RefMut",
                other => other,
            };
            format!("{n}_L_{}_R", args.iter().map(mangle_type).collect::<Vec<_>>().join("__"))
        }
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

pub fn is_intrinsic(name: &str) -> bool {
    matches!(name, "Gc::new" | "Gc::borrow" | "Gc::borrow_mut" | "Gc::release")
}

fn type_size(t: &Type) -> usize {
    match t {
        Type::Con(_, args) => 1 + args.iter().map(type_size).sum::<usize>(),
        Type::Fn(a, b) => 1 + type_size(a) + type_size(b),
        _ => 1,
    }
}

struct Mono<'a> {
    info: &'a TypeInfo,
    by_name: HashMap<String, &'a Body>,
    queue: Vec<(String, Vec<Type>)>,
    done: HashSet<String>,
    counts: HashMap<String, usize>,
}

impl<'a> Mono<'a> {
    /// Resolves a trait method call on a concrete self type to (global name, type args).
    fn resolve_trait(&self, trait_name: &str, method: &str, self_ty: &Type) -> Result<(String, Vec<Type>), Diagnostic> {
        // Impls for references fall back to the pointee, as the checker allows.
        let mut ty = self_ty.clone();
        loop {
            for imp in &self.info.impls {
                if imp.trait_name.as_deref() != Some(trait_name) {
                    continue;
                }
                let mut map = HashMap::new();
                if !match_pattern(&imp.self_ty, &ty, &mut map) {
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
                return Ok((format!("{trait_name}::{method}"), vec![ty.clone()]));
            }
            match ty.as_ref() {
                Some((_, inner)) => ty = inner.clone(),
                None => return Err(Diagnostic::new(Span::default(), format!("no instance of `{trait_name}` for `{self_ty}`"))),
            }
        }
    }

    fn request(&mut self, name: &str, targs: Vec<Type>) -> String {
        let mangled = mangle_fn(name, &targs);
        self.queue.push((name.to_string(), targs));
        mangled
    }

    fn callee(&mut self, c: &Callee, map: &HashMap<String, Type>) -> Result<Callee, Diagnostic> {
        Ok(match c {
            Callee::Extern(n) => Callee::Extern(n.clone()),
            Callee::Value => Callee::Value,
            Callee::Def { name, targs } => {
                let targs: Vec<Type> = targs.iter().map(|t| subst(t, map)).collect();
                if is_intrinsic(name) {
                    Callee::Def { name: name.clone(), targs }
                } else {
                    Callee::Def { name: self.request(name, targs), targs: vec![] }
                }
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
            captures: body.captures.clone(),
        };
        for bb in &body.blocks {
            let mut stmts = Vec::new();
            for s in &bb.stmts {
                let s = match s {
                    Statement::Drop(p, sp) => Statement::Drop(p.clone(), *sp),
                    Statement::StorageDead(l, sp) => Statement::StorageDead(*l, *sp),
                    Statement::Assign(place, rv, sp) => {
                        let rv = match rv {
                            Rvalue::Call(Callee::Value, _) | Rvalue::Aggregate(Agg::Fn { .. }, _) => {
                                return Err(Diagnostic::new(*sp, "function values are not supported in this version"));
                            }
                            Rvalue::Call(c, ops) => {
                                let c = self.callee(c, &map)?;
                                if let Callee::Def { name, targs } = &c {
                                    if name == "Gc::new" && self.info.contains_ref(&targs[0]) {
                                        return Err(Diagnostic::new(*sp, "cannot store a value holding references in `Gc`"));
                                    }
                                }
                                Rvalue::Call(c, ops.clone())
                            }
                            Rvalue::Aggregate(agg, ops) => {
                                let agg = match agg {
                                    Agg::Struct(t) => Agg::Struct(subst(t, &map)),
                                    Agg::Tuple(t) => Agg::Tuple(subst(t, &map)),
                                    Agg::Variant(t, i) => Agg::Variant(subst(t, &map), *i),
                                    Agg::Fn { .. } => unreachable!("rejected above"),
                                };
                                Rvalue::Aggregate(agg, ops.clone())
                            }
                            other => other.clone(),
                        };
                        Statement::Assign(place.clone(), rv, *sp)
                    }
                };
                stmts.push(s);
            }
            out.blocks.push(BasicBlock { stmts, term: bb.term.clone() });
        }
        Ok(out)
    }

    /// Requests the `Drop` impl of every type whose drop glue will call one.
    fn request_drop_impls(&mut self, bodies: &[Body]) {
        let mut seen: HashSet<Type> = HashSet::new();
        let mut work: Vec<Type> = Vec::new();
        for b in bodies {
            for l in &b.locals {
                work.push(l.ty.clone());
            }
            for bb in &b.blocks {
                for s in &bb.stmts {
                    if let Statement::Assign(_, Rvalue::Call(Callee::Def { name, targs }, _), _) = s {
                        if name == "Gc::new" {
                            work.extend(targs.iter().cloned());
                        }
                    }
                }
            }
        }
        while let Some(t) = work.pop() {
            let t = match t.as_ref() {
                Some((_, inner)) => inner.clone(),
                None => t,
            };
            let t = if t.is_gc() { if let Type::Con(_, a) = &t { a[0].clone() } else { t } } else { t };
            if !seen.insert(t.clone()) {
                continue;
            }
            let Type::Con(n, args) = &t else { continue };
            if let Some((id, map)) = self.info.impl_for("Drop", &t) {
                let imp = &self.info.impls[id];
                let global = imp.methods["drop"].clone();
                let targs: Vec<Type> = imp.generics.iter().map(|g| map[g].clone()).collect();
                self.request(&global, targs);
            }
            if let Some(s) = self.info.structs.get(n) {
                let map: HashMap<String, Type> = s.generics.iter().cloned().zip(args.iter().cloned()).collect();
                work.extend(s.fields.iter().map(|(_, ft)| subst(ft, &map)));
            } else if let Some(e) = self.info.enums.get(n) {
                let map: HashMap<String, Type> = e.generics.iter().cloned().zip(args.iter().cloned()).collect();
                work.extend(e.variants.iter().flat_map(|v| v.fields.iter()).map(|(_, ft)| subst(ft, &map)));
            } else if n == "Tuple" {
                work.extend(args.iter().cloned());
            }
        }
    }
}

pub fn monomorphize(bodies: Vec<Body>, info: &TypeInfo) -> Result<Vec<Body>, Diagnostic> {
    let by_name: HashMap<String, &Body> = bodies.iter().map(|b| (b.name.clone(), b)).collect();
    let mut m = Mono { info, by_name, queue: vec![("main".into(), vec![])], done: HashSet::new(), counts: HashMap::new() };
    let mut out = Vec::new();
    loop {
        let start = out.len();
        while let Some((name, targs)) = m.queue.pop() {
            let mangled = mangle_fn(&name, &targs);
            if !m.done.insert(mangled) {
                continue;
            }
            let c = m.counts.entry(name.clone()).or_insert(0);
            *c += 1;
            // Polymorphic recursion grows the instantiation types without bound.
            if *c > 200 || targs.iter().map(type_size).sum::<usize>() > 256 {
                return Err(Diagnostic::new(Span::default(), "polymorphic recursion is not supported"));
            }
            if matches!(info.globals[&name].kind, GlobalKind::Extern | GlobalKind::Intrinsic) {
                continue;
            }
            out.push(m.instantiate(&name, &targs)?);
        }
        m.request_drop_impls(&out[start..]);
        if m.queue.is_empty() {
            break;
        }
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
        crate::derive::expand(&mut p, &mut id)?;
        let info = check(&p)?;
        let mut bodies = lower(&p, &info)?;
        crate::ownck::check_and_insert_drops(&mut bodies, &info)?;
        monomorphize(bodies, &info)
    }

    #[test]
    fn gc_rejects_values_holding_references_even_through_generics() {
        let msg = "cannot store a value holding references in `Gc`";
        assert_eq!(mono_src("def main\n  let s = int_to_s(1)\n  let g = Gc.new(&s)\n  ()\nend\n").unwrap_err().msg, msg);
        let generic = "def wrap[T](x: T) -> Gc[T]\n  Gc.new(x)\nend\ndef main\n  let s = int_to_s(1)\n  let g = wrap(Some(&s))\n  ()\nend\n";
        assert_eq!(mono_src(generic).unwrap_err().msg, msg);
    }

    fn names(s: &str) -> Vec<String> {
        let mut n: Vec<String> = mono_src(s).unwrap().into_iter().map(|b| b.name).collect();
        n.sort();
        n
    }

    #[test]
    fn mangling() {
        assert_eq!(mangle_type(&Type::Con("Pair".into(), vec![Type::con("Int"), Type::tuple(vec![Type::con("Bool"), Type::con("String")])])), "Pair_L_Int__Tuple_L_Bool__String_R_R");
        assert_eq!(mangle_type(&Type::r#ref(true, Type::con("Int"))), "RefMut_L_Int_R");
        assert_eq!(mangle_fn("Show#3::to_s", &[Type::con("Int")]), "Show_3_to_s__Int");
        assert_eq!(mangle_fn("main", &[]), "main");
    }

    #[test]
    fn generic_def_instantiated_per_use_and_unused_generic_dropped() {
        let src = "def id[T](x: T) -> T\n  x\nend\ndef unused[T](x: T) -> T\n  x\nend\ndef main\n  id(1)\n  id(true)\n  ()\nend\n";
        assert_eq!(names(src), vec!["id__Bool", "id__Int", "main"]);
    }

    #[test]
    fn trait_call_resolves_to_impl_and_pulls_dependencies() {
        let src = "struct P\n  x: Int\nend\nimpl Show for P\n  def to_s(&self)\n    \"p\"\n  end\nend\ndef main\n  puts(\"#{Some(P { x: 1 })}\")\nend\n";
        let n = names(src);
        assert!(n.iter().any(|x| x.starts_with("Show_") && x.ends_with("_to_s__P")), "{n:?}");
        let bodies = mono_src(src).unwrap();
        assert!(bodies.iter().all(|b| b.locals.iter().all(|l| !l.ty.has_param())));
    }

    #[test]
    fn default_method_instantiated_with_self() {
        let src = "trait A\n  def a(&self) -> Int\n  def b(&self) -> Int\n    self.a + 1\n  end\nend\nstruct S\n  f: Int\nend\nimpl A for S\n  def a(&self)\n    self.f\n  end\nend\ndef main\n  S { f: 1 }.b\n  ()\nend\n";
        let n = names(src);
        assert!(n.contains(&"A_b__S".to_string()), "{n:?}");
    }

    #[test]
    fn polymorphic_recursion_error() {
        let src = "def f[T](x: T) -> Int\n  f((x, 1))\nend\ndef main\n  f(1)\n  ()\nend\n";
        assert_eq!(mono_src(src).unwrap_err().msg, "polymorphic recursion is not supported");
    }

    #[test]
    fn drop_impls_are_requested_for_droppable_types() {
        let src = "struct R\n  n: String\nend\nimpl Drop for R\n  def drop(&mut self)\n    puts(&@n)\n  end\nend\ndef main\n  let r = R { n: \"a\" }\n  let g = Gc.new(R { n: \"b\" })\n  ()\nend\n";
        let n = names(src);
        assert!(n.iter().any(|x| x.starts_with("Drop_") && x.ends_with("_drop")), "{n:?}");
    }

    #[test]
    fn intrinsics_keep_their_name_and_type_args() {
        let src = "def main\n  let g = Gc.new(1)\n  let v = g.borrow\n  ()\nend\n";
        let bodies = mono_src(src).unwrap();
        let main = bodies.iter().find(|b| b.name == "main").unwrap();
        let d = dump(main);
        assert!(d.contains("call Gc::new[Int]("), "{d}");
        assert!(d.contains("call Gc::borrow[Int]("), "{d}");
    }
}
