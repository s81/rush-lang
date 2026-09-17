//! Collects structs, enums, traits, impls, and top-level defs into the type tables.

use std::collections::{HashMap, HashSet};

use super::infer::{BodyJob, Checker, Match};
use super::*;
use crate::ast::*;

fn generic_names(g: &Generics) -> Result<Vec<String>, Diagnostic> {
    let mut names = Vec::new();
    for p in &g.params {
        if names.contains(&p.name) {
            return Err(Diagnostic::new(p.span, format!("duplicate type parameter `{}`", p.name)));
        }
        names.push(p.name.clone());
    }
    Ok(names)
}

/// ADT names contained by value in `t`, including through type arguments.
fn contained_adts(t: &Type, adts: &HashMap<String, usize>, out: &mut Vec<String>) {
    match t {
        // References and Gc handles are pointers: no by-value containment.
        Type::Con(n, _) if n == "&" || n == "&mut" || n == "Gc" => {}
        Type::Con(n, args) => {
            if adts.contains_key(n) && !out.contains(n) {
                out.push(n.clone());
            }
            args.iter().for_each(|a| contained_adts(a, adts, out));
        }
        _ => {}
    }
}

/// Rejects references where Plan 3a cannot track them (fields and return types).
fn no_refs(t: &Type, span: Span) -> Result<(), Diagnostic> {
    match t {
        Type::Con(n, _) if n == "&" || n == "&mut" => Err(Diagnostic::new(span, "references in this position are not supported until Plan 3b")),
        Type::Con(_, args) => args.iter().try_for_each(|a| no_refs(a, span)),
        Type::Fn(a, b) => {
            no_refs(a, span)?;
            no_refs(b, span)
        }
        _ => Ok(()),
    }
}

impl<'a> Checker<'a> {
    fn check_bounds(&self, g: &Generics) -> Result<Vec<(String, String)>, Diagnostic> {
        let mut out = Vec::new();
        for p in &g.params {
            for b in &p.bounds {
                if !self.info.traits.contains_key(b) {
                    return Err(Diagnostic::new(p.span, format!("unknown trait `{b}`")));
                }
                out.push((p.name.clone(), b.clone()));
            }
        }
        Ok(out)
    }

    pub fn collect_types(&mut self) -> Result<(), Diagnostic> {
        self.adts.insert("Gc".into(), 1);
        for item in &self.prog.items {
            let (name, generics, span) = match item {
                Item::Struct(s) => (&s.name, &s.generics, s.span),
                Item::Enum(e) => (&e.name, &e.generics, e.span),
                _ => continue,
            };
            if self.adts.contains_key(name) || ["Int", "Float", "Bool", "String", "Unit", "Tuple"].contains(&name.as_str()) {
                return Err(Diagnostic::new(span, format!("duplicate type `{name}`")));
            }
            self.adts.insert(name.clone(), generics.params.len());
        }
        for item in &self.prog.items {
            match item {
                Item::Struct(s) => {
                    let generics = generic_names(&s.generics)?;
                    let env = TypeEnv { adts: &self.adts, generics: &generics, self_ty: None };
                    let mut fields = Vec::new();
                    for f in &s.fields {
                        if fields.iter().any(|(n, _)| n == &f.name) {
                            return Err(Diagnostic::new(f.span, format!("duplicate field `{}`", f.name)));
                        }
                        let ft = from_ast(&f.ty, &env)?;
                        no_refs(&ft, f.span)?;
                        fields.push((f.name.clone(), ft));
                    }
                    self.info.structs.insert(s.name.clone(), StructInfo { generics, fields, span: s.span });
                }
                Item::Enum(e) => {
                    let generics = generic_names(&e.generics)?;
                    let env = TypeEnv { adts: &self.adts, generics: &generics, self_ty: None };
                    let mut variants = Vec::new();
                    for (idx, v) in e.variants.iter().enumerate() {
                        if self.info.variant_names.contains_key(&v.name) || self.adts.contains_key(&v.name) {
                            return Err(Diagnostic::new(v.span, format!("duplicate variant `{}`", v.name)));
                        }
                        let mut fields: Vec<(Option<String>, Type)> = Vec::new();
                        match &v.fields {
                            VariantFields::Unit => {}
                            VariantFields::Tuple(tys) => {
                                for t in tys {
                                    let ft = from_ast(t, &env)?;
                                    no_refs(&ft, t.span())?;
                                    fields.push((None, ft));
                                }
                            }
                            VariantFields::Named(fs) => {
                                for f in fs {
                                    if fields.iter().any(|(n, _)| n.as_deref() == Some(&f.name)) {
                                        return Err(Diagnostic::new(f.span, format!("duplicate field `{}`", f.name)));
                                    }
                                    let ft = from_ast(&f.ty, &env)?;
                                    no_refs(&ft, f.span)?;
                                    fields.push((Some(f.name.clone()), ft));
                                }
                            }
                        }
                        let params: Vec<Type> = generics.iter().map(|g| Type::Param(g.clone())).collect();
                        let ctor_ty = Type::func(&fields.iter().map(|(_, t)| t.clone()).collect::<Vec<_>>(), Type::Con(e.name.clone(), params));
                        self.info.globals.insert(
                            v.name.clone(),
                            Global {
                                scheme: Scheme { vars: generics.clone(), bounds: vec![], ty: ctor_ty },
                                n_params: fields.len(),
                                kind: GlobalKind::Variant { enum_name: e.name.clone(), index: idx },
                            },
                        );
                        self.info.variant_names.insert(v.name.clone(), (e.name.clone(), idx));
                        variants.push(VariantInfo { name: v.name.clone(), fields });
                    }
                    self.info.enums.insert(e.name.clone(), EnumInfo { generics, variants, span: e.span });
                }
                _ => {}
            }
        }
        // Recursive types without indirection have infinite size.
        let mut graph: HashMap<String, Vec<String>> = HashMap::new();
        for (n, s) in &self.info.structs {
            let mut out = Vec::new();
            s.fields.iter().for_each(|(_, t)| contained_adts(t, &self.adts, &mut out));
            graph.insert(n.clone(), out);
        }
        for (n, e) in &self.info.enums {
            let mut out = Vec::new();
            e.variants.iter().flat_map(|v| v.fields.iter()).for_each(|(_, t)| contained_adts(t, &self.adts, &mut out));
            graph.insert(n.clone(), out);
        }
        let mut names: Vec<&String> = graph.keys().collect();
        names.sort();
        for start in names {
            let mut stack = vec![start.clone()];
            let mut seen = HashSet::new();
            while let Some(n) = stack.pop() {
                for next in &graph[&n] {
                    if next == start {
                        let span = self.info.structs.get(start).map(|s| s.span).unwrap_or_else(|| self.info.enums[start].span);
                        return Err(Diagnostic::new(span, format!("recursive type `{start}` has infinite size")));
                    }
                    if seen.insert(next.clone()) {
                        stack.push(next.clone());
                    }
                }
            }
        }
        Ok(())
    }

    /// Converts a method header. `self_ty` is `Self` for traits or the impl type.
    /// Returns (params including self, ret).
    fn method_sig(&self, d: &Def, generics: &[String], self_ty: &Type, required: Option<(&[Type], &Type)>, where_: &str) -> Result<(Vec<Type>, Type), Diagnostic> {
        let env = TypeEnv { adts: &self.adts, generics, self_ty: Some(self_ty) };
        if d.self_param.is_none() {
            return Err(Diagnostic::new(d.span, format!("{where_} method `{}` must take `self`", d.name)));
        }
        let self_arg = match d.self_param.unwrap() {
            SelfKind::Value => self_ty.clone(),
            SelfKind::Ref => Type::r#ref(false, self_ty.clone()),
            SelfKind::RefMut => Type::r#ref(true, self_ty.clone()),
        };
        let mut params = vec![self_arg];
        for (i, p) in d.params.iter().enumerate() {
            match (&p.ty, required) {
                (Some(t), _) => params.push(from_ast(t, &env)?),
                (None, Some((req, _))) if i + 1 < req.len() => params.push(req[i + 1].clone()),
                (None, _) => return Err(Diagnostic::new(p.span, format!("{where_} method parameter `{}` must be annotated", p.name))),
            }
        }
        let ret = match (&d.ret, required) {
            (Some(t), _) => from_ast(t, &env)?,
            (None, Some((_, r))) => r.clone(),
            (None, None) => Type::unit(),
        };
        no_refs(&ret, d.ret.as_ref().map(|t| t.span()).unwrap_or(d.span))?;
        Ok((params, ret))
    }

    /// Converts an associated function header (no `self`); everything must be annotated.
    fn assoc_sig(&self, d: &Def, generics: &[String], self_ty: &Type) -> Result<(Vec<Type>, Type), Diagnostic> {
        let env = TypeEnv { adts: &self.adts, generics, self_ty: Some(self_ty) };
        let mut params = Vec::new();
        for p in &d.params {
            match &p.ty {
                Some(t) => params.push(from_ast(t, &env)?),
                None => return Err(Diagnostic::new(p.span, format!("associated function parameter `{}` must be annotated", p.name))),
            }
        }
        let ret = match &d.ret {
            Some(t) => from_ast(t, &env)?,
            None => Type::unit(),
        };
        no_refs(&ret, d.ret.as_ref().map(|t| t.span()).unwrap_or(d.span))?;
        Ok((params, ret))
    }

    /// Registers the compiler-implemented `Gc` type: `Gc.new`, `g.borrow`, `g.borrow_mut`.
    fn register_gc(&mut self) {
        let t = Type::Param("T".into());
        let gc = Type::Con("Gc".into(), vec![t.clone()]);
        let mut add = |name: &str, ty: Type| {
            self.info.globals.insert(name.to_string(), Global { scheme: Scheme { vars: vec!["T".into()], bounds: vec![], ty }, n_params: 1, kind: GlobalKind::Intrinsic });
        };
        add("Gc::new", Type::func(&[t.clone()], gc.clone()));
        add("Gc::borrow", Type::func(&[Type::r#ref(false, gc.clone())], Type::r#ref(false, t.clone())));
        add("Gc::borrow_mut", Type::func(&[Type::r#ref(false, gc.clone())], Type::r#ref(true, t.clone())));
        let id = self.info.impls.len();
        let mut methods = HashMap::new();
        methods.insert("borrow".to_string(), "Gc::borrow".to_string());
        methods.insert("borrow_mut".to_string(), "Gc::borrow_mut".to_string());
        let mut assoc = HashMap::new();
        assoc.insert("new".to_string(), "Gc::new".to_string());
        self.info.impls.push(ImplInfo { id, generics: vec!["T".into()], bounds: vec![], trait_name: None, self_ty: gc, methods, assoc, span: Span::default() });
    }

    pub fn collect_traits(&mut self) -> Result<(), Diagnostic> {
        for item in &self.prog.items {
            let Item::Trait(t) = item else { continue };
            if self.info.traits.contains_key(&t.name) {
                return Err(Diagnostic::new(t.span, format!("duplicate trait `{}`", t.name)));
            }
            self.info.traits.insert(t.name.clone(), TraitInfo { supertraits: t.supertraits.clone(), methods: HashMap::new(), span: t.span });
        }
        for item in &self.prog.items {
            let Item::Trait(t) = item else { continue };
            for s in &t.supertraits {
                if !self.info.traits.contains_key(s) {
                    return Err(Diagnostic::new(t.span, format!("unknown trait `{s}`")));
                }
            }
            let self_param = Type::Param("Self".into());
            let mut methods = HashMap::new();
            for m in &t.methods {
                if methods.contains_key(&m.name) {
                    return Err(Diagnostic::new(m.span, format!("duplicate method `{}`", m.name)));
                }
                let mgen = generic_names(&m.generics)?;
                let mut vars = vec!["Self".to_string()];
                vars.extend(mgen.iter().cloned());
                let mut bounds = vec![("Self".to_string(), t.name.clone())];
                bounds.extend(self.check_bounds(&m.generics)?);
                let (params, ret) = self.method_sig(m, &mgen, &self_param, None, "trait")?;
                let scheme = Scheme { vars: vars.clone(), bounds: bounds.clone(), ty: Type::func(&params, ret) };
                let has_default = !m.body.stmts.is_empty();
                if has_default {
                    let global = format!("{}::{}", t.name, m.name);
                    self.info.globals.insert(global.clone(), Global { scheme: scheme.clone(), n_params: params.len(), kind: GlobalKind::TraitDefault { trait_name: t.name.clone() } });
                    self.jobs.push(BodyJob { global, def: m, generics: vars.clone(), bounds: bounds.clone(), self_ty: Some(self_param.clone()), generalize: false });
                }
                methods.insert(m.name.clone(), MethodSig { scheme, n_params: params.len(), has_default });
            }
            self.info.traits.get_mut(&t.name).unwrap().methods = methods;
        }
        Ok(())
    }

    pub fn collect_impls(&mut self) -> Result<(), Diagnostic> {
        self.register_gc();
        for item in &self.prog.items {
            let Item::Impl(imp) = item else { continue };
            let id = self.info.impls.len();
            let generics = generic_names(&imp.generics)?;
            let bounds = self.check_bounds(&imp.generics)?;
            let self_ty = from_ast(&imp.self_ty, &TypeEnv { adts: &self.adts, generics: &generics, self_ty: None })?;
            if let Some(tn) = &imp.trait_name {
                if !self.info.traits.contains_key(tn) {
                    return Err(Diagnostic::new(imp.span, format!("unknown trait `{tn}`")));
                }
            } else if self_ty.head().map_or(true, |h| !self.adts.contains_key(h)) {
                return Err(Diagnostic::new(imp.self_ty.span(), "inherent impls are only allowed on structs and enums"));
            }
            let prefix = match &imp.trait_name {
                Some(t) => t.clone(),
                None => self_ty.head().unwrap().to_string(),
            };
            let mut methods = HashMap::new();
            let mut assoc = HashMap::new();
            for m in &imp.methods {
                if methods.contains_key(&m.name) || assoc.contains_key(&m.name) {
                    return Err(Diagnostic::new(m.span, format!("duplicate method `{}`", m.name)));
                }
                let mgen = generic_names(&m.generics)?;
                let mut all_gen = generics.clone();
                all_gen.extend(mgen.iter().cloned());
                let mut all_bounds = bounds.clone();
                all_bounds.extend(self.check_bounds(&m.generics)?);
                if m.self_param.is_none() {
                    if imp.trait_name.is_some() {
                        return Err(Diagnostic::new(m.span, format!("trait impl method `{}` must take `self`", m.name)));
                    }
                    let (params, ret) = self.assoc_sig(m, &all_gen, &self_ty)?;
                    let global = format!("{prefix}#{id}::{}", m.name);
                    self.info.globals.insert(global.clone(), Global { scheme: Scheme { vars: all_gen.clone(), bounds: all_bounds.clone(), ty: Type::func(&params, ret) }, n_params: params.len(), kind: GlobalKind::ImplMethod { impl_id: id } });
                    self.jobs.push(BodyJob { global: global.clone(), def: m, generics: all_gen, bounds: all_bounds, self_ty: Some(self_ty.clone()), generalize: false });
                    assoc.insert(m.name.clone(), global);
                    continue;
                }
                let (params, ret) = match &imp.trait_name {
                    Some(tn) => {
                        let Some(sig) = self.info.traits[tn].methods.get(&m.name).cloned() else {
                            return Err(Diagnostic::new(m.span, format!("method `{}` is not a member of trait `{tn}`", m.name)));
                        };
                        if sig.scheme.vars.len() - 1 != mgen.len() {
                            return Err(Diagnostic::new(m.span, format!("method `{}` declares {} type parameters, trait requires {}", m.name, mgen.len(), sig.scheme.vars.len() - 1)));
                        }
                        let mut map = HashMap::new();
                        map.insert("Self".to_string(), self_ty.clone());
                        for (tv, iv) in sig.scheme.vars.iter().skip(1).zip(&mgen) {
                            map.insert(tv.clone(), Type::Param(iv.clone()));
                        }
                        let req = subst(&sig.scheme.ty, &map);
                        let (req_params, req_ret) = req.uncurry_n(sig.n_params);
                        if m.params.len() + 1 != sig.n_params {
                            return Err(Diagnostic::new(m.span, format!("method `{}` takes {} parameters, trait requires {}", m.name, m.params.len(), sig.n_params - 1)));
                        }
                        let (params, ret) = self.method_sig(m, &all_gen, &self_ty, Some((&req_params, &req_ret)), "impl")?;
                        let declared = Type::func(&params, ret.clone());
                        if self.inf.unify(&req, &declared, m.span).is_err() {
                            return Err(Diagnostic::new(m.span, format!("method `{}` has type `{declared}`, trait requires `{req}`", m.name)));
                        }
                        (params, ret)
                    }
                    None => self.method_sig(m, &all_gen, &self_ty, None, "inherent")?,
                };
                let global = format!("{prefix}#{id}::{}", m.name);
                self.info.globals.insert(global.clone(), Global { scheme: Scheme { vars: all_gen.clone(), bounds: all_bounds.clone(), ty: Type::func(&params, ret) }, n_params: params.len(), kind: GlobalKind::ImplMethod { impl_id: id } });
                self.jobs.push(BodyJob { global: global.clone(), def: m, generics: all_gen, bounds: all_bounds, self_ty: Some(self_ty.clone()), generalize: false });
                methods.insert(m.name.clone(), global);
            }
            if let Some(tn) = &imp.trait_name {
                let mut required: Vec<&String> = self.info.traits[tn].methods.iter().filter(|(n, s)| !s.has_default && !methods.contains_key(*n)).map(|(n, _)| n).collect();
                required.sort();
                if let Some(m) = required.first() {
                    return Err(Diagnostic::new(imp.span, format!("missing method `{m}` in impl of `{tn}` for `{self_ty}`")));
                }
            }
            self.info.impls.push(ImplInfo { id, generics, bounds, trait_name: imp.trait_name.clone(), self_ty, methods, assoc, span: imp.span });
        }
        // `Copy` requires every field to be `Copy` (impl generics bounded by `Copy` count).
        for imp in self.info.impls.clone() {
            if imp.trait_name.as_deref() != Some("Copy") {
                continue;
            }
            let Type::Con(head, targs) = &imp.self_ty else { continue };
            let param_copy = |p: &str| imp.bounds.iter().any(|(gp, tr)| gp == p && tr == "Copy");
            let fields: Vec<(String, Type)> = if let Some(s) = self.info.structs.get(head) {
                let map: HashMap<String, Type> = s.generics.iter().cloned().zip(targs.iter().cloned()).collect();
                s.fields.iter().map(|(n, t)| (n.clone(), subst(t, &map))).collect()
            } else if let Some(e) = self.info.enums.get(head) {
                let map: HashMap<String, Type> = e.generics.iter().cloned().zip(targs.iter().cloned()).collect();
                let mut out = Vec::new();
                for v in &e.variants {
                    for (i, (n, t)) in v.fields.iter().enumerate() {
                        out.push((n.clone().unwrap_or_else(|| format!("{}.{i}", v.name)), subst(t, &map)));
                    }
                }
                out
            } else {
                continue;
            };
            for (fname, fty) in fields {
                if !self.info.is_copy(&fty, &param_copy) {
                    return Err(Diagnostic::new(imp.span, format!("cannot derive `Copy` for `{head}`: field `{fname}` is not `Copy`")));
                }
            }
        }
        // Overlap: two impls of one trait whose self types unify (params as fresh vars).
        for i in 0..self.info.impls.len() {
            for j in i + 1..self.info.impls.len() {
                let (a, b) = (&self.info.impls[i], &self.info.impls[j]);
                if a.trait_name.is_none() || a.trait_name != b.trait_name {
                    continue;
                }
                let mut inf = super::infer::Infer { subst: vec![] };
                let fresh = |inf: &mut super::infer::Infer, imp: &ImplInfo| {
                    let map: HashMap<String, Type> = imp.generics.iter().map(|g| (g.clone(), inf.fresh())).collect();
                    subst(&imp.self_ty, &map)
                };
                let ta = fresh(&mut inf, a);
                let tb = fresh(&mut inf, b);
                if inf.unify(&ta, &tb, b.span).is_ok() {
                    return Err(Diagnostic::new(b.span, format!("overlapping instances of `{}` for `{}`", a.trait_name.as_ref().unwrap(), b.self_ty)));
                }
            }
        }
        // Supertraits must be implemented for the same self type.
        for imp in self.info.impls.clone() {
            let Some(tn) = &imp.trait_name else { continue };
            for s in &self.info.traits[tn].supertraits {
                if !matches!(self.find_impl(s, &imp.self_ty), Match::Yes(_)) {
                    return Err(Diagnostic::new(imp.span, format!("`{tn}` requires `{s}`, but `{}` does not implement `{s}`", imp.self_ty)));
                }
            }
        }
        // Inherent methods with the same name on overlapping self types.
        for i in 0..self.info.impls.len() {
            for j in i + 1..self.info.impls.len() {
                let (a, b) = (&self.info.impls[i], &self.info.impls[j]);
                if a.trait_name.is_some() || b.trait_name.is_some() || a.self_ty.head() != b.self_ty.head() {
                    continue;
                }
                if let Some(m) = a.methods.keys().find(|m| b.methods.contains_key(*m)) {
                    return Err(Diagnostic::new(b.span, format!("duplicate method `{m}` for `{}`", b.self_ty)));
                }
            }
        }
        Ok(())
    }

    pub fn collect_defs(&mut self) -> Result<(), Diagnostic> {
        for item in &self.prog.items {
            let (d, is_extern) = match item {
                Item::Def(d) => (d, false),
                Item::Extern(d) => (d, true),
                _ => continue,
            };
            if self.info.globals.contains_key(&d.name) {
                return Err(Diagnostic::new(d.span, format!("duplicate definition of `{}`", d.name)));
            }
            if d.self_param.is_some() {
                return Err(Diagnostic::new(d.span, "`self` is only allowed in methods inside `impl` or `trait`"));
            }
            let generics = generic_names(&d.generics)?;
            let bounds = self.check_bounds(&d.generics)?;
            let env = TypeEnv { adts: &self.adts, generics: &generics, self_ty: None };
            let mut params = Vec::new();
            let mut annotated = true;
            for p in &d.params {
                params.push(match &p.ty {
                    Some(t) => from_ast(t, &env)?,
                    None if is_extern => return Err(Diagnostic::new(p.span, "extern parameters must be annotated")),
                    None => {
                        annotated = false;
                        self.inf.fresh()
                    }
                });
            }
            let ret = match &d.ret {
                Some(t) => {
                    let r = from_ast(t, &env)?;
                    no_refs(&r, t.span())?;
                    r
                }
                None if is_extern => Type::unit(),
                None => {
                    annotated = false;
                    self.inf.fresh()
                }
            };
            let ty = Type::func(&params, ret);
            let generalize = !is_extern && !annotated && generics.is_empty();
            let scheme = if generalize { Scheme::mono(ty) } else { Scheme { vars: generics.clone(), bounds: bounds.clone(), ty } };
            let kind = if is_extern { GlobalKind::Extern } else { GlobalKind::Def };
            self.info.globals.insert(d.name.clone(), Global { scheme, n_params: params.len(), kind });
            if !is_extern {
                self.jobs.push(BodyJob { global: d.name.clone(), def: d, generics, bounds, self_ty: None, generalize });
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::super::infer::check_program;
    use super::*;
    use crate::lexer::lex;
    use crate::parser::parse;

    fn check_src(s: &str) -> Result<TypeInfo, Diagnostic> {
        let prelude = include_str!("../../std/prelude.rush");
        let mut id = 0;
        let mut p = parse(lex(prelude).unwrap(), &mut id).unwrap();
        p.items.extend(parse(lex(s).unwrap(), &mut id).unwrap().items);
        check_program(&p)
    }

    fn err(s: &str) -> String {
        check_src(s).unwrap_err().msg
    }

    const MAIN: &str = "def main\n  ()\nend\n";

    #[test]
    fn registers_struct_fields_and_variant_constructors() {
        let info = check_src(&format!("struct Pair[A, B]\n  first: A\n  second: B\nend\nenum Shape\n  Circle(Float)\n  Rect {{ w: Float, h: Float }}\n  Empty\nend\n{MAIN}")).unwrap();
        assert_eq!(info.structs["Pair"].fields[1], ("second".into(), Type::Param("B".into())));
        assert_eq!(info.globals["Circle"].scheme.ty.to_string(), "Float -> Shape");
        assert_eq!(info.globals["Rect"].scheme.ty.to_string(), "Float -> Float -> Shape");
        assert_eq!(info.enums["Shape"].variants[1].fields[0].0.as_deref(), Some("w"));
        assert_eq!(info.variant_names["Empty"], ("Shape".into(), 2));
    }

    #[test]
    fn duplicate_variant_across_enums() {
        assert_eq!(err(&format!("enum A\n  X\nend\nenum B\n  X\nend\n{MAIN}")), "duplicate variant `X`");
    }

    #[test]
    fn unknown_type_and_arity() {
        assert_eq!(err(&format!("struct S\n  f: Strin\nend\n{MAIN}")), "unknown type `Strin`");
        assert_eq!(err(&format!("struct S\n  f: Option[Int, Int]\nend\n{MAIN}")), "type `Option` takes 1 type arguments, found 2");
    }

    #[test]
    fn missing_method_in_impl() {
        assert_eq!(err(&format!("struct S\n  f: Int\nend\nimpl Show for S\nend\n{MAIN}")), "missing method `to_s` in impl of `Show` for `S`");
    }

    #[test]
    fn signature_mismatch_with_trait() {
        assert_eq!(err(&format!("struct S\n  f: Int\nend\nimpl Show for S\n  def to_s(&self) -> Int\n    1\n  end\nend\n{MAIN}")), "method `to_s` has type `&S -> Int`, trait requires `&S -> String`");
    }

    #[test]
    fn overlapping_instances() {
        assert_eq!(err(&format!("impl[T] Show for Option[T]\n  def to_s(&self)\n    \"x\"\n  end\nend\n{MAIN}")), "overlapping instances of `Show` for `Option[T]`");
    }

    #[test]
    fn recursive_type_error() {
        assert_eq!(err(&format!("enum Tree\n  Leaf\n  Node(Tree, Tree)\nend\n{MAIN}")), "recursive type `Tree` has infinite size");
        assert_eq!(err(&format!("struct A\n  b: Option[A]\nend\n{MAIN}")), "recursive type `A` has infinite size");
    }

    #[test]
    fn supertrait_impl_required() {
        assert_eq!(err(&format!("trait Named: Show\n  def name(&self) -> String\nend\nstruct S\n  f: Int\nend\nimpl Named for S\n  def name(&self)\n    \"s\"\n  end\nend\n{MAIN}")), "`Named` requires `Show`, but `S` does not implement `Show`");
    }

    #[test]
    fn self_outside_trait_or_impl() {
        assert_eq!(err(&format!("def f(x: Self) -> Int\n  1\nend\n{MAIN}")), "`Self` is only allowed inside a trait or impl");
    }

    #[test]
    fn inherent_method_needs_annotations() {
        assert_eq!(err(&format!("struct S\n  f: Int\nend\nimpl S\n  def g(&self)\n    1\n  end\nend\n{MAIN}")), "type mismatch: expected Unit, found Int");
        assert_eq!(err(&format!("struct S\n  f: Int\nend\nimpl S\n  def g(&self, x) -> Int\n    1\n  end\nend\n{MAIN}")), "inherent method parameter `x` must be annotated");
    }

    #[test]
    fn not_a_member_of_trait() {
        assert_eq!(err(&format!("struct S\n  f: Int\nend\nimpl Show for S\n  def to_s(&self)\n    \"\"\n  end\n  def extra(&self) -> Int\n    1\n  end\nend\n{MAIN}")), "method `extra` is not a member of trait `Show`");
    }
}
