//! Types, schemes, declaration tables, and the entry point `check`.

mod decls;
mod exhaust;
mod infer;

use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::ast::{ExprId, PatId, Program, TypeExpr};
use crate::diag::{Diagnostic, Span};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    /// Inference variable.
    Var(u32),
    /// Rigid type parameter of the enclosing generic item.
    Param(String),
    /// Named type applied to arguments. Tuples are `Con("Tuple", ..)`; `Unit` is `Con("Unit", [])`.
    Con(String, Vec<Type>),
    /// Curried function type.
    Fn(Box<Type>, Box<Type>),
}

impl Type {
    pub fn con(n: &str) -> Type {
        Type::Con(n.to_string(), vec![])
    }
    pub fn unit() -> Type {
        Type::con("Unit")
    }
    pub fn tuple(items: Vec<Type>) -> Type {
        if items.is_empty() {
            Type::unit()
        } else {
            Type::Con("Tuple".into(), items)
        }
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
    pub fn r#ref(mutable: bool, t: Type) -> Type {
        Type::Con(if mutable { "&mut" } else { "&" }.into(), vec![t])
    }
    /// `Some((mutable, pointee))` for a reference type.
    pub fn as_ref(&self) -> Option<(bool, &Type)> {
        match self {
            Type::Con(n, args) if n == "&" => Some((false, &args[0])),
            Type::Con(n, args) if n == "&mut" => Some((true, &args[0])),
            _ => None,
        }
    }
    /// Strips all reference layers.
    pub fn peel(&self) -> &Type {
        let mut t = self;
        while let Some((_, inner)) = t.as_ref() {
            t = inner;
        }
        t
    }
    pub fn is_gc(&self) -> bool {
        matches!(self, Type::Con(n, _) if n == "Gc")
    }
    pub fn head(&self) -> Option<&str> {
        match self {
            Type::Con(n, _) => Some(n),
            _ => None,
        }
    }
    pub fn is_primitive(&self) -> bool {
        matches!(self.head(), Some("Int" | "Float" | "Bool" | "String" | "Unit" | "Symbol"))
    }
    pub fn has_var(&self) -> bool {
        match self {
            Type::Var(_) => true,
            Type::Param(_) => false,
            Type::Con(_, args) => args.iter().any(Type::has_var),
            Type::Fn(a, b) => a.has_var() || b.has_var(),
        }
    }
    pub fn has_param(&self) -> bool {
        match self {
            Type::Var(_) => false,
            Type::Param(_) => true,
            Type::Con(_, args) => args.iter().any(Type::has_param),
            Type::Fn(a, b) => a.has_param() || b.has_param(),
        }
    }
    /// Variables in first-occurrence order.
    pub fn vars(&self, out: &mut Vec<u32>) {
        match self {
            Type::Var(v) => {
                if !out.contains(v) {
                    out.push(*v);
                }
            }
            Type::Param(_) => {}
            Type::Con(_, args) => args.iter().for_each(|a| a.vars(out)),
            Type::Fn(a, b) => {
                a.vars(out);
                b.vars(out);
            }
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Type::Var(v) => write!(f, "?{v}"),
            Type::Param(p) => write!(f, "{p}"),
            Type::Con(n, args) if n == "&" || n == "&mut" => {
                let m = if n == "&" { "&" } else { "&mut " };
                match &args[0] {
                    Type::Fn(..) => write!(f, "{m}({})", args[0]),
                    a => write!(f, "{m}{a}"),
                }
            }
            Type::Con(n, args) if n == "Tuple" => {
                write!(f, "(")?;
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{a}")?;
                }
                write!(f, ")")
            }
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

/// Replaces `Param`s according to `map`. Params not in the map are left alone.
pub fn subst(t: &Type, map: &HashMap<String, Type>) -> Type {
    match t {
        Type::Var(_) => t.clone(),
        Type::Param(p) => map.get(p).cloned().unwrap_or_else(|| t.clone()),
        Type::Con(n, args) => Type::Con(n.clone(), args.iter().map(|a| subst(a, map)).collect()),
        Type::Fn(a, b) => Type::Fn(Box::new(subst(a, map)), Box::new(subst(b, map))),
    }
}

/// A polymorphic type. `vars` are `Param` names; `bounds` are `(param, trait)`.
#[derive(Debug, Clone, PartialEq)]
pub struct Scheme {
    pub vars: Vec<String>,
    pub bounds: Vec<(String, String)>,
    pub ty: Type,
}

impl Scheme {
    pub fn mono(ty: Type) -> Scheme {
        Scheme { vars: vec![], bounds: vec![], ty }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum GlobalKind {
    Def,
    Extern,
    /// Compiler-implemented (`Gc::new`, `Gc::borrow`, `Gc::borrow_mut`).
    Intrinsic,
    Variant { enum_name: String, index: usize },
    ImplMethod { impl_id: usize },
    TraitDefault { trait_name: String },
    /// A closure body; its scheme vars are the enclosing function's.
    Closure { parent: String },
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum CaptureMode {
    /// Borrowed `&`.
    Shared,
    /// Borrowed `&mut`; the body mutates the variable.
    Mut,
    /// A `&mut T` variable, captured as `&mut *r`.
    Reborrow,
    /// Copied or moved into a `move` closure's environment.
    Move,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Capture {
    pub name: String,
    /// The captured variable's type.
    pub ty: Type,
    pub mode: CaptureMode,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ClosureInfo {
    /// `parent#cK`, the name of the closure's body.
    pub name: String,
    pub parent: String,
    pub captures: Vec<Capture>,
    pub is_move: bool,
    /// Declared parameters; `[Unit]` for a block without parameters.
    pub params: Vec<Type>,
    pub ret: Type,
    pub span: Span,
}

impl ClosureInfo {
    /// Field types of the environment tuple, one per capture.
    pub fn env_fields(&self) -> Vec<Type> {
        self.captures
            .iter()
            .map(|c| match c.mode {
                CaptureMode::Shared => Type::r#ref(false, c.ty.clone()),
                CaptureMode::Mut => Type::r#ref(true, c.ty.clone()),
                CaptureMode::Reborrow | CaptureMode::Move => c.ty.clone(),
            })
            .collect()
    }
    /// The closure body's first parameter: `&Tuple[fields]`, or `&Unit` without captures.
    pub fn env_type(&self) -> Type {
        Type::r#ref(false, Type::tuple(self.env_fields()))
    }
    /// Type of the closure literal: owned, or `&(..)` when it borrows what it captures.
    pub fn ty(&self) -> Type {
        let f = Type::func(&self.params, self.ret.clone());
        if !self.is_move && !self.captures.is_empty() {
            Type::r#ref(false, f)
        } else {
            f
        }
    }
}

/// Number of top-level arrows of a function type (0 for anything else).
pub fn arity(t: &Type) -> usize {
    match t {
        Type::Fn(_, r) => 1 + arity(r),
        _ => 0,
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Global {
    pub scheme: Scheme,
    pub n_params: usize,
    pub kind: GlobalKind,
}

#[derive(Debug, Clone, PartialEq)]
pub struct StructInfo {
    pub generics: Vec<String>,
    pub fields: Vec<(String, Type)>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct VariantInfo {
    pub name: String,
    /// Field name is `Some` for named-field variants.
    pub fields: Vec<(Option<String>, Type)>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct EnumInfo {
    pub generics: Vec<String>,
    pub variants: Vec<VariantInfo>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MethodSig {
    /// `scheme.vars[0]` is `Self`; the type is `Self -> params... -> ret`.
    pub scheme: Scheme,
    pub n_params: usize,
    pub has_default: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TraitInfo {
    pub supertraits: Vec<String>,
    pub methods: HashMap<String, MethodSig>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ImplInfo {
    pub id: usize,
    pub generics: Vec<String>,
    pub bounds: Vec<(String, String)>,
    pub trait_name: Option<String>,
    pub self_ty: Type,
    /// Method name -> global name such as `Show#3::to_s`.
    pub methods: HashMap<String, String>,
    /// Associated (non-`self`) function name -> global name.
    pub assoc: HashMap<String, String>,
    pub span: Span,
}

/// How a method receiver is adjusted before the call.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Adjust {
    AutoRef(bool),
    AutoDeref,
}

#[derive(Debug, Clone, PartialEq)]
pub enum MethodRes {
    /// Inherent method; `targs` instantiate the impl generics followed by the method generics.
    Direct { global: String, targs: Vec<Type> },
    /// Trait method on `self_ty`; resolved to an impl by monomorphization.
    Trait { trait_name: String, method: String, self_ty: Type },
}

#[derive(Debug, Clone, PartialEq)]
pub enum DotRes {
    Field(usize),
    Method(MethodRes),
    /// `Type.function(args)`; the receiver expression is not evaluated.
    Assoc { global: String, targs: Vec<Type> },
    /// `Type.method`: a method named through its type, a function taking the receiver first.
    MethodValue(MethodRes),
}

#[derive(Debug, Default)]
pub struct TypeInfo {
    pub expr_types: HashMap<ExprId, Type>,
    pub pat_types: HashMap<PatId, Type>,
    pub globals: HashMap<String, Global>,
    pub structs: HashMap<String, StructInfo>,
    pub enums: HashMap<String, EnumInfo>,
    pub traits: HashMap<String, TraitInfo>,
    pub impls: Vec<ImplInfo>,
    /// Type arguments for expressions that reference a generic global, aligned with its scheme vars.
    pub insts: HashMap<ExprId, Vec<Type>>,
    pub dots: HashMap<ExprId, DotRes>,
    /// Variant name -> (enum name, variant index).
    pub variant_names: HashMap<String, (String, usize)>,
    /// Receiver adjustments, keyed by the receiver expression.
    pub adjust: HashMap<ExprId, Adjust>,
    /// Expressions of reference type whose `Copy` pointee is read (auto-deref).
    pub derefs: HashSet<ExprId>,
    /// Rvalue expressions auto-borrowed for a reference parameter (value: mutable).
    pub autorefs: HashMap<ExprId, bool>,
    /// Constructor patterns matched through a reference (place is dereferenced first).
    pub pat_deref: HashSet<PatId>,
    /// Bindings that bind by reference (value: mutable).
    pub pat_by_ref: HashMap<PatId, bool>,
    /// Bindings that move a non-Copy value out of the scrutinee.
    pub pat_moves: HashSet<PatId>,
    /// Function or trait method (`Trait::method`) -> index of the parameter its returned
    /// references borrow from (elision). Absent when the declared result holds no reference.
    pub elided: HashMap<String, usize>,
    /// Closure literals.
    pub closures: HashMap<ExprId, ClosureInfo>,
}

/// One-way match of a pattern type (impl generics as `Param`s) against a ground type.
pub fn match_pattern(pat: &Type, ty: &Type, map: &mut HashMap<String, Type>) -> bool {
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

impl TypeInfo {
    /// Finds the impl of `trait_name` matching ground type `ty` (no inference variables).
    pub fn impl_for(&self, trait_name: &str, ty: &Type) -> Option<(usize, HashMap<String, Type>)> {
        for imp in &self.impls {
            if imp.trait_name.as_deref() != Some(trait_name) {
                continue;
            }
            let mut map = HashMap::new();
            if match_pattern(&imp.self_ty, ty, &mut map) {
                return Some((imp.id, map));
            }
        }
        None
    }

    /// Whether values of `t` copy on use. `param_copy` answers for type parameters.
    pub fn is_copy(&self, t: &Type, param_copy: &dyn Fn(&str) -> bool) -> bool {
        match t {
            Type::Var(_) => false,
            Type::Param(p) => param_copy(p),
            Type::Fn(..) => true,
            Type::Con(n, args) => match n.as_str() {
                "Int" | "Float" | "Bool" | "Unit" | "Symbol" | "&" | "Gc" => true,
                "String" | "&mut" => false,
                "Tuple" => args.iter().all(|a| self.is_copy(a, param_copy)),
                _ => match self.impl_for("Copy", t) {
                    Some((id, map)) => self.impls[id].bounds.iter().all(|(gp, tr)| tr != "Copy" || self.is_copy(&map[gp], param_copy)),
                    None => false,
                },
            },
        }
    }

    /// Whether a value of `t` may hold a reference (and so carries loans).
    pub fn contains_ref(&self, t: &Type) -> bool {
        self.contains_in(t, &|t| matches!(t, Type::Con(n, _) if n == "&" || n == "&mut"), &mut Vec::new())
    }

    /// Whether `t` holds a function value anywhere, including behind references.
    pub fn contains_fn(&self, t: &Type) -> bool {
        self.contains_in(t, &|t| matches!(t, Type::Fn(..)), &mut Vec::new())
    }

    /// Whether values of `t` may carry loans: references, or function values (closures and
    /// partial applications can hold borrows).
    pub fn may_borrow(&self, t: &Type) -> bool {
        self.contains_ref(t) || self.contains_fn(t)
    }

    /// Whether `t` or a component of it (fields and variants, after substitution) is a `leaf`.
    fn contains_in(&self, t: &Type, leaf: &dyn Fn(&Type) -> bool, visiting: &mut Vec<Type>) -> bool {
        if leaf(t) {
            return true;
        }
        let Type::Con(n, args) = t else { return false };
        if args.iter().any(|a| self.contains_in(a, leaf, visiting)) {
            return true;
        }
        if visiting.contains(t) {
            return false;
        }
        visiting.push(t.clone());
        let fields: Vec<Type> = if let Some(s) = self.structs.get(n) {
            let map: HashMap<String, Type> = s.generics.iter().cloned().zip(args.iter().cloned()).collect();
            s.fields.iter().map(|(_, f)| subst(f, &map)).collect()
        } else if let Some(e) = self.enums.get(n) {
            let map: HashMap<String, Type> = e.generics.iter().cloned().zip(args.iter().cloned()).collect();
            e.variants.iter().flat_map(|v| v.fields.iter().map(|(_, f)| subst(f, &map))).collect::<Vec<_>>()
        } else {
            vec![]
        };
        let r = fields.iter().any(|f| self.contains_in(f, leaf, visiting));
        visiting.pop();
        r
    }

    /// Lifetime elision: the parameter a returned reference borrows from. `Ok(None)` when the
    /// result holds no reference; `Err` when elision cannot decide.
    pub fn elide(&self, params: &[Type], has_self: bool, ret: &Type) -> Result<Option<usize>, ()> {
        if !self.contains_ref(ret) {
            return Ok(None);
        }
        if has_self && params[0].as_ref().is_some() {
            return Ok(Some(0));
        }
        let with_refs: Vec<usize> = (0..params.len()).filter(|&i| self.contains_ref(&params[i])).collect();
        match with_refs.as_slice() {
            [i] => Ok(Some(*i)),
            _ => Err(()),
        }
    }

    /// Whether dropping a value of `t` does anything (frees memory or runs a `Drop` impl).
    pub fn needs_drop(&self, t: &Type) -> bool {
        match t {
            Type::Con(n, args) => match n.as_str() {
                "String" => true,
                "Int" | "Float" | "Bool" | "Unit" | "Symbol" | "&" | "&mut" | "Gc" => false,
                "Tuple" => args.iter().any(|a| self.needs_drop(a)),
                _ => {
                    if self.impl_for("Drop", t).is_some() {
                        return true;
                    }
                    if let Some(s) = self.structs.get(n) {
                        let map: HashMap<String, Type> = s.generics.iter().cloned().zip(args.iter().cloned()).collect();
                        return s.fields.iter().any(|(_, ft)| self.needs_drop(&subst(ft, &map)));
                    }
                    if let Some(e) = self.enums.get(n) {
                        let map: HashMap<String, Type> = e.generics.iter().cloned().zip(args.iter().cloned()).collect();
                        return e.variants.iter().flat_map(|v| v.fields.iter()).any(|(_, ft)| self.needs_drop(&subst(ft, &map)));
                    }
                    false
                }
            },
            _ => false,
        }
    }

    /// All traits implied by `trait_name`, including itself, through supertraits.
    pub fn trait_closure(&self, trait_name: &str) -> Vec<String> {
        let mut out = vec![trait_name.to_string()];
        let mut i = 0;
        while i < out.len() {
            if let Some(t) = self.traits.get(&out[i]) {
                for s in &t.supertraits {
                    if !out.contains(s) {
                        out.push(s.clone());
                    }
                }
            }
            i += 1;
        }
        out
    }
}

/// Context for converting a `TypeExpr` to a `Type`.
pub struct TypeEnv<'a> {
    /// ADT name -> arity.
    pub adts: &'a HashMap<String, usize>,
    pub generics: &'a [String],
    pub self_ty: Option<&'a Type>,
}

pub const BUILTIN_TYPES: &[&str] = &["Int", "Float", "Bool", "String", "Unit", "Symbol"];

pub fn from_ast(t: &TypeExpr, env: &TypeEnv) -> Result<Type, Diagnostic> {
    match t {
        TypeExpr::Ref(m, inner, _) => Ok(Type::r#ref(*m, from_ast(inner, env)?)),
        TypeExpr::Tuple(items, _) => {
            let mut ts = Vec::new();
            for i in items {
                ts.push(from_ast(i, env)?);
            }
            Ok(Type::tuple(ts))
        }
        TypeExpr::Fn(a, b, _) => Ok(Type::Fn(Box::new(from_ast(a, env)?), Box::new(from_ast(b, env)?))),
        TypeExpr::Name(name, args, span) => {
            if name == "Self" {
                return match env.self_ty {
                    Some(t) if args.is_empty() => Ok(t.clone()),
                    Some(_) => Err(Diagnostic::new(*span, "`Self` takes no type arguments")),
                    None => Err(Diagnostic::new(*span, "`Self` is only allowed inside a trait or impl")),
                };
            }
            if env.generics.contains(name) {
                if !args.is_empty() {
                    return Err(Diagnostic::new(*span, format!("type parameter `{name}` takes no type arguments")));
                }
                return Ok(Type::Param(name.clone()));
            }
            let name = match name.as_str() {
                "i64" => "Int",
                "f64" => "Float",
                n => n,
            };
            let arity = if BUILTIN_TYPES.contains(&name) {
                0
            } else {
                match env.adts.get(name) {
                    Some(a) => *a,
                    None => return Err(Diagnostic::new(*span, format!("unknown type `{name}`"))),
                }
            };
            if args.len() != arity {
                let what = if arity == 0 { "no type arguments".to_string() } else { format!("{arity} type arguments") };
                return Err(Diagnostic::new(*span, format!("type `{name}` takes {what}, found {}", args.len())));
            }
            let mut ts = Vec::new();
            for a in args {
                ts.push(from_ast(a, env)?);
            }
            Ok(Type::Con(name.to_string(), ts))
        }
    }
}

pub fn check(prog: &Program) -> Result<TypeInfo, Diagnostic> {
    infer::check_program(prog)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn display() {
        assert_eq!(Type::func(&[Type::con("Int"), Type::con("Bool")], Type::unit()).to_string(), "Int -> Bool -> Unit");
        let hof = Type::func(&[Type::func(&[Type::con("Int")], Type::con("Int"))], Type::con("Int"));
        assert_eq!(hof.to_string(), "(Int -> Int) -> Int");
        assert_eq!(Type::Con("List".into(), vec![Type::con("Int")]).to_string(), "List[Int]");
        assert_eq!(Type::tuple(vec![Type::con("Int"), Type::Param("T".into())]).to_string(), "(Int, T)");
        assert_eq!(Type::tuple(vec![]).to_string(), "Unit");
        assert_eq!(Type::r#ref(true, Type::con("Int")).to_string(), "&mut Int");
        assert_eq!(Type::r#ref(false, Type::Con("Gc".into(), vec![Type::con("Int")])).peel().to_string(), "Gc[Int]");
    }
}
