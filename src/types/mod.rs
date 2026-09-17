//! Types, schemes, declaration tables, and the entry point `check`.

mod decls;
mod exhaust;
mod infer;

use std::collections::HashMap;
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
    pub fn head(&self) -> Option<&str> {
        match self {
            Type::Con(n, _) => Some(n),
            _ => None,
        }
    }
    pub fn is_primitive(&self) -> bool {
        matches!(self.head(), Some("Int" | "Float" | "Bool" | "String" | "Unit"))
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
    Variant { enum_name: String, index: usize },
    ImplMethod { impl_id: usize },
    TraitDefault { trait_name: String },
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
    pub span: Span,
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
}

impl TypeInfo {
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

const BUILTIN_TYPES: &[&str] = &["Int", "Float", "Bool", "String", "Unit"];

pub fn from_ast(t: &TypeExpr, env: &TypeEnv) -> Result<Type, Diagnostic> {
    match t {
        TypeExpr::Ref(_, inner, _) => from_ast(inner, env),
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
    }
}
