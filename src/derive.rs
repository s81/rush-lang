//! Expands `derive Copy, Clone, Show, Eq` into impl items by synthesizing Rush source.

use crate::ast::*;
use crate::diag::{Diagnostic, Span};
use crate::lexer::lex;
use crate::parser::parse;

const SUPPORTED: &[&str] = &["Copy", "Clone", "Show", "Eq"];

/// Appends generated impls for every `derive` line. Generated items carry the deriving item's span.
pub fn expand(prog: &mut Program, next_id: &mut ExprId) -> Result<(), Diagnostic> {
    let mut generated = Vec::new();
    for item in &prog.items {
        let (derives, span) = match item {
            Item::Struct(s) => (&s.derives, s.span),
            Item::Enum(e) => (&e.derives, e.span),
            _ => continue,
        };
        for d in derives {
            if !SUPPORTED.contains(&d.as_str()) {
                return Err(Diagnostic::new(span, format!("cannot derive `{d}`; supported: Copy, Clone, Show, Eq")));
            }
            let src = generate(item, d);
            let toks = lex(&src).map_err(|e| Diagnostic::new(span, format!("internal derive error: {}", e.msg)))?;
            let mut p = parse(toks, next_id).map_err(|e| Diagnostic::new(span, format!("internal derive error: {}", e.msg)))?;
            for it in &mut p.items {
                respan_item(it, span);
            }
            generated.extend(p.items);
        }
    }
    prog.items.extend(generated);
    Ok(())
}

fn type_text(t: &TypeExpr) -> String {
    match t {
        TypeExpr::Name(n, args, _) if args.is_empty() => n.clone(),
        TypeExpr::Name(n, args, _) => format!("{n}[{}]", args.iter().map(type_text).collect::<Vec<_>>().join(", ")),
        TypeExpr::Tuple(items, _) => format!("({})", items.iter().map(type_text).collect::<Vec<_>>().join(", ")),
        TypeExpr::Fn(a, b, _) => format!("{} -> {}", type_text(a), type_text(b)),
        TypeExpr::Ref(m, inner, _) => format!("&{}{}", if *m { "mut " } else { "" }, type_text(inner)),
    }
}

/// `impl[A: Trait, B: Trait] Trait for Name[A, B]` header.
fn header(name: &str, generics: &Generics, trait_name: &str) -> String {
    let bound = if trait_name == "Copy" { "Copy" } else { trait_name };
    if generics.params.is_empty() {
        return format!("impl {trait_name} for {name}");
    }
    let gens: Vec<String> = generics.params.iter().map(|p| format!("{}: {bound}", p.name)).collect();
    let args: Vec<&str> = generics.params.iter().map(|p| p.name.as_str()).collect();
    format!("impl[{}] {trait_name} for {name}[{}]", gens.join(", "), args.join(", "))
}

fn self_ty(name: &str, generics: &Generics) -> String {
    if generics.params.is_empty() {
        name.to_string()
    } else {
        format!("{name}[{}]", generics.params.iter().map(|p| p.name.as_str()).collect::<Vec<_>>().join(", "))
    }
}

/// Source text of the impl for `derive` on `item`.
pub fn generate(item: &Item, derive: &str) -> String {
    match item {
        Item::Struct(s) => gen_struct(s, derive),
        Item::Enum(e) => gen_enum(e, derive),
        _ => unreachable!(),
    }
}

fn gen_struct(s: &StructDef, derive: &str) -> String {
    let h = header(&s.name, &s.generics, derive);
    let st = self_ty(&s.name, &s.generics);
    match derive {
        "Show" => {
            let body = if s.fields.is_empty() {
                format!("\"{}\"", s.name)
            } else {
                let parts: Vec<String> = s.fields.iter().map(|f| format!("{}: #{{@{}.inspect}}", f.name, f.name)).collect();
                format!("\"{} {{ {} }}\"", s.name, parts.join(", "))
            };
            format!("{h}\n  def to_s(&self)\n    {body}\n  end\nend\n")
        }
        "Eq" => {
            let body = if s.fields.is_empty() {
                "true".to_string()
            } else {
                s.fields.iter().map(|f| format!("@{} == other.{}", f.name, f.name)).collect::<Vec<_>>().join(" and ")
            };
            format!("{h}\n  def eq(&self, other: &{st})\n    {body}\n  end\nend\n")
        }
        "Clone" => {
            let fields: Vec<String> = s.fields.iter().map(|f| format!("{}: @{}.clone", f.name, f.name)).collect();
            let body = if fields.is_empty() { format!("{} {{ }}", s.name) } else { format!("{} {{ {} }}", s.name, fields.join(", ")) };
            format!("{h}\n  def clone(&self)\n    {body}\n  end\nend\n")
        }
        "Copy" => {
            let hc = header(&s.name, &s.generics, "Clone").replace("Clone for", "Clone for").replace(": Clone", ": Copy");
            format!("{h}\nend\n{hc}\n  def clone(&self)\n    *self\n  end\nend\n")
        }
        _ => unreachable!(),
    }
}

fn variant_binders(v: &VariantDef, prefix: &str) -> (String, Vec<String>) {
    // (pattern text, binder names)
    match &v.fields {
        VariantFields::Unit => (v.name.clone(), vec![]),
        VariantFields::Tuple(tys) => {
            let names: Vec<String> = (0..tys.len()).map(|i| format!("{prefix}{i}")).collect();
            (format!("{}({})", v.name, names.join(", ")), names)
        }
        VariantFields::Named(fs) => {
            let names: Vec<String> = (0..fs.len()).map(|i| format!("{prefix}{i}")).collect();
            let pats: Vec<String> = fs.iter().zip(&names).map(|(f, n)| format!("{}: {n}", f.name)).collect();
            (format!("{} {{ {} }}", v.name, pats.join(", ")), names)
        }
    }
}

fn gen_enum(e: &EnumDef, derive: &str) -> String {
    let h = header(&e.name, &e.generics, derive);
    let st = self_ty(&e.name, &e.generics);
    match derive {
        "Show" => {
            let mut arms = String::new();
            for v in &e.variants {
                let (pat, names) = variant_binders(v, "a");
                let text = match &v.fields {
                    VariantFields::Unit => format!("\"{}\"", v.name),
                    VariantFields::Tuple(_) => format!("\"{}({})\"", v.name, names.iter().map(|n| format!("#{{{n}.inspect}}")).collect::<Vec<_>>().join(", ")),
                    VariantFields::Named(fs) => format!(
                        "\"{} {{ {} }}\"",
                        v.name,
                        fs.iter().zip(&names).map(|(f, n)| format!("{}: #{{{n}.inspect}}", f.name)).collect::<Vec<_>>().join(", ")
                    ),
                };
                arms.push_str(&format!("    in {pat} then {text}\n"));
            }
            format!("{h}\n  def to_s(&self)\n    case self\n{arms}    end\n  end\nend\n")
        }
        "Eq" => {
            let mut arms = String::new();
            for v in &e.variants {
                let (pa, an) = variant_binders(v, "a");
                let (pb, bn) = variant_binders(v, "b");
                let body = if an.is_empty() { "true".to_string() } else { an.iter().zip(&bn).map(|(a, b)| format!("{a} == {b}")).collect::<Vec<_>>().join(" and ") };
                arms.push_str(&format!("    in ({pa}, {pb}) then {body}\n"));
            }
            if e.variants.len() > 1 {
                arms.push_str("    in (_, _) then false\n");
            }
            format!("{h}\n  def eq(&self, other: &{st})\n    case (self, other)\n{arms}    end\n  end\nend\n")
        }
        "Clone" => {
            let mut arms = String::new();
            for v in &e.variants {
                let (pat, names) = variant_binders(v, "a");
                let rebuild = match &v.fields {
                    VariantFields::Unit => v.name.clone(),
                    VariantFields::Tuple(_) => format!("{}({})", v.name, names.iter().map(|n| format!("{n}.clone")).collect::<Vec<_>>().join(", ")),
                    VariantFields::Named(fs) => format!(
                        "{} {{ {} }}",
                        v.name,
                        fs.iter().zip(&names).map(|(f, n)| format!("{}: {n}.clone", f.name)).collect::<Vec<_>>().join(", ")
                    ),
                };
                arms.push_str(&format!("    in {pat} then {rebuild}\n"));
            }
            format!("{h}\n  def clone(&self)\n    case self\n{arms}    end\n  end\nend\n")
        }
        "Copy" => {
            let hc = header(&e.name, &e.generics, "Clone").replace(": Clone", ": Copy");
            format!("{h}\nend\n{hc}\n  def clone(&self)\n    *self\n  end\nend\n")
        }
        _ => unreachable!(),
    }
}

// ----- respan -----

fn respan_item(item: &mut Item, sp: Span) {
    match item {
        Item::Impl(i) => {
            i.span = sp;
            respan_generics(&mut i.generics, sp);
            respan_type(&mut i.self_ty, sp);
            i.methods.iter_mut().for_each(|m| respan_def(m, sp));
        }
        Item::Def(d) | Item::Extern(d) => respan_def(d, sp),
        Item::Struct(s) => s.span = sp,
        Item::Enum(e) => e.span = sp,
        Item::Trait(t) => t.span = sp,
    }
}

fn respan_generics(g: &mut Generics, sp: Span) {
    g.params.iter_mut().for_each(|p| p.span = sp);
}

fn respan_type(t: &mut TypeExpr, sp: Span) {
    match t {
        TypeExpr::Name(_, args, s) => {
            *s = sp;
            args.iter_mut().for_each(|a| respan_type(a, sp));
        }
        TypeExpr::Tuple(items, s) => {
            *s = sp;
            items.iter_mut().for_each(|a| respan_type(a, sp));
        }
        TypeExpr::Fn(a, b, s) => {
            *s = sp;
            respan_type(a, sp);
            respan_type(b, sp);
        }
        TypeExpr::Ref(_, inner, s) => {
            *s = sp;
            respan_type(inner, sp);
        }
    }
}

fn respan_def(d: &mut Def, sp: Span) {
    d.span = sp;
    respan_generics(&mut d.generics, sp);
    for p in &mut d.params {
        p.span = sp;
        if let Some(t) = &mut p.ty {
            respan_type(t, sp);
        }
    }
    if let Some(t) = &mut d.ret {
        respan_type(t, sp);
    }
    respan_block(&mut d.body, sp);
}

fn respan_block(b: &mut Block, sp: Span) {
    b.span = sp;
    for s in &mut b.stmts {
        match s {
            Stmt::Let { pat, init, span, .. } => {
                *span = sp;
                respan_pat(pat, sp);
                respan_expr(init, sp);
            }
            Stmt::Expr(e) => respan_expr(e, sp),
        }
    }
}

fn respan_pat(p: &mut Pattern, sp: Span) {
    p.span = sp;
    match &mut p.kind {
        PatKind::Tuple(ps) | PatKind::Or(ps) | PatKind::Variant { fields: ps, .. } => ps.iter_mut().for_each(|q| respan_pat(q, sp)),
        PatKind::Struct { fields, .. } => fields.iter_mut().for_each(|(_, q)| respan_pat(q, sp)),
        PatKind::At(_, inner) => respan_pat(inner, sp),
        PatKind::Wild | PatKind::Bind(_) | PatKind::Lit(_) => {}
    }
}

fn respan_expr(e: &mut Expr, sp: Span) {
    e.span = sp;
    match &mut e.kind {
        ExprKind::Tuple(items) => items.iter_mut().for_each(|i| respan_expr(i, sp)),
        ExprKind::StructLit { fields, .. } => fields.iter_mut().for_each(|(_, v)| respan_expr(v, sp)),
        ExprKind::Dot { recv, args, .. } => {
            respan_expr(recv, sp);
            args.iter_mut().flatten().for_each(|a| respan_expr(a, sp));
        }
        ExprKind::TupleIndex(r, _) | ExprKind::Ref(_, r) | ExprKind::Deref(r) | ExprKind::Unary(_, r) => respan_expr(r, sp),
        ExprKind::Binary(_, a, b) | ExprKind::Assign(a, b) | ExprKind::Range(a, b, _) => {
            respan_expr(a, sp);
            respan_expr(b, sp);
        }
        ExprKind::Call(f, args) => {
            respan_expr(f, sp);
            args.iter_mut().for_each(|a| respan_expr(a, sp));
        }
        ExprKind::If { cond, then, els } => {
            respan_expr(cond, sp);
            respan_block(then, sp);
            if let Some(b) = els {
                respan_block(b, sp);
            }
        }
        ExprKind::While { cond, body } => {
            respan_expr(cond, sp);
            respan_block(body, sp);
        }
        ExprKind::Case { scrutinee, arms } => {
            respan_expr(scrutinee, sp);
            for a in arms {
                a.span = sp;
                respan_pat(&mut a.pat, sp);
                if let Some(g) = &mut a.guard {
                    respan_expr(g, sp);
                }
                respan_block(&mut a.body, sp);
            }
        }
        ExprKind::Interp(parts) => parts.iter_mut().for_each(|p| {
            if let InterpPart::Expr(x) = p {
                respan_expr(x, sp)
            }
        }),
        ExprKind::Return(v) => v.iter_mut().for_each(|x| respan_expr(x, sp)),
        ExprKind::Int(_) | ExprKind::Float(_) | ExprKind::Str(_) | ExprKind::Bool(_) | ExprKind::Unit | ExprKind::Symbol(_) | ExprKind::Var(_) => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_src(s: &str) -> Program {
        parse(lex(s).unwrap(), &mut 0).unwrap()
    }

    #[test]
    fn struct_show_eq_clone_copy_text() {
        let p = parse_src("struct Person\n  derive Show, Eq, Clone\n  name: String\n  age: Int\nend\n");
        assert_eq!(
            generate(&p.items[0], "Show"),
            "impl Show for Person\n  def to_s(&self)\n    \"Person { name: #{@name.inspect}, age: #{@age.inspect} }\"\n  end\nend\n"
        );
        assert_eq!(generate(&p.items[0], "Eq"), "impl Eq for Person\n  def eq(&self, other: &Person)\n    @name == other.name and @age == other.age\n  end\nend\n");
        assert_eq!(generate(&p.items[0], "Clone"), "impl Clone for Person\n  def clone(&self)\n    Person { name: @name.clone, age: @age.clone }\n  end\nend\n");
        let p = parse_src("struct Pt[A, B]\n  derive Copy\n  x: A\n  y: B\nend\n");
        assert_eq!(
            generate(&p.items[0], "Copy"),
            "impl[A: Copy, B: Copy] Copy for Pt[A, B]\nend\nimpl[A: Copy, B: Copy] Clone for Pt[A, B]\n  def clone(&self)\n    *self\n  end\nend\n"
        );
    }

    #[test]
    fn enum_show_eq_clone_text() {
        let p = parse_src("enum S\n  derive Show, Eq, Clone\n  C(Float)\n  R { w: Float, h: Float }\n  E\nend\n");
        assert_eq!(
            generate(&p.items[0], "Show"),
            "impl Show for S\n  def to_s(&self)\n    case self\n    in C(a0) then \"C(#{a0.inspect})\"\n    in R { w: a0, h: a1 } then \"R { w: #{a0.inspect}, h: #{a1.inspect} }\"\n    in E then \"E\"\n    end\n  end\nend\n"
        );
        assert_eq!(
            generate(&p.items[0], "Eq"),
            "impl Eq for S\n  def eq(&self, other: &S)\n    case (self, other)\n    in (C(a0), C(b0)) then a0 == b0\n    in (R { w: a0, h: a1 }, R { w: b0, h: b1 }) then a0 == b0 and a1 == b1\n    in (E, E) then true\n    in (_, _) then false\n    end\n  end\nend\n"
        );
        assert_eq!(
            generate(&p.items[0], "Clone"),
            "impl Clone for S\n  def clone(&self)\n    case self\n    in C(a0) then C(a0.clone)\n    in R { w: a0, h: a1 } then R { w: a0.clone, h: a1.clone }\n    in E then E\n    end\n  end\nend\n"
        );
    }

    #[test]
    fn expand_appends_respanned_impls() {
        let mut p = parse_src("struct P\n  derive Show, Eq\n  x: Int\nend\ndef main\n  ()\nend\n");
        let mut id = 100;
        expand(&mut p, &mut id).unwrap();
        assert_eq!(p.items.len(), 4);
        let Item::Struct(s) = &p.items[0] else { panic!() };
        let sp = s.span;
        let Item::Impl(i) = &p.items[2] else { panic!() };
        assert_eq!(i.trait_name.as_deref(), Some("Show"));
        assert_eq!(i.span, sp);
        let Stmt::Expr(body) = &i.methods[0].body.stmts[0] else { panic!() };
        assert_eq!(body.span, sp);
        assert!(id > 100);
    }

    #[test]
    fn unknown_derive() {
        let mut p = parse_src("struct P\n  derive Ord\n  x: Int\nend\n");
        assert_eq!(expand(&mut p, &mut 0).unwrap_err().msg, "cannot derive `Ord`; supported: Copy, Clone, Show, Eq");
    }
}
