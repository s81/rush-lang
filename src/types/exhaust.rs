//! Exhaustiveness and reachability of `case` arms (usefulness matrix).

use std::collections::HashMap;

use super::*;
use crate::ast::{Arm, Lit, PatKind, Pattern};

#[derive(Clone, Debug, PartialEq)]
enum C {
    Variant(usize),
    Tuple,
    Struct,
    Bool(bool),
    Int(i64),
    Float(u64),
    Str(String),
    Unit,
}

#[derive(Clone, Debug)]
enum P {
    Wild,
    Ctor(C, Vec<P>),
    Or(Vec<P>),
}

fn convert(info: &TypeInfo, p: &Pattern) -> P {
    match &p.kind {
        PatKind::Wild | PatKind::Bind(_) => P::Wild,
        PatKind::At(_, inner) => convert(info, inner),
        PatKind::Lit(l) => P::Ctor(
            match l {
                Lit::Int(v) => C::Int(*v),
                Lit::Float(v) => C::Float(v.to_bits()),
                // A column holds one type, so strings and symbols never meet.
                Lit::Str(s) | Lit::Symbol(s) => C::Str(s.clone()),
                Lit::Bool(b) => C::Bool(*b),
                Lit::Unit => C::Unit,
            },
            vec![],
        ),
        PatKind::Tuple(ps) => P::Ctor(C::Tuple, ps.iter().map(|q| convert(info, q)).collect()),
        PatKind::Variant { name, fields } => {
            let (_, idx) = &info.variant_names[name];
            P::Ctor(C::Variant(*idx), fields.iter().map(|q| convert(info, q)).collect())
        }
        PatKind::Struct { name, fields } => {
            if let Some(s) = info.structs.get(name) {
                let subs = s.fields.iter().map(|(f, _)| fields.iter().find(|(n, _)| n == f).map(|(_, q)| convert(info, q)).unwrap_or(P::Wild)).collect();
                P::Ctor(C::Struct, subs)
            } else {
                let (en, idx) = &info.variant_names[name];
                let v = &info.enums[en].variants[*idx];
                let subs = v.fields.iter().map(|(f, _)| fields.iter().find(|(n, _)| Some(n) == f.as_ref()).map(|(_, q)| convert(info, q)).unwrap_or(P::Wild)).collect();
                P::Ctor(C::Variant(*idx), subs)
            }
        }
        PatKind::Or(alts) => P::Or(alts.iter().map(|q| convert(info, q)).collect()),
    }
}

struct Sig {
    /// `None` means the constructor set is infinite (only a wildcard covers).
    ctors: Option<Vec<C>>,
}

fn signature(info: &TypeInfo, ty: &Type) -> Sig {
    match ty.peel() {
        Type::Con(n, items) => match n.as_str() {
            "Bool" => Sig { ctors: Some(vec![C::Bool(true), C::Bool(false)]) },
            "Unit" => Sig { ctors: Some(vec![C::Unit]) },
            "Tuple" => {
                let _ = items;
                Sig { ctors: Some(vec![C::Tuple]) }
            }
            _ if info.structs.contains_key(n) => Sig { ctors: Some(vec![C::Struct]) },
            _ if info.enums.contains_key(n) => Sig { ctors: Some((0..info.enums[n].variants.len()).map(C::Variant).collect()) },
            _ => Sig { ctors: None },
        },
        _ => Sig { ctors: None },
    }
}

/// Field types of constructor `c` at type `ty`.
fn fields_of(info: &TypeInfo, ty: &Type, c: &C) -> Vec<Type> {
    match (ty.peel(), c) {
        (Type::Con(_, items), C::Tuple) => items.clone(),
        (Type::Con(n, targs), C::Struct) => {
            let s = &info.structs[n];
            let map: HashMap<String, Type> = s.generics.iter().cloned().zip(targs.iter().cloned()).collect();
            s.fields.iter().map(|(_, t)| subst(t, &map)).collect()
        }
        (Type::Con(n, targs), C::Variant(i)) => {
            let e = &info.enums[n];
            let map: HashMap<String, Type> = e.generics.iter().cloned().zip(targs.iter().cloned()).collect();
            e.variants[*i].fields.iter().map(|(_, t)| subst(t, &map)).collect()
        }
        _ => vec![],
    }
}

fn expand_or(rows: &[Vec<P>]) -> Vec<Vec<P>> {
    let mut out = Vec::new();
    for r in rows {
        match r.first() {
            Some(P::Or(alts)) => {
                for a in alts {
                    let mut nr = vec![a.clone()];
                    nr.extend(r[1..].iter().cloned());
                    out.extend(expand_or(&[nr]));
                }
            }
            _ => out.push(r.clone()),
        }
    }
    out
}

/// Rows specialized by constructor `c` of arity `n`.
fn specialize(rows: &[Vec<P>], c: &C, n: usize) -> Vec<Vec<P>> {
    let mut out = Vec::new();
    for r in rows {
        match &r[0] {
            P::Ctor(rc, subs) if rc == c => {
                let mut nr = subs.clone();
                nr.extend(r[1..].iter().cloned());
                out.push(nr);
            }
            P::Wild => {
                let mut nr = vec![P::Wild; n];
                nr.extend(r[1..].iter().cloned());
                out.push(nr);
            }
            _ => {}
        }
    }
    out
}

/// Returns a witness vector if `q` matches something no row matches.
fn useful(info: &TypeInfo, rows: &[Vec<P>], q: &[P], tys: &[Type]) -> Option<Vec<P>> {
    if q.is_empty() {
        return if rows.is_empty() { Some(vec![]) } else { None };
    }
    let rows = expand_or(rows);
    match &q[0] {
        P::Or(alts) => {
            for a in alts {
                let mut nq = vec![a.clone()];
                nq.extend(q[1..].iter().cloned());
                if let Some(w) = useful(info, &rows, &nq, tys) {
                    return Some(w);
                }
            }
            None
        }
        P::Ctor(c, subs) => {
            let n = subs.len();
            let mut nq = subs.clone();
            nq.extend(q[1..].iter().cloned());
            let mut ntys = fields_of(info, &tys[0], c);
            ntys.extend(tys[1..].iter().cloned());
            let w = useful(info, &specialize(&rows, c, n), &nq, &ntys)?;
            let mut out = vec![P::Ctor(c.clone(), w[..n].to_vec())];
            out.extend(w[n..].iter().cloned());
            Some(out)
        }
        P::Wild => {
            let sig = signature(info, &tys[0]);
            let heads: Vec<C> = rows.iter().filter_map(|r| if let P::Ctor(c, _) = &r[0] { Some(c.clone()) } else { None }).collect();
            let complete = sig.ctors.as_ref().map_or(false, |all| all.iter().all(|c| heads.contains(c)));
            if complete {
                for c in sig.ctors.as_ref().unwrap() {
                    let ftys = fields_of(info, &tys[0], c);
                    let n = ftys.len();
                    let mut nq = vec![P::Wild; n];
                    nq.extend(q[1..].iter().cloned());
                    let mut ntys = ftys;
                    ntys.extend(tys[1..].iter().cloned());
                    if let Some(w) = useful(info, &specialize(&rows, c, n), &nq, &ntys) {
                        let mut out = vec![P::Ctor(c.clone(), w[..n].to_vec())];
                        out.extend(w[n..].iter().cloned());
                        return Some(out);
                    }
                }
                None
            } else {
                let default: Vec<Vec<P>> = rows.iter().filter(|r| matches!(r[0], P::Wild)).map(|r| r[1..].to_vec()).collect();
                let w = useful(info, &default, &q[1..], &tys[1..])?;
                let head = match &sig.ctors {
                    Some(all) => {
                        let missing = all.iter().find(|c| !heads.contains(c)).unwrap();
                        let n = fields_of(info, &tys[0], missing).len();
                        P::Ctor(missing.clone(), vec![P::Wild; n])
                    }
                    None => P::Wild,
                };
                let mut out = vec![head];
                out.extend(w);
                Some(out)
            }
        }
    }
}

fn show(info: &TypeInfo, ty: &Type, p: &P) -> String {
    let ty = ty.peel();
    match p {
        P::Wild => "_".into(),
        P::Or(alts) => alts.iter().map(|a| show(info, ty, a)).collect::<Vec<_>>().join(" | "),
        P::Ctor(c, subs) => {
            let ftys = fields_of(info, ty, c);
            let inner = |subs: &[P]| subs.iter().zip(&ftys).map(|(s, t)| show(info, t, s)).collect::<Vec<_>>();
            match c {
                C::Bool(b) => b.to_string(),
                C::Int(v) => v.to_string(),
                C::Float(bits) => format!("{:?}", f64::from_bits(*bits)),
                C::Str(s) => format!("{s:?}"),
                C::Unit => "()".into(),
                C::Tuple => format!("({})", inner(subs).join(", ")),
                C::Struct => {
                    let s = &info.structs[ty.head().unwrap()];
                    let fields: Vec<String> = s.fields.iter().zip(inner(subs)).map(|((n, _), v)| format!("{n}: {v}")).collect();
                    format!("{} {{ {} }}", ty.head().unwrap(), fields.join(", "))
                }
                C::Variant(i) => {
                    let v = &info.enums[ty.head().unwrap()].variants[*i];
                    if v.fields.is_empty() {
                        v.name.clone()
                    } else if v.fields[0].0.is_some() {
                        let fields: Vec<String> = v.fields.iter().zip(inner(subs)).map(|((n, _), val)| format!("{}: {val}", n.as_ref().unwrap())).collect();
                        format!("{} {{ {} }}", v.name, fields.join(", "))
                    } else {
                        format!("{}({})", v.name, inner(subs).join(", "))
                    }
                }
            }
        }
    }
}

pub fn check_case(info: &TypeInfo, ty: &Type, arms: &[Arm], span: Span) -> Result<(), Diagnostic> {
    let tys = vec![ty.clone()];
    let mut rows: Vec<Vec<P>> = Vec::new();
    for arm in arms {
        let p = convert(info, &arm.pat);
        if useful(info, &rows, &[p.clone()], &tys).is_none() {
            return Err(Diagnostic::new(arm.pat.span, "unreachable pattern"));
        }
        if arm.guard.is_none() {
            rows.push(vec![p]);
        }
    }
    if let Some(w) = useful(info, &rows, &[P::Wild], &tys) {
        return Err(Diagnostic::new(span, format!("non-exhaustive `case`: pattern `{}` not covered", show(info, ty, &w[0]))));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::super::infer::check_program;
    use super::*;
    use crate::lexer::lex;
    use crate::parser::parse;

    fn err(s: &str) -> String {
        let prelude = include_str!("../../std/prelude.rush");
        let mut id = 0;
        let mut p = parse(lex(prelude).unwrap(), &mut id).unwrap();
        p.items.extend(parse(lex(s).unwrap(), &mut id).unwrap().items);
        match check_program(&p) {
            Ok(_) => "ok".into(),
            Err(d) => d.msg,
        }
    }

    const SHAPE: &str = "enum Shape\n  Circle(Float)\n  Rect(Float, Float)\n  Empty\nend\n";

    #[test]
    fn missing_variant() {
        assert_eq!(err(&format!("{SHAPE}def f(s: Shape) -> Int\n  case s\n  in Circle(_) then 1\n  in Empty then 2\n  end\nend\ndef main\n  ()\nend\n")), "non-exhaustive `case`: pattern `Rect(_, _)` not covered");
    }

    #[test]
    fn nested_missing_in_tuple() {
        assert_eq!(err("def f(o: (Option[Int], Option[Int])) -> Int\n  case o\n  in (Some(_), _) then 1\n  in (None, Some(_)) then 2\n  end\nend\ndef main\n  ()\nend\n"), "non-exhaustive `case`: pattern `(None, None)` not covered");
    }

    #[test]
    fn bool_matrix_complete_and_or_patterns() {
        assert_eq!(err("def f(b: (Bool, Int)) -> Int\n  case b\n  in (true, _) | (false, 1) then 1\n  in (false, _) then 2\n  end\nend\ndef main\n  ()\nend\n"), "ok");
    }

    #[test]
    fn literal_patterns_need_wildcard() {
        assert_eq!(err("def f(n: Int) -> Int\n  case n\n  in 1 then 1\n  in 2 then 2\n  end\nend\ndef main\n  ()\nend\n"), "non-exhaustive `case`: pattern `_` not covered");
        assert_eq!(err("def f(n: Int) -> Int\n  case n\n  in 1 then 1\n  else\n    0\n  end\nend\ndef main\n  ()\nend\n"), "ok");
    }

    #[test]
    fn guard_does_not_count() {
        assert_eq!(err("def f(b: Bool) -> Int\n  case b\n  in true then 1\n  in false if b then 2\n  end\nend\ndef main\n  ()\nend\n"), "non-exhaustive `case`: pattern `false` not covered");
    }

    #[test]
    fn unreachable_arm() {
        assert_eq!(err("def f(b: Bool) -> Int\n  case b\n  in _ then 1\n  in true then 2\n  end\nend\ndef main\n  ()\nend\n"), "unreachable pattern");
    }

    #[test]
    fn struct_pattern_witness() {
        assert_eq!(err("struct P\n  a: Bool\n  b: Bool\nend\ndef f(p: P) -> Int\n  case p\n  in P { a: true } then 1\n  in P { b: true } then 2\n  end\nend\ndef main\n  ()\nend\n"), "non-exhaustive `case`: pattern `P { a: false, b: false }` not covered");
    }
}
