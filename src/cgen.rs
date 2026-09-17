//! C99 emission from monomorphized MIR.

use std::collections::HashMap;
use std::fmt::Write;

use crate::ast::{BinOp, UnOp};
use crate::mir::*;
use crate::mono::mangle_type;
use crate::types::{subst, Type, TypeInfo};

fn c_type(t: &Type) -> String {
    match t {
        Type::Con(n, args) if args.is_empty() => match n.as_str() {
            "Int" => "int64_t".into(),
            "Float" => "double".into(),
            "Bool" => "bool".into(),
            "String" => "rush_str".into(),
            "Unit" => "rush_unit".into(),
            _ => format!("rush_{}", mangle_type(t)),
        },
        Type::Con(..) => format!("rush_{}", mangle_type(t)),
        _ => panic!("cgen: unsupported type {t}"),
    }
}

fn is_named(t: &Type, name: &str) -> bool {
    matches!(t, Type::Con(n, _) if n == name)
}

fn c_string_lit(s: &str) -> String {
    let mut out = String::from("\"");
    for b in s.bytes() {
        match b {
            b'"' | b'\\' => write!(out, "\\{:03o}", b).unwrap(),
            0x20..=0x7e => out.push(b as char),
            _ => write!(out, "\\{:03o}", b).unwrap(),
        }
    }
    out.push('"');
    out
}

struct Gen<'a> {
    info: &'a TypeInfo,
}

impl<'a> Gen<'a> {
    /// Field types of an ADT or tuple instantiation, with C field names.
    fn fields(&self, t: &Type) -> Vec<(String, Type)> {
        let Type::Con(n, args) = t else { return vec![] };
        if n == "Tuple" {
            return args.iter().enumerate().map(|(i, a)| (format!("f{i}"), a.clone())).collect();
        }
        if let Some(s) = self.info.structs.get(n) {
            let map: HashMap<String, Type> = s.generics.iter().cloned().zip(args.iter().cloned()).collect();
            return s.fields.iter().map(|(f, ft)| (format!("f_{f}"), subst(ft, &map))).collect();
        }
        vec![]
    }

    /// Variant field lists of an enum instantiation.
    fn variants(&self, t: &Type) -> Vec<Vec<(String, Type)>> {
        let Type::Con(n, args) = t else { return vec![] };
        let Some(e) = self.info.enums.get(n) else { return vec![] };
        let map: HashMap<String, Type> = e.generics.iter().cloned().zip(args.iter().cloned()).collect();
        e.variants
            .iter()
            .map(|v| {
                v.fields
                    .iter()
                    .enumerate()
                    .map(|(i, (name, ft))| (name.as_ref().map(|s| format!("f_{s}")).unwrap_or_else(|| format!("f{i}")), subst(ft, &map)))
                    .collect()
            })
            .collect()
    }

    fn is_adt(&self, t: &Type) -> bool {
        matches!(t, Type::Con(n, _) if n == "Tuple" || self.info.structs.contains_key(n) || self.info.enums.contains_key(n))
    }

    /// Types this ADT contains by value.
    fn deps(&self, t: &Type) -> Vec<Type> {
        let mut out: Vec<Type> = self.fields(t).into_iter().map(|(_, t)| t).collect();
        for v in self.variants(t) {
            out.extend(v.into_iter().map(|(_, t)| t));
        }
        out.into_iter().filter(|t| self.is_adt(t)).collect()
    }

    fn collect_type(&self, t: &Type, order: &mut Vec<Type>) {
        if !self.is_adt(t) || order.contains(t) {
            return;
        }
        for d in self.deps(t) {
            self.collect_type(&d, order);
        }
        if !order.contains(t) {
            order.push(t.clone());
        }
    }

    fn type_defs(&self, bodies: &[Body]) -> String {
        let mut order: Vec<Type> = Vec::new();
        for b in bodies {
            for l in &b.locals {
                self.collect_type(&l.ty, &mut order);
            }
            for bb in &b.blocks {
                for Statement::Assign(_, rv) in &bb.stmts {
                    if let Rvalue::Aggregate(agg, _) = rv {
                        let t = match agg {
                            Agg::Struct(t) | Agg::Tuple(t) | Agg::Variant(t, _) => t,
                        };
                        self.collect_type(t, &mut order);
                    }
                }
            }
        }
        let mut c = String::new();
        for t in &order {
            writeln!(c, "typedef struct {n} {n};", n = c_type(t)).unwrap();
        }
        c.push('\n');
        for t in &order {
            let name = c_type(t);
            let variants = self.variants(t);
            if variants.is_empty() {
                writeln!(c, "struct {name} {{").unwrap();
                let fields = self.fields(t);
                if fields.is_empty() {
                    c.push_str("  char _;\n");
                }
                for (f, ft) in fields {
                    writeln!(c, "  {} {f};", c_type(&ft)).unwrap();
                }
                c.push_str("};\n\n");
            } else {
                writeln!(c, "struct {name} {{\n  int32_t tag;").unwrap();
                if variants.iter().any(|v| !v.is_empty()) {
                    c.push_str("  union {\n");
                    for (i, v) in variants.iter().enumerate() {
                        if v.is_empty() {
                            continue;
                        }
                        write!(c, "    struct {{ ").unwrap();
                        for (f, ft) in v {
                            write!(c, "{} {f}; ", c_type(ft)).unwrap();
                        }
                        writeln!(c, "}} v{i};").unwrap();
                    }
                    c.push_str("  } u;\n");
                }
                c.push_str("};\n\n");
            }
        }
        c
    }

    /// C expression for a place and the place's type.
    fn place(&self, b: &Body, p: &Place) -> (String, Type) {
        let mut s = format!("_{}", p.local);
        let mut ty = b.locals[p.local as usize].ty.clone();
        for pr in &p.proj {
            match pr {
                Proj::Field(i) => {
                    let (f, ft) = self.fields(&ty).into_iter().nth(*i).unwrap_or_else(|| panic!("cgen: field {i} of {ty}"));
                    s = format!("{s}.{f}");
                    ty = ft;
                }
                Proj::Downcast(v, i) => {
                    let (f, ft) = self.variants(&ty)[*v][*i].clone();
                    s = format!("{s}.u.v{v}.{f}");
                    ty = ft;
                }
            }
        }
        (s, ty)
    }

    fn operand(&self, b: &Body, o: &Operand) -> (String, Type) {
        match o {
            Operand::Place(p) => self.place(b, p),
            Operand::Const(Const::Int(v)) => (format!("INT64_C({v})"), Type::con("Int")),
            Operand::Const(Const::Float(v)) => {
                let s = if v.is_finite() && v.fract() == 0.0 { format!("{v:.1}") } else { format!("{v:?}") };
                (s, Type::con("Float"))
            }
            Operand::Const(Const::Bool(v)) => (v.to_string(), Type::con("Bool")),
            Operand::Const(Const::Str(s)) => (format!("rush_str_lit({}, {})", c_string_lit(s), s.len()), Type::con("String")),
            Operand::Const(Const::Unit) => ("RUSH_UNIT".to_string(), Type::unit()),
        }
    }

    fn signature(&self, b: &Body) -> String {
        let params: Vec<String> = (1..=b.n_params).map(|i| format!("{} _{i}", c_type(&b.locals[i].ty))).collect();
        let params = if params.is_empty() { "void".to_string() } else { params.join(", ") };
        format!("static {} rush_{}({})", c_type(&b.locals[0].ty), b.name, params)
    }

    fn rvalue(&self, b: &Body, rv: &Rvalue) -> String {
        match rv {
            Rvalue::Use(o) => self.operand(b, o).0,
            Rvalue::Unary(UnOp::Neg, o) => format!("(-{})", self.operand(b, o).0),
            Rvalue::Unary(UnOp::Not, o) => format!("(!{})", self.operand(b, o).0),
            Rvalue::Binary(op, x, y) => {
                let (l, t) = self.operand(b, x);
                let (r, _) = self.operand(b, y);
                let is_int = is_named(&t, "Int");
                let is_str = is_named(&t, "String");
                match op {
                    BinOp::Div if is_int => format!("rush_div_i64({l}, {r})"),
                    BinOp::Rem if is_int => format!("rush_rem_i64({l}, {r})"),
                    BinOp::Rem => format!("fmod({l}, {r})"),
                    BinOp::Add if is_str => format!("rush_str_concat({l}, {r})"),
                    BinOp::Eq if is_str => format!("rush_str_eq({l}, {r})"),
                    BinOp::Ne if is_str => format!("(!rush_str_eq({l}, {r}))"),
                    BinOp::Eq if is_named(&t, "Unit") => "true".into(),
                    BinOp::Ne if is_named(&t, "Unit") => "false".into(),
                    _ => {
                        let sym = match op {
                            BinOp::Add => "+",
                            BinOp::Sub => "-",
                            BinOp::Mul => "*",
                            BinOp::Div => "/",
                            BinOp::Rem => "%",
                            BinOp::Eq => "==",
                            BinOp::Ne => "!=",
                            BinOp::Lt => "<",
                            BinOp::Le => "<=",
                            BinOp::Gt => ">",
                            BinOp::Ge => ">=",
                            BinOp::And => "&&",
                            BinOp::Or => "||",
                        };
                        format!("({l} {sym} {r})")
                    }
                }
            }
            Rvalue::Call(callee, args) => {
                let name = match callee {
                    Callee::Def { name, .. } | Callee::Extern(name) => name,
                    Callee::Trait { .. } => panic!("cgen: unresolved trait call"),
                };
                let args: Vec<String> = args.iter().map(|o| self.operand(b, o).0).collect();
                format!("rush_{name}({})", args.join(", "))
            }
            Rvalue::Discriminant(p) => format!("(int64_t){}.tag", self.place(b, p).0),
            Rvalue::Aggregate(..) => unreachable!("aggregates are emitted as statements"),
        }
    }

    fn body(&self, b: &Body, c: &mut String) {
        writeln!(c, "{} {{", self.signature(b)).unwrap();
        for (i, l) in b.locals.iter().enumerate() {
            if i >= 1 && i <= b.n_params {
                continue;
            }
            writeln!(c, "  {} _{i};", c_type(&l.ty)).unwrap();
        }
        for (i, bb) in b.blocks.iter().enumerate() {
            writeln!(c, "bb{i}:").unwrap();
            for Statement::Assign(place, rv) in &bb.stmts {
                let (target, _) = self.place(b, place);
                match rv {
                    Rvalue::Aggregate(agg, ops) => {
                        let ops: Vec<String> = ops.iter().map(|o| self.operand(b, o).0).collect();
                        match agg {
                            Agg::Struct(t) | Agg::Tuple(t) => {
                                let fields = self.fields(t);
                                if fields.is_empty() {
                                    writeln!(c, "  {target}._ = 0;").unwrap();
                                }
                                for ((f, _), v) in fields.iter().zip(&ops) {
                                    writeln!(c, "  {target}.{f} = {v};").unwrap();
                                }
                            }
                            Agg::Variant(t, idx) => {
                                writeln!(c, "  {target}.tag = {idx};").unwrap();
                                let fields = &self.variants(t)[*idx];
                                for ((f, _), v) in fields.iter().zip(&ops) {
                                    writeln!(c, "  {target}.u.v{idx}.{f} = {v};").unwrap();
                                }
                            }
                        }
                    }
                    _ => writeln!(c, "  {target} = {};", self.rvalue(b, rv)).unwrap(),
                }
            }
            match &bb.term {
                Terminator::Goto(t) => writeln!(c, "  goto bb{t};").unwrap(),
                Terminator::If(cond, a, d) => writeln!(c, "  if ({}) goto bb{a}; else goto bb{d};", self.operand(b, cond).0).unwrap(),
                Terminator::Return => writeln!(c, "  return _0;").unwrap(),
                // rush_unreachable never returns; the trailing return keeps C compilers quiet.
                Terminator::Unreachable => writeln!(c, "  rush_unreachable();\n  return _0;").unwrap(),
            }
        }
        c.push_str("}\n\n");
    }
}

pub fn gen(bodies: &[Body], info: &TypeInfo) -> String {
    let g = Gen { info };
    let mut c = String::new();
    c.push_str("#include \"rush_rt.h\"\n#include <math.h>\n\n");
    c.push_str(&g.type_defs(bodies));
    for b in bodies {
        writeln!(c, "{};", g.signature(b)).unwrap();
    }
    c.push('\n');
    for b in bodies {
        g.body(b, &mut c);
    }
    c.push_str("static void rush_entry(void) {\n  rush_main();\n}\n\nint main(int argc, char **argv) {\n  return rush_rt_run(argc, argv, rush_entry);\n}\n");
    c
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::lex;
    use crate::mono::monomorphize;
    use crate::parser::parse;
    use crate::types::check;

    fn gen_src(s: &str) -> String {
        let prelude = include_str!("../std/prelude.rush");
        let mut id = 0;
        let mut p = parse(lex(prelude).unwrap(), &mut id).unwrap();
        p.items.extend(parse(lex(s).unwrap(), &mut id).unwrap().items);
        let info = check(&p).unwrap();
        let bodies = lower(&p, &info).unwrap();
        let bodies = monomorphize(bodies, &info).unwrap();
        gen(&bodies, &info)
    }

    #[test]
    fn emits_prototype_definition_and_main() {
        let c = gen_src(
            "def fib(n: Int) -> Int\n  if n < 2\n    n\n  else\n    fib(n - 1) + fib(n - 2)\n  end\nend\ndef main\n  puts(int_to_s(fib(10)))\nend\n",
        );
        assert!(c.starts_with("#include \"rush_rt.h\"\n"));
        assert!(c.contains("static int64_t rush_fib(int64_t _1);\n"));
        assert!(c.contains("static rush_unit rush_main(void);\n"));
        assert!(c.contains("static int64_t rush_fib(int64_t _1) {\n"));
        assert!(c.contains("  _2 = (_1 < INT64_C(2));\n"));
        assert!(c.contains("  if (_2) goto bb1; else goto bb2;\n"));
        assert!(c.contains("  _5 = rush_fib(_4);\n"));
        assert!(c.contains("  return _0;\n"));
        assert!(c.contains("int main(int argc, char **argv) {\n  return rush_rt_run(argc, argv, rush_entry);\n}\n"));
    }

    #[test]
    fn string_literals_are_octal_escaped_with_length() {
        let c = gen_src("def main\n  puts(\"a\\\"b\\n\")\nend\n");
        assert!(c.contains("rush_str_lit(\"a\\042b\\012\", 4)"), "{c}");
    }

    #[test]
    fn division_and_string_equality_call_the_runtime() {
        let c = gen_src("def main\n  let a = 7 / 2\n  let b = 7 % 2\n  let c = \"x\" == \"y\"\n  let d = \"x\" + \"y\"\n  ()\nend\n");
        assert!(c.contains("rush_div_i64("));
        assert!(c.contains("rush_rem_i64("));
        assert!(c.contains("rush_str_eq("));
        assert!(c.contains("rush_str_concat("));
    }

    #[test]
    fn float_division_is_inline() {
        let c = gen_src("def main\n  let a = 7.0 / 2.0\n  ()\nend\n");
        assert!(c.contains(" / "));
        assert!(!c.contains("rush_div_i64"));
    }

    #[test]
    fn unit_and_bool_constants() {
        let c = gen_src("def main\n  let u = ()\n  let b = not true\n  ()\nend\n");
        assert!(c.contains("RUSH_UNIT"));
        assert!(c.contains("(!true)"));
    }

    #[test]
    fn struct_enum_and_tuple_definitions_in_dependency_order() {
        let src = "struct P\n  x: Int\nend\nenum S\n  C(P)\n  R(P, (Int, Bool))\n  E\nend\ndef main\n  let s = R(P { x: 1 }, (2, true))\n  case s\n  in C(p) then p.x\n  in R(p, t) then t.0\n  in E then 0\n  end\n  ()\nend\n";
        let c = gen_src(src);
        let p = c.find("struct rush_P {").unwrap();
        let t = c.find("struct rush_Tuple_L_Int__Bool_R {").unwrap();
        let s = c.find("struct rush_S {").unwrap();
        assert!(p < s && t < s, "{c}");
        assert!(c.contains("typedef struct rush_S rush_S;"));
        assert!(c.contains("  int32_t tag;\n  union {\n    struct { rush_P f0; } v0;\n    struct { rush_P f0; rush_Tuple_L_Int__Bool_R f1; } v1;\n  } u;\n"), "{c}");
        assert!(c.contains(".tag = 1;"), "{c}");
        assert!(c.contains(".u.v1.f1 = _"), "{c}");
        assert!(c.contains(".tag;"), "{c}");
        assert!(c.contains(".u.v1.f1;"), "{c}");
        assert!(c.contains(".f0;"), "{c}");
    }

    #[test]
    fn unit_only_enum_has_no_union() {
        let c = gen_src("enum Color\n  Red\n  Blue\nend\ndef main\n  let c = Red\n  ()\nend\n");
        assert!(c.contains("struct rush_Color {\n  int32_t tag;\n};"), "{c}");
    }
}
