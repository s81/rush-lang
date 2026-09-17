//! C99 emission from monomorphized MIR.

use std::collections::{HashMap, HashSet};
use std::fmt::Write;

use crate::ast::{BinOp, UnOp};
use crate::mir::*;
use crate::mono::mangle_type;
use crate::types::{subst, Type, TypeInfo};

fn c_type(t: &Type) -> String {
    match t {
        Type::Con(n, args) if n == "&" || n == "&mut" || n == "Gc" => format!("{}*", c_type(&args[0])),
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

fn is_pointer(t: &Type) -> bool {
    matches!(t, Type::Con(n, _) if n == "&" || n == "&mut" || n == "Gc")
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
    debug: bool,
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

    /// Types this ADT contains, split into by-value (ordering) and by-pointer.
    fn deps(&self, t: &Type) -> (Vec<Type>, Vec<Type>) {
        let mut all: Vec<Type> = self.fields(t).into_iter().map(|(_, t)| t).collect();
        for v in self.variants(t) {
            all.extend(v.into_iter().map(|(_, t)| t));
        }
        let mut by_value = Vec::new();
        let mut by_ptr = Vec::new();
        for d in all {
            if is_pointer(&d) {
                by_ptr.push(d);
            } else if self.is_adt(&d) {
                by_value.push(d);
            }
        }
        (by_value, by_ptr)
    }

    fn collect_type(&self, t: &Type, order: &mut Vec<Type>, visiting: &mut HashSet<Type>) {
        let t = strip_pointers(t);
        if !self.is_adt(&t) || order.contains(&t) || !visiting.insert(t.clone()) {
            return;
        }
        let (by_value, by_ptr) = self.deps(&t);
        for d in by_value {
            self.collect_type(&d, order, visiting);
        }
        order.push(t.clone());
        for d in by_ptr {
            self.collect_type(&d, order, visiting);
        }
    }

    fn all_types(&self, bodies: &[Body]) -> Vec<Type> {
        let mut order: Vec<Type> = Vec::new();
        let mut visiting = HashSet::new();
        for b in bodies {
            for l in &b.locals {
                self.collect_type(&l.ty, &mut order, &mut visiting);
            }
            for bb in &b.blocks {
                for s in &bb.stmts {
                    if let Statement::Assign(_, rv, _) = s {
                        match rv {
                            Rvalue::Aggregate(agg, _) => {
                                let t = match agg {
                                    Agg::Struct(t) | Agg::Tuple(t) | Agg::Variant(t, _) => t,
                                };
                                self.collect_type(t, &mut order, &mut visiting);
                            }
                            Rvalue::Call(Callee::Def { name, targs }, _) if name == "Gc::new" => {
                                self.collect_type(&targs[0], &mut order, &mut visiting);
                            }
                            _ => {}
                        }
                    }
                }
            }
        }
        order
    }

    fn type_defs(&self, order: &[Type]) -> String {
        let mut c = String::new();
        for t in order {
            writeln!(c, "typedef struct {n} {n};", n = c_type(t)).unwrap();
        }
        c.push('\n');
        for t in order {
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

    /// Droppable types reachable from the bodies, for which drop glue is emitted.
    fn drop_types(&self, bodies: &[Body], order: &[Type]) -> Vec<Type> {
        let mut out: Vec<Type> = Vec::new();
        let consider = |t: &Type, out: &mut Vec<Type>| {
            let t = strip_pointers(t);
            if self.info.needs_drop(&t) && !out.contains(&t) {
                out.push(t);
            }
        };
        for t in order {
            consider(t, &mut out);
        }
        for b in bodies {
            for l in &b.locals {
                consider(&l.ty, &mut out);
            }
            for bb in &b.blocks {
                for s in &bb.stmts {
                    match s {
                        Statement::Drop(p, _) => consider(&place_type(self.info, b, p), &mut out),
                        Statement::Assign(_, Rvalue::Call(Callee::Def { name, targs }, _), _) if name == "Gc::new" => consider(&targs[0], &mut out),
                        _ => {}
                    }
                }
            }
        }
        // Fields of droppable types need glue too.
        let mut i = 0;
        while i < out.len() {
            let t = out[i].clone();
            for (_, ft) in self.fields(&t) {
                consider(&ft, &mut out);
            }
            for v in self.variants(&t) {
                for (_, ft) in v {
                    consider(&ft, &mut out);
                }
            }
            i += 1;
        }
        out
    }

    fn drop_fn_name(t: &Type) -> String {
        format!("rush_drop_{}", mangle_type(t))
    }

    fn drop_glue(&self, types: &[Type]) -> String {
        let mut c = String::new();
        for t in types {
            writeln!(c, "static void {}(void *vp);", Self::drop_fn_name(t)).unwrap();
        }
        c.push('\n');
        for t in types {
            writeln!(c, "static void {}(void *vp) {{", Self::drop_fn_name(t)).unwrap();
            if is_named(t, "String") {
                c.push_str("  rush_str_drop((rush_str *)vp);\n}\n\n");
                continue;
            }
            writeln!(c, "  {ct} *v = ({ct} *)vp;", ct = c_type(t)).unwrap();
            if let Some((id, map)) = self.info.impl_for("Drop", t) {
                let imp = &self.info.impls[id];
                let targs: Vec<Type> = imp.generics.iter().map(|g| map[g].clone()).collect();
                writeln!(c, "  rush_{}(v);", crate::mono::mangle_fn(&imp.methods["drop"], &targs)).unwrap();
            }
            let variants = self.variants(t);
            if variants.is_empty() {
                for (f, ft) in self.fields(t) {
                    if self.info.needs_drop(&ft) {
                        writeln!(c, "  {}(&v->{f});", Self::drop_fn_name(&ft)).unwrap();
                    }
                }
            } else {
                c.push_str("  switch (v->tag) {\n");
                for (i, v) in variants.iter().enumerate() {
                    writeln!(c, "  case {i}:").unwrap();
                    for (f, ft) in v {
                        if self.info.needs_drop(ft) {
                            writeln!(c, "    {}(&v->u.v{i}.{f});", Self::drop_fn_name(ft)).unwrap();
                        }
                    }
                    c.push_str("    break;\n");
                }
                c.push_str("  default: break;\n  }\n");
            }
            c.push_str("}\n\n");
        }
        c
    }

    /// C expression for a place and the place's type.
    fn place(&self, b: &Body, p: &Place) -> (String, Type) {
        let mut s = format!("_{}", p.local);
        let mut ty = b.locals[p.local as usize].ty.clone();
        for pr in &p.proj {
            match pr {
                Proj::Deref => {
                    let Type::Con(_, args) = &ty else { panic!("cgen: deref of {ty}") };
                    ty = args[0].clone();
                    s = format!("(*{s})");
                }
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
            Rvalue::MoveOut(p) => self.place(b, p).0,
            Rvalue::Ref(_, p) => format!("&{}", self.place(b, p).0),
            Rvalue::Unary(UnOp::Neg, o) => format!("(-{})", self.operand(b, o).0),
            Rvalue::Unary(UnOp::Not, o) => format!("(!{})", self.operand(b, o).0),
            Rvalue::Binary(op, x, y) => {
                let (l, t) = self.operand(b, x);
                let (r, _) = self.operand(b, y);
                let is_int = is_named(&t, "Int");
                let is_str = is_named(&t, "String");
                match op {
                    BinOp::Add if is_int && self.debug => format!("rush_add_i64_checked({l}, {r})"),
                    BinOp::Sub if is_int && self.debug => format!("rush_sub_i64_checked({l}, {r})"),
                    BinOp::Mul if is_int && self.debug => format!("rush_mul_i64_checked({l}, {r})"),
                    BinOp::Div if is_int => format!("rush_div_i64({l}, {r})"),
                    BinOp::Rem if is_int => format!("rush_rem_i64({l}, {r})"),
                    BinOp::Rem => format!("fmod({l}, {r})"),
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
            for s in &bb.stmts {
                match s {
                    Statement::Drop(p, _) => {
                        let (expr, ty) = self.place(b, p);
                        if self.info.needs_drop(&ty) {
                            writeln!(c, "  {}(&{expr});", Self::drop_fn_name(&ty)).unwrap();
                        }
                    }
                    Statement::Assign(place, rv, _) => {
                        let (target, tty) = self.place(b, place);
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
                            Rvalue::Call(Callee::Def { name, targs }, ops) if name == "Gc::new" => {
                                let pt = &targs[0];
                                let drop = if self.info.needs_drop(pt) { Self::drop_fn_name(pt) } else { "NULL".into() };
                                let (v, _) = self.operand(b, &ops[0]);
                                writeln!(c, "  {target} = ({ct} *)rush_gc_alloc(sizeof({ct}), {drop});\n  *{target} = {v};", ct = c_type(pt)).unwrap();
                            }
                            Rvalue::Call(Callee::Def { name, .. }, ops) if name == "Gc::borrow" || name == "Gc::borrow_mut" => {
                                let (g, _) = self.operand(b, &ops[0]);
                                writeln!(c, "  {target} = *{g};").unwrap();
                            }
                            _ => {
                                let _ = tty;
                                writeln!(c, "  {target} = {};", self.rvalue(b, rv)).unwrap()
                            }
                        }
                    }
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

fn strip_pointers(t: &Type) -> Type {
    let mut t = t.clone();
    loop {
        match &t {
            Type::Con(n, args) if n == "&" || n == "&mut" || n == "Gc" => t = args[0].clone(),
            _ => return t,
        }
    }
}

pub fn gen(bodies: &[Body], info: &TypeInfo, debug: bool) -> String {
    let g = Gen { info, debug };
    let mut c = String::new();
    c.push_str("#include \"rush_rt.h\"\n#include <math.h>\n#include <stdlib.h>\n\n");
    let order = g.all_types(bodies);
    c.push_str(&g.type_defs(&order));
    let drops = g.drop_types(bodies, &order);
    c.push_str(&g.drop_glue(&drops));
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

    fn gen_src_dbg(s: &str, debug: bool) -> String {
        let prelude = include_str!("../std/prelude.rush");
        let mut id = 0;
        let mut p = parse(lex(prelude).unwrap(), &mut id).unwrap();
        p.items.extend(parse(lex(s).unwrap(), &mut id).unwrap().items);
        crate::derive::expand(&mut p, &mut id).unwrap();
        let info = check(&p).unwrap();
        let mut bodies = lower(&p, &info).unwrap();
        crate::ownck::check_and_insert_drops(&mut bodies, &info).unwrap();
        let bodies = monomorphize(bodies, &info).unwrap();
        gen(&bodies, &info, debug)
    }

    fn gen_src(s: &str) -> String {
        gen_src_dbg(s, false)
    }

    #[test]
    fn emits_prototype_definition_and_main() {
        let c = gen_src(
            "def fib(n: Int) -> Int\n  if n < 2\n    n\n  else\n    fib(n - 1) + fib(n - 2)\n  end\nend\ndef main\n  puts(int_to_s(fib(10)))\nend\n",
        );
        assert!(c.starts_with("#include \"rush_rt.h\"\n"));
        assert!(c.contains("static int64_t rush_fib(int64_t _1);\n"));
        assert!(c.contains("static rush_unit rush_main(void);\n"));
        assert!(c.contains("  _2 = (_1 < INT64_C(2));\n"));
        assert!(c.contains("  if (_2) goto bb1; else goto bb2;\n"));
        assert!(c.contains("  _5 = rush_fib(_4);\n"));
        assert!(c.contains("int main(int argc, char **argv) {\n  return rush_rt_run(argc, argv, rush_entry);\n}\n"));
    }

    #[test]
    fn string_literals_are_octal_escaped_with_length() {
        let c = gen_src("def main\n  puts(\"a\\\"b\\n\")\nend\n");
        assert!(c.contains("rush_str_lit(\"a\\042b\\012\", 4)"), "{c}");
    }

    #[test]
    fn division_and_string_ops_call_the_runtime() {
        let c = gen_src("def main\n  let a = 7 / 2\n  let b = 7 % 2\n  let c = \"x\" == \"y\"\n  let d = \"x\" + \"y\"\n  ()\nend\n");
        assert!(c.contains("rush_div_i64("));
        assert!(c.contains("rush_rem_i64("));
        assert!(c.contains("rush_str_eq("));
        assert!(c.contains("rush_str_concat(_"), "{c}");
    }

    #[test]
    fn struct_enum_and_tuple_definitions_in_dependency_order() {
        let src = "struct P\n  x: Int\nend\nenum S\n  C(P)\n  R(P, (Int, Bool))\n  E\nend\ndef main\n  let s = R(P { x: 1 }, (2, true))\n  case s\n  in C(p) then p.x\n  in R(p, t) then t.0\n  in E then 0\n  end\n  ()\nend\n";
        let c = gen_src(src);
        let p = c.find("struct rush_P {").unwrap();
        let t = c.find("struct rush_Tuple_L_Int__Bool_R {").unwrap();
        let s = c.find("struct rush_S {").unwrap();
        assert!(p < s && t < s, "{c}");
        assert!(c.contains("  int32_t tag;\n  union {\n    struct { rush_P f0; } v0;\n    struct { rush_P f0; rush_Tuple_L_Int__Bool_R f1; } v1;\n  } u;\n"), "{c}");
    }

    #[test]
    fn references_derefs_and_drop_glue() {
        let src = "struct Person\n  derive Clone\n  name: String\n  age: Int\nend\nimpl Drop for Person\n  def drop(&mut self)\n    @age = 0\n  end\nend\ndef age_of(p: &Person) -> Int\n  p.age\nend\ndef main\n  let p = Person { name: \"a\", age: 1 }\n  let o = Some(p.clone)\n  let n = age_of(&p)\n  ()\nend\n";
        let c = gen_src(src);
        assert!(c.contains("static int64_t rush_age_of(rush_Person* _1)"), "{c}");
        assert!(c.contains("(*_1).f_age"), "{c}");
        assert!(c.contains("static void rush_drop_Person(void *vp) {"), "{c}");
        assert!(c.contains("rush_str_drop((rush_str *)vp)"), "{c}");
        assert!(c.contains("_drop(v);"), "{c}");
        assert!(c.contains("rush_drop_String(&v->f_name);"), "{c}");
        assert!(c.contains("static void rush_drop_Option_L_Person_R(void *vp) {"), "{c}");
        assert!(c.contains("switch (v->tag)"), "{c}");
        assert!(c.contains("rush_drop_Person(&_"), "{c}");
    }

    #[test]
    fn gc_intrinsics_and_debug_arithmetic() {
        let c = gen_src_dbg("def main\n  let g = Gc.new(\"s\")\n  let r = g.borrow\n  let n = 1 + 2 * 3\n  ()\nend\n", true);
        assert!(c.contains("rush_gc_alloc(sizeof(rush_str), rush_drop_String)"), "{c}");
        assert!(c.contains(" = *_"), "{c}");
        assert!(c.contains("rush_add_i64_checked("), "{c}");
        assert!(c.contains("rush_mul_i64_checked("), "{c}");
        let c2 = gen_src("def main\n  let n = 1 + 2\n  ()\nend\n");
        assert!(!c2.contains("checked"), "{c2}");
    }
}
