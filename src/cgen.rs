use std::fmt::Write;

use crate::ast::{BinOp, UnOp};
use crate::mir::*;
use crate::types::{Type, TypeInfo};

fn c_type(t: &Type) -> &'static str {
    match t {
        Type::Con(n, _) => match n.as_str() {
            "Int" => "int64_t",
            "Float" => "double",
            "Bool" => "bool",
            "String" => "rush_str",
            "Unit" => "rush_unit",
            _ => panic!("cgen: unsupported type {t}"),
        },
        _ => panic!("cgen: non-ground type {t}"),
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

fn operand(o: &Operand) -> String {
    match o {
        Operand::Local(id) => format!("_{id}"),
        Operand::Const(Const::Int(v)) => format!("INT64_C({v})"),
        Operand::Const(Const::Float(v)) => {
            if v.is_finite() && v.fract() == 0.0 { format!("{v:.1}") } else { format!("{v:?}") }
        }
        Operand::Const(Const::Bool(v)) => v.to_string(),
        Operand::Const(Const::Str(s)) => format!("rush_str_lit({}, {})", c_string_lit(s), s.len()),
        Operand::Const(Const::Unit) => "RUSH_UNIT".to_string(),
    }
}

fn operand_type(b: &Body, o: &Operand) -> Type {
    match o {
        Operand::Local(id) => b.locals[*id as usize].ty.clone(),
        Operand::Const(Const::Int(_)) => Type::con("Int"),
        Operand::Const(Const::Float(_)) => Type::con("Float"),
        Operand::Const(Const::Bool(_)) => Type::con("Bool"),
        Operand::Const(Const::Str(_)) => Type::con("String"),
        Operand::Const(Const::Unit) => Type::unit(),
    }
}

fn signature(b: &Body) -> String {
    let params: Vec<String> = (1..=b.n_params).map(|i| format!("{} _{i}", c_type(&b.locals[i].ty))).collect();
    let params = if params.is_empty() { "void".to_string() } else { params.join(", ") };
    format!("static {} rush_{}({})", c_type(&b.locals[0].ty), b.name, params)
}

fn rvalue(b: &Body, rv: &Rvalue) -> String {
    match rv {
        Rvalue::Use(o) => operand(o),
        Rvalue::Unary(UnOp::Neg, o) => format!("(-{})", operand(o)),
        Rvalue::Unary(UnOp::Not, o) => format!("(!{})", operand(o)),
        Rvalue::Binary(op, x, y) => {
            let t = operand_type(b, x);
            let (l, r) = (operand(x), operand(y));
            let is_int = is_named(&t, "Int");
            match op {
                BinOp::Div if is_int => format!("rush_div_i64({l}, {r})"),
                BinOp::Rem if is_int => format!("rush_rem_i64({l}, {r})"),
                BinOp::Rem => format!("fmod({l}, {r})"),
                BinOp::Eq if is_named(&t, "String") => format!("rush_str_eq({l}, {r})"),
                BinOp::Ne if is_named(&t, "String") => format!("(!rush_str_eq({l}, {r}))"),
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
                Callee::Def(n) | Callee::Extern(n) => n,
            };
            let args: Vec<String> = args.iter().map(operand).collect();
            format!("rush_{name}({})", args.join(", "))
        }
    }
}

pub fn gen(bodies: &[Body], _info: &TypeInfo) -> String {
    let mut c = String::new();
    c.push_str("#include \"rush_rt.h\"\n#include <math.h>\n\n");
    for b in bodies {
        writeln!(c, "{};", signature(b)).unwrap();
    }
    c.push('\n');
    for b in bodies {
        writeln!(c, "{} {{", signature(b)).unwrap();
        for (i, l) in b.locals.iter().enumerate() {
            if i >= 1 && i <= b.n_params {
                continue;
            }
            writeln!(c, "  {} _{i};", c_type(&l.ty)).unwrap();
        }
        for (i, bb) in b.blocks.iter().enumerate() {
            writeln!(c, "bb{i}:").unwrap();
            for st in &bb.stmts {
                let Statement::Assign(id, rv) = st;
                writeln!(c, "  _{id} = {};", rvalue(b, rv)).unwrap();
            }
            match &bb.term {
                Terminator::Goto(t) => writeln!(c, "  goto bb{t};").unwrap(),
                Terminator::If(cond, a, d) => {
                    writeln!(c, "  if ({}) goto bb{a}; else goto bb{d};", operand(cond)).unwrap()
                }
                Terminator::Return => writeln!(c, "  return _0;").unwrap(),
                // rush_unreachable never returns; the trailing return keeps C compilers quiet.
                Terminator::Unreachable => writeln!(c, "  rush_unreachable();\n  return _0;").unwrap(),
            }
        }
        c.push_str("}\n\n");
    }
    c.push_str("int main(int argc, char **argv) {\n  rush_rt_init(argc, argv);\n  rush_main();\n  return 0;\n}\n");
    c
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::lex;
    use crate::parser::parse;
    use crate::types::check;

    fn gen_src(s: &str) -> String {
        let prelude = include_str!("../std/prelude.rush");
        let mut id = 0;
        let mut p = parse(lex(prelude).unwrap(), &mut id).unwrap();
        p.items.extend(parse(lex(s).unwrap(), &mut id).unwrap().items);
        let info = check(&p).unwrap();
        let bodies = lower(&p, &info).unwrap();
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
        assert!(c.contains("int main(int argc, char **argv) {\n  rush_rt_init(argc, argv);\n  rush_main();\n  return 0;\n}\n"));
    }

    #[test]
    fn string_literals_are_octal_escaped_with_length() {
        let c = gen_src("def main\n  puts(\"a\\\"b\\n\")\nend\n");
        assert!(c.contains("rush_str_lit(\"a\\042b\\012\", 4)"), "{c}");
    }

    #[test]
    fn division_and_string_equality_call_the_runtime() {
        let c = gen_src("def main\n  let a = 7 / 2\n  let b = 7 % 2\n  let c = \"x\" == \"y\"\n  ()\nend\n");
        assert!(c.contains("rush_div_i64("));
        assert!(c.contains("rush_rem_i64("));
        assert!(c.contains("rush_str_eq("));
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
}
