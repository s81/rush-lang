use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use crate::ast::Item;
use crate::{borrowck, cgen, derive, diag, lexer, mir, mono, ownck, parser, types};

const PRELUDE: &str = include_str!("../std/prelude.rush");
const RT_C: &str = include_str!("../runtime/rush_rt.c");
const RT_H: &str = include_str!("../runtime/rush_rt.h");

#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Build,
    Run,
    Test,
}

const USAGE: &str = "\
rush - a compiled language with Go-style binaries, Haskell-style types,
       Rust-style ownership, and Ruby-style syntax

usage:
  rush build <file.rush> [--debug]   compile to an executable next to the source
  rush run <file.rush> [--debug]     compile and run
  rush test <file.rush> [--debug]    run every top-level `def test_*`

options:
  -h, --help                        show this help
  -V, --version                     show the version

environment:
  RUSH_CC                           C compiler command (default: cc, gcc, clang, tcc, or zig cc)
";

fn version() -> String {
    format!("rush {}", env!("CARGO_PKG_VERSION"))
}

pub fn main(args: Vec<String>) -> i32 {
    match args.first().map(String::as_str) {
        Some("build") => build(&args[1..], Mode::Build),
        Some("run") => build(&args[1..], Mode::Run),
        Some("test") => build(&args[1..], Mode::Test),
        Some("-h" | "--help") => {
            print!("{USAGE}");
            0
        }
        Some("-V" | "--version") => {
            println!("{}", version());
            0
        }
        Some(other) if !other.starts_with('-') => {
            eprintln!("error: unknown command `{other}`");
            eprint!("{USAGE}");
            2
        }
        _ => {
            eprint!("{USAGE}");
            2
        }
    }
}

struct Compiled {
    c: String,
    tests: Vec<String>,
}

/// Runs the whole front end and returns C source, or a rendered diagnostic.
pub fn compile_to_c(path: &str, src: &str, debug: bool) -> Result<String, String> {
    compile(path, src, debug, false).map(|c| c.c)
}

fn compile(path: &str, src: &str, debug: bool, test: bool) -> Result<Compiled, String> {
    let go = || -> Result<Compiled, diag::Diagnostic> {
        let mut id = 0;
        let mut prog = parser::parse(lexer::lex(PRELUDE)?, &mut id)?;
        let user = parser::parse(lexer::lex(src)?, &mut id)?;
        // `rush test` runs every top-level `def test_*` with no receiver, parameters, or
        // generics. Test files do not need a `main`; add a placeholder so type checking and
        // the rest of the pipeline see the usual entry point.
        let tests: Vec<String> = user
            .items
            .iter()
            .filter_map(|item| match item {
                Item::Def(d)
                    if d.name.starts_with("test_")
                        && d.generics.params.is_empty()
                        && d.self_param.is_none()
                        && d.params.is_empty() =>
                {
                    Some(d.name.clone())
                }
                _ => None,
            })
            .collect();
        prog.items.extend(user.items);
        if test && !prog.items.iter().any(|item| matches!(item, Item::Def(d) if d.name == "main")) {
            prog.items.extend(parser::parse(lexer::lex("def main\n  ()\nend\n")?, &mut id)?.items);
        }
        derive::expand(&mut prog, &mut id)?;
        let info = types::check(&prog)?;
        let mut bodies = mir::lower(&prog, &info)?;
        ownck::check_and_insert_drops(&mut bodies, &info)?;
        borrowck::check(&mut bodies, &info)?;
        let roots = if test {
            tests.iter().map(|t| (t.clone(), vec![])).collect()
        } else {
            vec![("main".into(), vec![])]
        };
        let bodies = mono::monomorphize_from(bodies, &info, roots)?;
        let c = if test { cgen::gen_tests(&bodies, &info, debug, &tests) } else { cgen::gen(&bodies, &info, debug) };
        Ok(Compiled { c, tests })
    };
    go().map_err(|d| diag::render(path, src, &d))
}

/// Splits `RUSH_CC` like a small shell: whitespace separates arguments, single and double
/// quotes group them, and a backslash escapes whitespace, quotes, or another backslash.
/// Backslashes in Windows paths are otherwise preserved.
fn split_command(s: &str) -> Result<Vec<String>, String> {
    let mut out = Vec::new();
    let mut cur = String::new();
    let mut started = false;
    let mut quote: Option<char> = None;
    let mut chars = s.chars();
    while let Some(c) = chars.next() {
        match quote {
            Some(q) => {
                if c == q {
                    quote = None;
                } else if c == '\\' && q == '"' {
                    match chars.next() {
                        Some(n @ ('"' | '\\')) => cur.push(n),
                        Some(n) => {
                            cur.push('\\');
                            cur.push(n);
                        }
                        None => return Err("RUSH_CC ends with a backslash".into()),
                    }
                } else {
                    cur.push(c);
                }
            }
            None => match c {
                '\'' | '"' => {
                    quote = Some(c);
                    started = true;
                }
                '\\' => match chars.next() {
                    Some(n @ (' ' | '\t' | '\r' | '\n' | '\'' | '"' | '\\')) => {
                        cur.push(n);
                        started = true;
                    }
                    Some(n) => {
                        cur.push('\\');
                        cur.push(n);
                        started = true;
                    }
                    None => return Err("RUSH_CC ends with a backslash".into()),
                },
                c if c.is_whitespace() => {
                    if started {
                        out.push(std::mem::take(&mut cur));
                        started = false;
                    }
                }
                _ => {
                    cur.push(c);
                    started = true;
                }
            },
        }
    }
    if let Some(q) = quote {
        return Err(format!("RUSH_CC has an unterminated {q} quote"));
    }
    if started {
        out.push(cur);
    }
    if out.is_empty() {
        return Err("RUSH_CC is empty".into());
    }
    if out[0].is_empty() {
        return Err("RUSH_CC has an empty command".into());
    }
    Ok(out)
}

fn find_cc() -> Result<Option<Vec<String>>, String> {
    if let Ok(cc) = std::env::var("RUSH_CC") {
        return split_command(&cc).map(Some);
    }
    let candidates: [&[&str]; 5] = [&["cc"], &["gcc"], &["clang"], &["tcc"], &["zig", "cc"]];
    for cand in candidates {
        let ok = Command::new(cand[0])
            .args(&cand[1..])
            .arg("-v")
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .map(|s| s.success())
            .unwrap_or(false);
        if ok {
            return Ok(Some(cand.iter().map(|s| s.to_string()).collect()));
        }
    }
    Ok(None)
}

fn build(args: &[String], mode: Mode) -> i32 {
    if args.iter().any(|a| a == "-h" || a == "--help") {
        print!("{USAGE}");
        return 0;
    }
    if args.iter().any(|a| a == "-V" || a == "--version") {
        println!("{}", version());
        return 0;
    }
    let Some(path) = args.iter().find(|a| !a.starts_with("--")) else {
        eprintln!("error: no input file");
        return 2;
    };
    let debug = args.iter().any(|a| a == "--debug");
    let src = match std::fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: cannot read {path}: {e}");
            return 2;
        }
    };
    let compiled = match compile(path, &src, debug, mode == Mode::Test) {
        Ok(c) => c,
        Err(msg) => {
            eprint!("{msg}");
            return 1;
        }
    };
    if mode == Mode::Test && compiled.tests.is_empty() {
        println!("no tests found in {path}");
        return 0;
    }
    let src_path = Path::new(path);
    let stem = src_path.file_stem().unwrap().to_string_lossy().to_string();
    let parent = src_path.parent().filter(|p| !p.as_os_str().is_empty()).unwrap_or(Path::new("."));
    let build_dir = parent.join(".rush-build");
    let exe: PathBuf = parent.join(if cfg!(windows) { format!("{stem}.exe") } else { stem.clone() });
    let write = |name: &str, data: &str| std::fs::write(build_dir.join(name), data);
    if let Err(e) = std::fs::create_dir_all(&build_dir)
        .and_then(|_| write(&format!("{stem}.c"), &compiled.c))
        .and_then(|_| write("rush_rt.c", RT_C))
        .and_then(|_| write("rush_rt.h", RT_H))
    {
        eprintln!("error: cannot write build directory {}: {e}", build_dir.display());
        return 2;
    }
    let cc = match find_cc() {
        Ok(Some(cc)) => cc,
        Ok(None) => {
            eprintln!("error: no C compiler found; install gcc, clang, or tcc, or set RUSH_CC");
            return 2;
        }
        Err(e) => {
            eprintln!("error: {e}");
            return 2;
        }
    };
    let mut cmd = Command::new(&cc[0]);
    cmd.args(&cc[1..]);
    cmd.arg("-std=c99");
    if debug {
        cmd.args(["-O0", "-g"]);
    } else {
        cmd.arg("-O2");
    }
    cmd.arg("-I").arg(&build_dir);
    cmd.arg("-o").arg(&exe);
    cmd.arg(build_dir.join(format!("{stem}.c")));
    cmd.arg(build_dir.join("rush_rt.c"));
    if !cfg!(windows) {
        cmd.arg("-lm");
    }
    match cmd.status() {
        Ok(s) if s.success() => {}
        Ok(s) => {
            eprintln!("error: C compiler exited with {s}");
            return 1;
        }
        Err(e) => {
            eprintln!("error: cannot run {}: {e}", cc[0]);
            return 2;
        }
    }
    if mode == Mode::Build {
        return 0;
    }
    let exe_abs = std::fs::canonicalize(&exe).unwrap_or(exe);
    if mode == Mode::Run {
        return match Command::new(&exe_abs).status() {
            Ok(s) => s.code().unwrap_or(1),
            Err(e) => {
                eprintln!("error: cannot run {}: {e}", exe_abs.display());
                2
            }
        };
    }
    run_tests(&exe_abs, &compiled.tests)
}

/// Runs each test in a fresh process, so a panic or `abort` only fails that test.
fn run_tests(exe: &Path, tests: &[String]) -> i32 {
    println!("running {} test{}", tests.len(), if tests.len() == 1 { "" } else { "s" });
    let mut failed = 0usize;
    for test in tests {
        match Command::new(exe).arg(test).output() {
            Ok(out) if out.status.success() => println!("test {test} ... ok"),
            Ok(out) => {
                failed += 1;
                println!("test {test} ... FAILED");
                let stdout = String::from_utf8_lossy(&out.stdout).replace("\r\n", "\n");
                let stderr = String::from_utf8_lossy(&out.stderr).replace("\r\n", "\n");
                if !stdout.is_empty() {
                    println!("---- {test} stdout ----\n{stdout}");
                }
                if !stderr.is_empty() {
                    println!("---- {test} stderr ----\n{stderr}");
                }
            }
            Err(e) => {
                failed += 1;
                println!("test {test} ... FAILED\n  cannot run {}: {e}", exe.display());
            }
        }
    }
    let passed = tests.len() - failed;
    println!("\n{passed} passed, {failed} failed");
    i32::from(failed != 0)
}

#[cfg(test)]
mod tests {
    use super::split_command;

    #[test]
    fn rush_cc_splits_quotes_and_keeps_windows_paths() {
        assert_eq!(split_command("gcc").unwrap(), vec!["gcc"]);
        assert_eq!(split_command(" cc -O2 ").unwrap(), vec!["cc", "-O2"]);
        assert_eq!(split_command("cc -DMSG=\"a b\"").unwrap(), vec!["cc", "-DMSG=a b"]);
        assert_eq!(
            split_command(r#""C:\Program Files\LLVM\bin\clang.exe" -O2"#).unwrap(),
            vec![r"C:\Program Files\LLVM\bin\clang.exe", "-O2"]
        );
        assert_eq!(split_command(r"C:\tools\cc.exe").unwrap(), vec![r"C:\tools\cc.exe"]);
        assert_eq!(split_command(r#"cc "a\"b""#).unwrap(), vec!["cc", "a\"b"]);
        // An escaped space is part of the argument, not a separator.
        assert_eq!(split_command("cc\\ -O2").unwrap(), vec!["cc -O2"]);
        assert_eq!(split_command("cc 'a b'").unwrap(), vec!["cc", "a b"]);
    }

    #[test]
    fn rush_cc_rejects_empty_and_malformed_values() {
        assert_eq!(split_command("").unwrap_err(), "RUSH_CC is empty");
        assert_eq!(split_command("   ").unwrap_err(), "RUSH_CC is empty");
        assert_eq!(split_command("\"\"").unwrap_err(), "RUSH_CC has an empty command");
        assert_eq!(split_command("cc \"x").unwrap_err(), "RUSH_CC has an unterminated \" quote");
        assert_eq!(split_command("cc 'x").unwrap_err(), "RUSH_CC has an unterminated ' quote");
        assert_eq!(split_command("cc\\").unwrap_err(), "RUSH_CC ends with a backslash");
    }
}
