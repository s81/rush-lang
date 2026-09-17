use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use crate::{cgen, diag, lexer, mir, mono, parser, types};

const PRELUDE: &str = include_str!("../std/prelude.rush");
const RT_C: &str = include_str!("../runtime/rush_rt.c");
const RT_H: &str = include_str!("../runtime/rush_rt.h");

pub fn main(args: Vec<String>) -> i32 {
    match args.first().map(String::as_str) {
        Some("build") => build(&args[1..], false),
        Some("run") => build(&args[1..], true),
        _ => {
            eprintln!("usage: rush build <file.rush> [--debug]\n       rush run <file.rush> [--debug]");
            2
        }
    }
}

/// Runs the whole front end and returns C source, or a rendered diagnostic.
pub fn compile_to_c(path: &str, src: &str) -> Result<String, String> {
    let go = || -> Result<String, diag::Diagnostic> {
        let mut id = 0;
        let mut prog = parser::parse(lexer::lex(PRELUDE)?, &mut id)?;
        prog.items.extend(parser::parse(lexer::lex(src)?, &mut id)?.items);
        let info = types::check(&prog)?;
        let bodies = mir::lower(&prog, &info)?;
        let bodies = mono::monomorphize(bodies, &info)?;
        Ok(cgen::gen(&bodies, &info))
    };
    go().map_err(|d| diag::render(path, src, &d))
}

fn find_cc() -> Option<Vec<String>> {
    if let Ok(cc) = std::env::var("RUSH_CC") {
        return Some(cc.split_whitespace().map(str::to_string).collect());
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
            return Some(cand.iter().map(|s| s.to_string()).collect());
        }
    }
    None
}

fn build(args: &[String], run: bool) -> i32 {
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
    let c = match compile_to_c(path, &src) {
        Ok(c) => c,
        Err(msg) => {
            eprint!("{msg}");
            return 1;
        }
    };
    let src_path = Path::new(path);
    let stem = src_path.file_stem().unwrap().to_string_lossy().to_string();
    let parent = src_path.parent().filter(|p| !p.as_os_str().is_empty()).unwrap_or(Path::new("."));
    let build_dir = parent.join(".rush-build");
    let exe: PathBuf = parent.join(if cfg!(windows) { format!("{stem}.exe") } else { stem.clone() });
    let write = |name: &str, data: &str| std::fs::write(build_dir.join(name), data);
    if let Err(e) = std::fs::create_dir_all(&build_dir)
        .and_then(|_| write(&format!("{stem}.c"), &c))
        .and_then(|_| write("rush_rt.c", RT_C))
        .and_then(|_| write("rush_rt.h", RT_H))
    {
        eprintln!("error: cannot write build directory {}: {e}", build_dir.display());
        return 2;
    }
    let Some(cc) = find_cc() else {
        eprintln!("error: no C compiler found; install gcc, clang, or tcc, or set RUSH_CC");
        return 2;
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
    if !run {
        return 0;
    }
    let exe_abs = std::fs::canonicalize(&exe).unwrap_or(exe);
    match Command::new(&exe_abs).status() {
        Ok(s) => s.code().unwrap_or(1),
        Err(e) => {
            eprintln!("error: cannot run {}: {e}", exe_abs.display());
            2
        }
    }
}
