mod util;

use std::path::{Path, PathBuf};
use std::process::Command;

use util::TempDir;

fn rush(args: &[&str], cwd: &Path) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_rush"))
        .args(args)
        .current_dir(cwd)
        .output()
        .expect("failed to spawn rush")
}

fn cases(dir: &str, ext: &str) -> Vec<(PathBuf, String)> {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests").join(dir);
    let mut out = Vec::new();
    for entry in std::fs::read_dir(&dir).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().map_or(true, |e| e != "rush") {
            continue;
        }
        let expected = std::fs::read_to_string(path.with_extension(ext)).unwrap().replace("\r\n", "\n");
        out.push((path, expected));
    }
    assert!(!out.is_empty(), "no test cases in {}", dir.display());
    out.sort();
    out
}

fn normalize_line(line: &str) -> String {
    let line = line.trim_end();
    // Rendered diagnostics are `path:line:col: error: msg`; the golden files may omit the
    // prefix, so strip it from either side before comparing.
    for kind in [": error: ", ": note: "] {
        if let Some(i) = line.find(kind) {
            return line[i + 2..].to_string();
        }
    }
    line.to_string()
}

/// Keeps only the compiler's diagnostic messages, dropping the echoed source and caret lines
/// that `diag::render` adds. The result is compared exactly with the `.err` fixture.
fn diagnostic_lines(stderr: &str) -> Vec<String> {
    stderr
        .replace("\r\n", "\n")
        .lines()
        .filter(|line| line.contains(": error: ") || line.contains(": note: ") || line.starts_with("error: ") || line.starts_with("note: "))
        .map(normalize_line)
        .collect()
}

fn expected_diagnostics(expected: &str) -> Vec<String> {
    expected.lines().filter(|line| !line.trim().is_empty()).map(normalize_line).collect()
}

fn panic_lines(stderr: &str) -> Vec<String> {
    stderr
        .replace("\r\n", "\n")
        .lines()
        .filter(|line| line.starts_with("panic: "))
        .map(|line| line.trim_end().to_string())
        .collect()
}

#[test]
fn programs_produce_expected_output() {
    for (path, expected) in cases("programs", "out") {
        let file = path.file_name().unwrap().to_str().unwrap();
        let tmp = TempDir::new("program");
        tmp.copy_in(&path);
        let out = rush(&["run", file], tmp.path());
        let stderr = String::from_utf8_lossy(&out.stderr).replace("\r\n", "\n");
        // A sibling .err file means the program panics: non-zero exit and a `panic:` line.
        match std::fs::read_to_string(path.with_extension("err")) {
            Ok(err) => {
                assert!(!out.status.success(), "{file}: expected a panic\n{stderr}");
                let got = panic_lines(&stderr);
                let expected: Vec<String> = err
                    .replace("\r\n", "\n")
                    .lines()
                    .map(|line| line.trim_end().to_string())
                    .filter(|line| line.starts_with("panic: "))
                    .collect();
                assert!(!got.is_empty(), "{file}: expected a `panic:` line, stderr was:\n{stderr}");
                assert_eq!(got, expected, "{file}: panic message mismatch\nstderr was:\n{stderr}");
            }
            Err(_) => assert!(out.status.success(), "{file}: rush run failed\n{stderr}"),
        }
        let stdout = String::from_utf8_lossy(&out.stdout).replace("\r\n", "\n");
        assert_eq!(stdout, expected, "{file}: stdout mismatch");
    }
}

#[test]
fn error_programs_report_expected_diagnostic() {
    for (path, expected) in cases("errors", "err") {
        let file = path.file_name().unwrap().to_str().unwrap();
        let tmp = TempDir::new("error");
        tmp.copy_in(&path);
        let out = rush(&["build", file], tmp.path());
        assert_eq!(out.status.code(), Some(1), "{file}: expected exit code 1");
        let stderr = String::from_utf8_lossy(&out.stderr).replace("\r\n", "\n");
        assert_eq!(
            diagnostic_lines(&stderr),
            expected_diagnostics(&expected),
            "{file}: diagnostic mismatch\nstderr was:\n{stderr}"
        );
    }
}
