use std::path::{Path, PathBuf};
use std::process::Command;

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

#[test]
fn programs_produce_expected_output() {
    for (path, expected) in cases("programs", "out") {
        let dir = path.parent().unwrap();
        let file = path.file_name().unwrap().to_str().unwrap();
        let out = rush(&["run", file], dir);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(out.status.success(), "{file}: rush run failed\n{stderr}");
        let stdout = String::from_utf8_lossy(&out.stdout).replace("\r\n", "\n");
        assert_eq!(stdout, expected, "{file}: stdout mismatch");
    }
}

#[test]
fn error_programs_report_expected_diagnostic() {
    for (path, expected) in cases("errors", "err") {
        let dir = path.parent().unwrap();
        let file = path.file_name().unwrap().to_str().unwrap();
        let out = rush(&["build", file], dir);
        assert_eq!(out.status.code(), Some(1), "{file}: expected exit code 1");
        let stderr = String::from_utf8_lossy(&out.stderr).replace("\r\n", "\n");
        assert!(
            stderr.contains(expected.trim_end()),
            "{file}: stderr was:\n{stderr}\nexpected to contain:\n{expected}"
        );
    }
}
