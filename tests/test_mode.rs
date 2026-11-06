mod util;

use std::path::Path;
use std::process::Command;

fn rush(args: &[&str], cwd: &Path) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_rush"))
        .args(args)
        .current_dir(cwd)
        .output()
        .expect("failed to spawn rush")
}

#[test]
fn runs_each_test_in_its_own_process() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let tmp = util::TempDir::new("test-mode");
    let file = tmp.copy_in(&root.join("tests/fixtures/test_mode/sample.rush"));
    let name = file.file_name().unwrap().to_str().unwrap();
    let out = rush(&["test", name], tmp.path());
    let stdout = String::from_utf8_lossy(&out.stdout).replace("\r\n", "\n");
    let stderr = String::from_utf8_lossy(&out.stderr).replace("\r\n", "\n");
    assert_eq!(out.status.code(), Some(1), "stdout:\n{stdout}\nstderr:\n{stderr}");
    assert!(stdout.contains("running 2 tests"), "{stdout}");
    assert!(stdout.contains("test test_pass ... ok"), "{stdout}");
    assert!(stdout.contains("test test_fail ... FAILED"), "{stdout}");
    assert!(stdout.contains("1 passed, 1 failed"), "{stdout}");
    // `main` is not a test and must not run.
    assert!(!stdout.contains("main should not run"), "{stdout}");
    // A panic in one test is reported with that test and does not stop the others.
    assert!(stdout.contains("panic: division by zero"), "{stdout}");
}

#[test]
fn test_files_may_omit_main() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let tmp = util::TempDir::new("no-main");
    let file = tmp.copy_in(&root.join("tests/fixtures/test_mode/no_main.rush"));
    let name = file.file_name().unwrap().to_str().unwrap();
    let out = rush(&["test", name], tmp.path());
    let stdout = String::from_utf8_lossy(&out.stdout).replace("\r\n", "\n");
    let stderr = String::from_utf8_lossy(&out.stderr).replace("\r\n", "\n");
    assert_eq!(out.status.code(), Some(0), "stdout:\n{stdout}\nstderr:\n{stderr}");
    assert!(stdout.contains("running 1 test"), "{stdout}");
    assert!(stdout.contains("test test_only ... ok"), "{stdout}");
    assert!(stdout.contains("1 passed, 0 failed"), "{stdout}");
}

#[test]
fn no_tests_returns_before_looking_for_a_compiler() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let tmp = util::TempDir::new("no-tests");
    let file = tmp.copy_in(&root.join("tests/fixtures/test_mode/no_tests.rush"));
    let name = file.file_name().unwrap().to_str().unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_rush"))
        .args(["test", name])
        .current_dir(tmp.path())
        .env("RUSH_CC", "this-compiler-does-not-exist")
        .output()
        .expect("failed to spawn rush");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert_eq!(out.status.code(), Some(0), "stdout:\n{stdout}\nstderr:\n{stderr}");
    assert!(stdout.contains("no tests found"), "{stdout}");
    assert!(!stderr.contains("compiler"), "{stderr}");
}

#[test]
fn invalid_rush_cc_is_rejected() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let tmp = util::TempDir::new("rush-cc");
    let file = tmp.copy_in(&root.join("tests/fixtures/test_mode/no_tests.rush"));
    let name = file.file_name().unwrap().to_str().unwrap();
    let cases = [
        ("", "RUSH_CC is empty"),
        ("   ", "RUSH_CC is empty"),
        ("\"\"", "RUSH_CC has an empty command"),
        ("cc \"unterminated", "RUSH_CC has an unterminated \" quote"),
        ("cc 'unterminated", "RUSH_CC has an unterminated ' quote"),
        ("cc\\", "RUSH_CC ends with a backslash"),
    ];
    for (value, expected) in cases {
        let out = Command::new(env!("CARGO_BIN_EXE_rush"))
            .args(["build", name])
            .current_dir(tmp.path())
            .env("RUSH_CC", value)
            .output()
            .expect("failed to spawn rush");
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert_eq!(out.status.code(), Some(2), "RUSH_CC={value:?}, stderr:\n{stderr}");
        assert!(stderr.contains(expected), "RUSH_CC={value:?}, stderr:\n{stderr}");
    }
}
