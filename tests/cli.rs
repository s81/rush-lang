//! Command-line surface: version, help, and argument errors.

use std::process::{Command, Output};

fn rush(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_rush")).args(args).output().expect("run the rush binary")
}

fn stdout(out: &Output) -> String {
    String::from_utf8_lossy(&out.stdout).replace("\r\n", "\n")
}

fn stderr(out: &Output) -> String {
    String::from_utf8_lossy(&out.stderr).replace("\r\n", "\n")
}

#[test]
fn version_flags_print_the_package_version() {
    let expected = format!("rush {}\n", env!("CARGO_PKG_VERSION"));
    for flag in ["--version", "-V"] {
        let out = rush(&[flag]);
        assert!(out.status.success(), "{flag} failed: {}", stderr(&out));
        assert_eq!(stdout(&out), expected, "{flag}");
        assert_eq!(stderr(&out), "", "{flag} wrote to stderr");
    }
}

#[test]
fn version_works_after_a_subcommand() {
    let expected = format!("rush {}\n", env!("CARGO_PKG_VERSION"));
    for args in [["build", "--version"], ["run", "-V"], ["test", "--version"]] {
        let out = rush(&args);
        assert!(out.status.success(), "{args:?} failed: {}", stderr(&out));
        assert_eq!(stdout(&out), expected, "{args:?}");
    }
}

#[test]
fn help_flags_list_the_commands() {
    for flag in ["--help", "-h"] {
        let out = rush(&[flag]);
        assert!(out.status.success(), "{flag} failed: {}", stderr(&out));
        let text = stdout(&out);
        for needle in ["rush build", "rush run", "rush test", "--version", "RUSH_CC"] {
            assert!(text.contains(needle), "{flag} output is missing `{needle}`:\n{text}");
        }
    }
}

#[test]
fn help_after_a_subcommand_does_not_need_an_input_file() {
    let out = rush(&["run", "--help"]);
    assert!(out.status.success(), "{}", stderr(&out));
    assert!(stdout(&out).contains("rush run <file.rush>"));
}

#[test]
fn no_arguments_prints_usage_and_fails() {
    let out = rush(&[]);
    assert_eq!(out.status.code(), Some(2));
    assert_eq!(stdout(&out), "");
    assert!(stderr(&out).contains("usage:"));
}

#[test]
fn an_unknown_command_is_reported() {
    let out = rush(&["frobnicate"]);
    assert_eq!(out.status.code(), Some(2));
    assert!(stderr(&out).contains("unknown command `frobnicate`"));
    assert!(stderr(&out).contains("usage:"));
}
