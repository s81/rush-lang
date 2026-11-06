//! Shared helpers for the integration tests. This module is included by each test binary.

#![allow(dead_code)]

use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_DIR: AtomicU64 = AtomicU64::new(0);

/// A uniquely named directory under the system temp directory, removed on drop.
pub struct TempDir {
    path: PathBuf,
}

impl TempDir {
    pub fn new(tag: &str) -> TempDir {
        let n = NEXT_DIR.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!("rush-test-{}-{}-{}", std::process::id(), n, tag));
        let _ = std::fs::remove_dir_all(&path);
        std::fs::create_dir_all(&path).expect("create temp directory");
        TempDir { path }
    }

    pub fn path(&self) -> &Path {
        &self.path
    }

    /// Copies `src` into this directory and returns the copy's path.
    pub fn copy_in(&self, src: &Path) -> PathBuf {
        let dst = self.path.join(src.file_name().expect("source file name"));
        std::fs::copy(src, &dst).expect("copy test fixture");
        dst
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.path);
    }
}

/// Splits a compiler command like a small shell. Mirrors `driver::split_command`; the integration
/// tests cannot link against the binary crate, so the rules are duplicated here.
pub fn split_command(s: &str) -> Result<Vec<String>, String> {
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

/// Finds the C compiler used by the runtime tests: `RUSH_CC` when set, then the usual names.
pub fn find_cc() -> Option<Vec<String>> {
    if let Ok(cc) = std::env::var("RUSH_CC") {
        return Some(split_command(&cc).expect("RUSH_CC is a valid command"));
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
