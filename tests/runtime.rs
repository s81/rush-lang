mod util;

use std::path::Path;
use std::process::Command;

use util::TempDir;

#[test]
fn collector_frees_garbage_and_keeps_roots() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let tmp = TempDir::new("gc");
    let exe = tmp.path().join(if cfg!(windows) { "gc_test.exe" } else { "gc_test" });
    let cc = util::find_cc().expect("a C compiler");
    let mut cmd = Command::new(&cc[0]);
    cmd.args(&cc[1..]);
    cmd.args(["-std=c99", "-O2", "-I"])
        .arg(root.join("runtime"))
        .arg("-o")
        .arg(&exe)
        .arg(root.join("runtime/gc_test.c"))
        .arg(root.join("runtime/rush_rt.c"));
    if !cfg!(windows) {
        cmd.arg("-lm");
    }
    let status = cmd.status().expect("run cc");
    assert!(status.success(), "C compile failed");
    let out = Command::new(&exe).output().expect("run gc_test");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(out.status.success(), "gc_test failed:\n{stdout}");
    assert!(stdout.contains("gc ok"), "{stdout}");
}
