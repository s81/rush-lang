use std::path::Path;
use std::process::{Command, Stdio};

fn find_cc() -> Option<Vec<String>> {
    if let Ok(cc) = std::env::var("RUSH_CC") {
        return Some(cc.split_whitespace().map(str::to_string).collect());
    }
    let candidates: [&[&str]; 5] = [&["cc"], &["gcc"], &["clang"], &["tcc"], &["zig", "cc"]];
    for cand in candidates {
        let ok = Command::new(cand[0]).args(&cand[1..]).arg("-v").stdout(Stdio::null()).stderr(Stdio::null()).status().map(|s| s.success()).unwrap_or(false);
        if ok {
            return Some(cand.iter().map(|s| s.to_string()).collect());
        }
    }
    None
}

#[test]
fn collector_frees_garbage_and_keeps_roots() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let out_dir = root.join("target").join("gc_test");
    std::fs::create_dir_all(&out_dir).unwrap();
    let exe = out_dir.join(if cfg!(windows) { "gc_test.exe" } else { "gc_test" });
    let cc = find_cc().expect("a C compiler");
    let mut cmd = Command::new(&cc[0]);
    cmd.args(&cc[1..]);
    cmd.args(["-std=c99", "-O2", "-I"]).arg(root.join("runtime")).arg("-o").arg(&exe).arg(root.join("runtime/gc_test.c")).arg(root.join("runtime/rush_rt.c"));
    let status = cmd.status().expect("run cc");
    assert!(status.success(), "C compile failed");
    let out = Command::new(&exe).output().expect("run gc_test");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(out.status.success(), "gc_test failed:\n{stdout}");
    assert!(stdout.contains("gc ok"), "{stdout}");
}
