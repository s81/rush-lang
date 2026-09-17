# Rush

A compiled language: Go-style single binaries, Haskell-style types, Rust-style ownership, Ruby-style syntax.
Design: `docs/superpowers/specs/2026-09-17-rush-stage1-design.md`.

## Build

    export PATH="$HOME/.cargo/bin:$PATH"   # Git Bash on Windows
    cargo build --release

Needs a C compiler on PATH (`cc`, `gcc`, `clang`, `tcc`, or `zig cc`) or `RUSH_CC="path/to/cc"`.

## Use

    rush build hello.rush     # writes hello(.exe) next to the source
    rush run hello.rush       # build and run
    rush build hello.rush --debug

## Test

    cargo test
