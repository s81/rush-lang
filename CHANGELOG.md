# Changelog

All notable changes to Rush are recorded here. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and versions follow
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.1.0] - 2026-11-07

The first Windows x86_64 release of the `rush` compiler.

### Added

- A single-binary compiler driver with `rush build`, `rush run`, and `rush test`.
- `--version`/`-V` and `--help`/`-h` output, including a `RUSH_CC` hint.
- A Windows x86_64 release package containing `rush.exe`, the README, this
  changelog, and `examples/hello.rush`, plus a SHA256 checksum.
- A tag-driven GitHub Actions workflow that builds and publishes the Windows
  release artifact.

### Language and compiler

- Lexing, parsing, type checking with inference and generics, monomorphization,
  ownership and borrow checking, and C code generation.
- Structs, enums, traits, impls, `derive`, pattern matching, and closures with
  capture inference.
- Owned and borrowed values, move checking, compiler-inserted drops, and an
  optional tracing collector for `Gc[T]`.
- The `Result` and `Option` types, `try`, higher-kinded type constructors, and
  the `?` operator's supporting machinery in the prelude.
- `RUSH_CC` lets users select `cc`, `gcc`, `clang`, `tcc`, or `zig cc`; the
  compiler embeds its prelude and C runtime, so no separate runtime install is
  needed.

### Known limitations

- Higher-kinded `Functor`/`Applicative`/`Monad`, the full standard library, and
  imports are not implemented yet.
- A C compiler is required to turn generated C into an executable.
- macOS and Linux binaries are not part of this release; build them from source.

[0.1.0]: https://github.com/s81/rush-lang/releases/tag/v0.1.0
