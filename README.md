# Rush

A compiled language: Go-style single binaries, Haskell-style types, Rust-style ownership, Ruby-style syntax.
Design: `docs/superpowers/specs/2026-09-17-rush-stage1-design.md`.

## Taste

```ruby
enum Shape
  Circle(Float)
  Rect(Float, Float)
end

trait Area
  def area(&self) -> Float
  def describe(&self) -> String
    "area #{self.area}"
  end
end

impl Area for Shape
  def area(&self)
    case self
    in Circle(r) then 3.14159 * r * r
    in Rect(w, h) then w * h
    end
  end
end

def unwrap_or[T](o: Option[T], default: T) -> T
  case o
  in Some(v) then v
  in None then default
  end
end

def main
  puts(&Rect(2.0, 3.0).describe)
  puts("#{unwrap_or(Some(3), 0)} #{Some("x")}")
end
```

Values are owned and moved; borrows are explicit for named variables and automatic for
method receivers and temporaries; heap data is freed by compiler-inserted drops; `Gc[T]`
opts a value into the collector.

```ruby
struct Person
  derive Show, Eq, Clone
  name: String
  age: Int
end

impl Person
  def birthday(&mut self)
    @age += 1
  end
end

def main
  let mut p = Person { name: "Ann", age: 30 }
  p.birthday
  let q = p.clone
  let r = p                 # p is moved; using it again is a compile error
  puts("#{q == r} #{q}")    # true Person { name: "Ann", age: 31 }
  let shared = Gc.new(q)
  puts("#{shared.borrow.age}")
end
```

Borrows are checked: a place has one live `&mut` or any number of live `&`, and a borrow
ends at its last use. A function returning a reference borrows from `self` or its one
reference parameter.

```ruby
impl Person
  def name_ref(&self) -> &String   # the result borrows self
    &@name
  end
  def set_age(&mut self, a: Int)
    @age = a
  end
end

def main
  let mut p = Person { name: "Ann", age: 30 }
  let n = p.name_ref
  puts(n)                   # Ann
  p.set_age(p.age + 1)      # fine: n is dead, and the receiver is borrowed after the argument
  let r = &mut p
  # puts(&p.name)           # error: cannot borrow `p.name` as shared because it is mutably borrowed
  r.set_age(40)
  puts("#{p}")              # Person { name: "Ann", age: 40 }
end
```

Functions are values and every one of them curries. A block is a closure: `{ |x| ... }` or
`do |x| ... end`, written after a call to become its last argument. A closure that captures
borrows what it uses and stays where it is (`&(A -> B)`); `move` gives it its own environment
on the collected heap, so it can be returned (`A -> B`). `x |> f(a)` supplies the last argument.

```ruby
def each_to(n: Int, f: &(Int -> Unit))
  for i in 1..n
    f(i)
  end
end

def adder(k: Int) -> Int -> Int
  move { |x| x + k }                    # owned: it can be returned
end

def add(a: Int, b: Int) -> Int
  a + b
end

def main
  let mut total = 0
  each_to(3) { |i| total += i }         # the block borrows total for the call
  let inc = add(1)                      # partial application: Int -> Int
  puts("#{total} #{inc(5)} #{5 |> adder(10)}")   # 6 6 15
  let found = loop
    total += 1
    if total > 8
      break total
    end
  end
  puts("#{found} #{:done} #{1..3}")     # 9 done 1..3
end
```

## Build

    export PATH="$HOME/.cargo/bin:$PATH"   # Git Bash on Windows
    cargo build --release

Needs a C compiler on PATH (`cc`, `gcc`, `clang`, `tcc`, or `zig cc`) or `RUSH_CC="path/to/cc"`.

## Install on Windows

Download `rush-v0.1.0-x86_64-pc-windows-msvc.zip` from the
[releases page](https://github.com/s81/rush-lang/releases), unzip it wherever you
like, and add that folder to `PATH`:

    rush --version
    rush run examples\hello.rush

The package contains `rush.exe`, this README, the changelog, and
`examples/hello.rush`. Building programs still needs a C compiler on `PATH`
(MinGW-w64 gcc, LLVM clang, tcc, or Zig) or `RUSH_CC` pointing at one. The
compiler embeds its prelude and C runtime, so there is nothing else to install.

## Release a Windows build

Push a tag that matches the version in `Cargo.toml`. The `Release` workflow runs
on `windows-latest`, builds the MSVC binary, smoke-tests the packaged compiler on
`examples/hello.rush`, uploads the zip and checksum, and publishes the GitHub
release:

    git tag v0.1.0
    git push origin v0.1.0

To build and package locally from PowerShell:

    ./scripts/package-windows.ps1

If PowerShell blocks local scripts, run
`powershell -ExecutionPolicy Bypass -File scripts/package-windows.ps1` instead.
Artifacts land in `dist/` as `rush-v<version>-<target>.zip` plus a `.sha256`.
Pass `-SkipSmokeTest` to skip compiling the example, or `-SkipBuild` to package
an existing `target/<target>/release/rush.exe`. The workflow can also be started
manually with an existing tag.

## Use

    rush build hello.rush     # writes hello(.exe) next to the source
    rush run hello.rush       # build and run
    rush build hello.rush --debug
    rush test hello.rush      # run every top-level `def test_*` in its own process

## Test

    cargo test

`cargo test` runs the module tests, the golden programs in `tests/programs`, the diagnostics in
`tests/errors`, the collector check in `runtime/gc_test.c`, and the `rush test` harness test.
Program cases run in a fresh temporary directory so builds never write beside the fixtures.
The C compiler comes from `RUSH_CC` (split like a small shell, so quoted paths work) or the
first of `cc`, `gcc`, `clang`, `tcc`, and `zig cc` on `PATH`.

## Status

The compiler implements Plans 1 through 4a, the `Result` half of Plan 4b, and `rush test` from
Plan 5. Plan 4b's higher-kinded `Functor`/`Applicative`/`Monad` traits, and Plan 5's full
standard library, imports, and sized integers remain. The design document lists the known Stage 1
limitations. CI runs the suite with gcc and clang on Linux/macOS and UCRT64 MinGW gcc on Windows.
