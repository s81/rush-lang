# Rush, Stage 1 design

Date: 2026-09-17
Status: approved section by section by the project owner in the brainstorming session; awaiting written review.

## Goal

Rush is a compiled language with:

- a single native binary per program, produced by emitting portable C99 and calling a system C compiler, like Go's user experience;
- a Hindley-Milner static type system with typeclass-style traits and higher-kinded types, like Haskell;
- ownership and borrowing checked at compile time, with a small garbage collector only for explicitly shared data, like Rust;
- Ruby-flavoured syntax: `def`/`end`, blocks, `case`/`in`, `?`/`!` method names, symbols, string interpolation;
- portability to Windows x86-64, Linux x86-64, Linux ARM64, and macOS x86-64/ARM64.

Stage 1 delivers the Rust-hosted compiler that compiles and runs real single-threaded programs. Stage 2 adds green threads and channels. Stage 3 rewrites the compiler in Rush. Each stage gets its own spec.

## Decisions taken with the owner

| Topic | Decision |
|---|---|
| Rust-style safety | No null, immutable by default, plus a real ownership and borrow checker |
| Host language and backend | Compiler in Rust, emits C99, links with the system C compiler |
| Type system | HM inference, ADTs, traits, higher-kinded types |
| Syntax | `def`/`end`, `do`/`end` and `{ \|x\| }` blocks, everything is an expression, Ruby naming |
| Milestone | Real programs in Stage 1, self-hosting in Stage 3 |
| Concurrency | Go-style green threads and channels, deferred to Stage 2 |
| GC | Conservative mark-sweep, stop-the-world |
| Targets | Windows, Linux, macOS, ARM64 |
| Heap split | Owned by default, explicit `Gc[T]` for shared or cyclic data |
| Data model | `struct`, `enum`, `trait`, no inheritance, functional style |
| Errors | `Result`/`Option` with `?`, panic for bugs, no exceptions |
| Primitives | Fixed-size integers, `f64`, immutable UTF-8 `String` |
| FP features | First-class closures, `\|>`, auto-currying, Functor/Applicative/Monad in stdlib |
| Name | Rush, `.rush` files, `rush` CLI |
| Architecture | Typed AST plus a small MIR, borrow checking with non-lexical lifetimes |
| Gc syntax | `Gc.new(v)`; `Type.function(args)` calls associated functions in general |
| Copies | Explicit `.clone` through `Clone`; use after move is an error |
| Call borrows | Named variables need `&x`; temporaries and method receivers auto-borrow |
| String operators | `+`, `==`, `!=` borrow both operands; `Eq::eq` takes `&Self` |
| Match ergonomics | `case` on `&T` matches the pointee and binds by reference; `&T` with `T: Copy` reads as `T` |
| Drops | At the end of the enclosing lexical scope in reverse declaration order, on `return`, and on reassignment; expression-statement temporaries at the end of the statement, `let` initializer temporaries at the end of the scope (2026-09-18) |
| References in fields | A type holding references has one implicit lifetime shared by all its reference fields; it cannot go into `Gc` and counts as a reference for elision (2026-09-18) |
| Gc borrow release | `Gc.borrow`/`borrow_mut` are released at the last use of the returned reference, as computed by the borrow checker (2026-09-18) |
| Two-phase receivers | An auto-borrowed `&mut self` receiver is borrowed after the arguments are evaluated, so `p.set_age(p.age + 1)` compiles (2026-09-18) |
| `&mut` moves | `&mut T` is not `Copy`; `let r2 = r` moves `r`, while passing a `&mut` local as an argument or receiver reborrows it (2026-09-18) |
| Loan precision | Loans are per place with field precision: `&mut p.a` and `&p.b` do not conflict; enum variant fields count as fields (2026-09-18) |
| Diagnostic notes | Borrow errors point at the conflicting access with a note "`x` is borrowed here"; use after move notes "value moved here"; "does not live long enough" points at the dying variable (2026-09-18) |
| Generic call loans | A call result holding references takes the elided argument's loans; if only the instantiated return type holds references (`id[T](x: T) -> T` with `&s`), it takes the loans of every argument holding references (2026-09-18) |
| Literals | String literals are owned `String`s with static storage |
| Derived Show | Uses `Show.inspect`, which quotes strings; `to_s` does not |
| Closure types | `A -> B` is owned: named functions, `move` closures, and closures with no captures. It is `Copy`, its environment is on the GC heap, and it can be stored and returned. A non-`move` closure with captures is `&(A -> B)`: its environment is on the stack and it holds loans on its captures, so it cannot escape (2026-09-18) |
| Capture modes | Without `move`, a capture is `&mut` when the body assigns to it, borrows it `&mut`, or calls a `&mut self` method on it, a reborrow when the variable is `&mut T`, and `&` otherwise. `move` copies `Copy` captures and moves the rest, and its body may not assign to or mutably borrow one; shared mutable state goes in a `Gc` (2026-09-18) |
| Call-once closures | None. A closure body cannot move a capture out, so every closure can be called any number of times (2026-09-18) |
| Function values | Defs, associated functions, methods named through their type (`Shape.area`), and variant constructors are values and curry. Supplying every argument is one indirect call; fewer builds a partial application on the GC heap, and only `Copy` arguments may be bound, since a partial application can be called again (2026-09-18) |
| `\|>` | `x \|> f(a)` is `f(a, x)` and `x \|> f` is `f(x)`, rewritten in the parser, so `a` is evaluated before `x` (2026-09-18) |
| Blocks | `{ \|x\| e }`, `do \|x\| ... end`, either with `move`. A block after a call's `)`, after a bare call name, or after a method call is that call's last argument. Standalone, `{` starts a block only before `\|`, which leaves `{ "k" => v }` free for Plan 5 maps (2026-09-18) |
| Ranges and `for` | `a..b` includes `b` and `a...b` excludes it; a range is `Range[T] { start, stop, exclusive }` and shows as `1..5`. `for` iterates a `Range[Int]` until iterators arrive in Plan 5 (2026-09-18) |
| `loop` and `break` | `loop` yields the value of its `break e`, and `Unit` without one; `break` in `while` and `for` takes no value. Both `break` and `next` drop the locals of the scopes they leave, in reverse order (2026-09-18) |
| Symbols | `:name` is a `Copy` `Symbol`, compared with `==` and usable as a `case` pattern (which then needs `_` or `else`). `to_s` is `name`, `inspect` and derived `Show` are `:name` (2026-09-18) |
| `return` in a block | Returns from the block, as in Rust; `break` and `next` refer to loops inside the block, and outside one are an error (2026-09-18) |

## 1. Language surface

```ruby
# shapes.rush
struct Point
  x: Float
  y: Float
end

enum Shape
  Circle(Float)
  Rect(Float, Float)
end

trait Area
  def area(&self) -> Float
end

impl Area for Shape
  def area(&self)
    case self
    in Circle(r) then 3.14159 * r * r
    in Rect(w, h) then w * h
    end
  end
end

def total(shapes: &List[Shape]) -> Float
  shapes.map { |s| s.area } |> sum
end

def main
  let shapes = [Circle(1.0), Rect(2.0, 3.0)]
  let mut n = 0
  shapes.each do |s|
    n += 1
    puts "#{s.area}"
  end
  puts "total: #{total(&shapes)} over #{n}"
end
```

### Lexical rules

- A newline ends a statement unless the line ends in an operator, a comma, an opening bracket, or a backslash. Semicolons are not used.
- Comments start with `#` and run to end of line.
- Identifiers: `snake_case` for values and functions, `CamelCase` for types, traits, and enum variants. Method names may end in `?` or `!`.
- Literals: `42`, `1_000`, `0xFF`, `3.14`, `'c'`, `"str #{expr}"`, `:symbol`, `true`, `false`, `[1, 2]`, `{ "k" => v }` for maps, `(a, b)` for tuples, `1..5` and `1...5` for ranges.
- Keywords: `def end let mut if elsif else while for in loop break next return case then struct enum trait impl import move mdo self true false and or not type extern`.

### Declarations

- `def name(p1: T1, p2: T2) -> R` ... `end`. Parameter and return types are optional; see section 3.
- `let x = e` binds immutably. `let mut x = e` binds mutably. `let (a, b) = e` destructures.
- `struct Name` with `field: Type` lines. `struct Name[T]` for generic structs.
- `enum Name` with `Variant`, `Variant(T1, T2)`, or `Variant { f: T }` lines.
- `trait Name` with `def` signatures and optional default bodies. `trait Name: Super` for supertraits. `type Item` for associated types.
- `impl Trait for Type` and `impl Type` for inherent methods. `impl[T: Bound] Trait for Type[T]` for generic instances.
- A `derive Show, Eq, Copy` line inside a `struct` or `enum` body generates those instances (decided 2026-09-17; implemented from Plan 3 on).
- `import name` loads `name.rush` from the same directory. Everything top-level in a file is exported. One file is one module.
- `extern "C" def name(p: T) -> R` declares a runtime primitive.

### Expressions and control flow

- Everything is an expression. The last expression in a body is its value. `return e` exits early.
- `if c` / `elsif c` / `else` / `end`. `while c` / `end`. `for x in iter` / `end`. `loop` / `end`. `break` and `next` inside loops; `break e` yields a value from `loop`.
- `case e` / `in Pattern then body` / `in Pattern if guard then body` / `else body` / `end`. Multi-line arm bodies omit `then` and run until the next `in`. Patterns: literals, `_`, bindings, `Variant(p, ...)`, `Struct { f: p }`, tuples `(p, q)`, lists `[p, q, *rest]`, `p | q` alternation, `x @ p` binding a whole. Matches must be exhaustive.
- Blocks: `{ |x, y| expr }` and `do |x, y| ... end` are closure literals. A block after a call's closing parenthesis, or after a bare call, is passed as the last argument. `move do |x| ... end` and `move { |x| ... }` capture by move.
- Calls: `f(a, b)`. Parentheses are required when there are arguments. A zero-argument function is called by its bare name. The bare name of a function with arguments denotes the function value. Ruby command-call syntax like `puts "hi"` is not supported in Stage 1.
- Method call `recv.name(args)` looks up inherent methods, then trait methods in scope. `@x` inside a method is `self.x`.
- Operators, tightest first: postfix `?` and `.`; unary `-`, `not`, `&`, `&mut`, `*`; `* / %`; `+ -`; `<< >>`; `& | ^` on integers; `.. ...`; `== != < <= > >=`; `and`; `or`; `|>`; `>>=`; assignment `= += -= *= /=`.
- `a |> f(b)` means `f(b, a)`: the left value becomes the last argument. `a |> f` means `f(a)`.
- `e?` on `Option[T]` or `Result[T, E]` unwraps or returns early from the enclosing function, which must return the same kind of type.
- String interpolation `"#{e}"` calls `to_s` from the `Show` trait.
- Integer overflow panics in debug builds and wraps in release builds. Division by zero panics.

## 2. Ownership, borrowing, and the GC

- Every value has exactly one owner. Assignment, argument passing, and return move the value unless its type is `Copy`.
- `Copy` types: all integer types, `Float`, `Bool`, `Char`, `Symbol`, `Unit`, `&T`, `Gc[T]`, function values with no captured non-`Copy` environment, and tuples of `Copy` types. User structs and enums may derive `Copy` when all fields are `Copy`.
- `&x` creates a shared borrow, `&mut x` a mutable borrow, and `*r` dereferences. At any program point a place has either one live `&mut` or any number of live `&`. A place cannot be moved or assigned while borrowed. Liveness is computed on the MIR control-flow graph, so a borrow ends at its last use, not at scope end.
- Method receivers auto-borrow: for `def m(&self)` the call `x.m` borrows `&x`; for `&mut self` it borrows `&mut x`; for `self` it moves `x`.
- Stage 1 has no lifetime syntax. Functions returning a reference follow Rust's elision rules: one reference parameter, or a `&self`/`&mut self` receiver, determines the output lifetime. If elision cannot decide, the compiler reports an error that suggests returning an owned value.
- Owned heap data (`String`, `List`, `Map`, `StringBuilder`, and any struct or enum containing them) is freed by drop calls the compiler inserts at scope exit on every control-flow path. User types may implement `Drop` with `def drop(&mut self)`.
- `Gc[T]` is the only route to shared, cyclic, or long-lived-without-owner data. `Gc.new(v)` moves `v` onto the collected heap and returns a `Copy` handle. `g.borrow` returns `&T` and `g.borrow_mut` returns `&mut T`. Both are checked at runtime with a borrow count in the object header; a violation panics. The returned reference is borrow-checked at compile time like any other reference.
- Closures capture free variables by shared or mutable reference, whichever the body needs, or by value with `move`. A closure literal has type `A -> B` when it is `move` or captures nothing, and `&(A -> B)` otherwise. An owned `A -> B` is `Copy`, keeps its environment on the GC heap, and can be stored and returned. A `&(A -> B)` keeps its environment on the stack and holds loans on its captures, so returning it, storing it in a struct or `Gc`, or passing it where the parameter type is owned is a compile error that suggests `move`.
- The GC is a conservative, non-moving, stop-the-world mark-sweep collector in C. It scans the C stack between a recorded base and the current stack pointer, a registered set of global roots, and the bodies of reachable GC objects word by word. Only `Gc[T]` cells and escaping closure environments live on the GC heap, so it stays small. Stage 2 registers each green-thread stack as an additional root range.

## 3. Type system

- Hindley-Milner inference with let-polymorphism. `def` parameter and return types are optional. A `def` without annotations is inferred; mutually recursive functions are inferred as one group. Polymorphic recursion is rejected because every generic function is monomorphized.
- Built-in types: `Int` (alias `i64`), `i8 i16 i32 i64 u8 u16 u32 u64`, `Float` (alias `f64`), `f32`, `Bool`, `Char`, `String`, `Symbol`, `Unit`, tuples, `List[T]`, `Map[K, V]`, `Option[T]`, `Result[T, E]`, `Gc[T]`, `Range[T]`, `&T`, `&mut T`, and function types `A -> B`.
- Numeric literals default to `Int` or `Float` unless context requires another numeric type.
- Traits are typeclasses. A trait may declare methods, default method bodies, supertraits, and associated types. Instances are `impl Trait for Type` or `impl[T: Bound] Trait for Type[T]`. Two instances that could both match a type are rejected as overlapping. There is no orphan rule because Stage 1 compiles one unit.
- Trait parameters may be higher-kinded: `trait Functor[F[_]]` declares `F` of kind `* -> *`. Kinds are inferred from how a parameter is applied; a mismatch is an error.
- Bounds appear in square brackets: `def show_all[T: Show](xs: &List[T]) -> String`. Bounds are also inferred for unannotated functions.
- All trait dispatch is static. Every generic function and instance is monomorphized per concrete instantiation. There are no trait objects in Stage 1.
- Every function is curried. `f(a, b)` means `f(a)(b)`. A full application of a `def` with all arguments compiles to one C call. A partial application allocates a closure holding the supplied arguments; if any supplied argument is a borrow, the closure carries that borrow and is checked as a borrow.
- Monad notation: `?` covers `Option` and `Result`. `a >>= f` is `bind(a, f)`. `mdo ... end` desugars `x <- e` lines into nested `bind` calls and a final `pure`.

## 4. Compiler pipeline and runtime

A single Cargo crate producing the binary `rush`. Modules, in dependency order:

| Module | Responsibility |
|---|---|
| `lexer.rs` | Tokens with spans, newline significance, string interpolation splitting |
| `ast.rs`, `parser.rs` | Recursive-descent parser producing the AST |
| `resolve.rs` | Scopes, imports, name binding, method and trait visibility |
| `types.rs` | Unification, generalization, kind inference, trait instance resolution, exhaustiveness |
| `mir.rs` | Lowering to a control-flow graph; desugars `?`, `case`, `\|>`, `mdo`, blocks, currying, interpolation |
| `borrowck.rs` | Liveness, borrow conflicts, move checking, drop insertion |
| `mono.rs` | Monomorphization of generic functions and instances |
| `cgen.rs` | Emits one C99 translation unit |
| `driver.rs` | CLI: `rush build`, `rush run`, `rush test`; finds a C compiler via `RUSH_CC`, then `cc`, `gcc`, `clang`, `tcc`, `zig cc` |

The runtime is `runtime/rush_rt.c` and `runtime/rush_rt.h`, embedded into the compiler binary with `include_str!` and written beside the generated C at build time. It contains the GC, panic, allocation, string and list primitives, and IO primitives.

C mapping:

- structs to C structs; enums to a tag plus a union; `Option[T]` and `Result[T, E]` are ordinary enums;
- `List[T]` to a data pointer, length, and capacity with malloc-managed storage; `String` to a pointer and length, immutable UTF-8; `Map[K, V]` to an open-addressing hash table;
- closures to a function pointer plus an environment pointer; monomorphized functions get mangled names of the form `rush_<module>_<name>_<instantiation-hash>`;
- `Gc[T]` to a pointer to a GC header followed by `T`;
- panics print the message and location to stderr and call `abort`.

Build flow: `rush build main.rush` writes `main.c` and `rush_rt.c` into a `.rush-build/` directory, invokes the C compiler with `-O2` (or `-O0 -g` with `--debug`), and places the binary beside the source. `rush run` builds then executes.

## 5. Standard library, Stage 1

Implemented in an embedded `std/prelude.rush` where possible, with `extern "C"` primitives in the runtime.

- Core traits: `Eq`, `Ord`, `Show` (`to_s`), `Hash`, `Clone`, `Copy`, `Drop`, `Default`, `Iterator` (with `next`).
- HKT traits: `Functor` (`fmap`), `Applicative` (`pure`, `ap`), `Monad` (`bind`), with instances for `Option`, `Result[_, E]`, and `List`.
- Types: `Option`, `Result`, `List`, `Map`, `String`, `StringBuilder`, `Range`, `Gc`.
- Methods: `each`, `map`, `filter`, `fold`, `sum`, `len`, `push`, `pop`, `get`, `contains?`, `sort`, `join`, `split`, `chars`, `to_i`, `to_f`, `unwrap`, `unwrap_or`, `and_then`, `is_some?`, `is_ok?`.
- IO and process: `puts`, `print`, `read_line`, `File.read`, `File.write`, `args`, `exit`, `now_ms`.
- Excluded from Stage 1: networking, threads, channels, formatting beyond interpolation and `to_s`, regular expressions.

## 6. Testing

- Unit tests in each Rust module use small inline programs and assert on tokens, AST shape, inferred types, or diagnostic text.
- `tests/programs/*.rush` each have a `.out` file. A Rust integration test compiles every program through the full pipeline and the C compiler, runs it, and diffs stdout against `.out`.
- `tests/errors/*.rush` each have a `.err` file holding the expected diagnostic. They cover type mismatches, missing instances, non-exhaustive matches, use after move, conflicting borrows, and escaping non-`move` closures.
- `rush test file.rush` compiles the file and runs every `def test_*` function, reporting pass or fail per test. Stage 3's self-hosting suite uses this.
- Development is test-first: each pipeline stage gets a failing test before its implementation.

## 7. Diagnostics

Every error reports file, line, column, and a one-line message, with the offending span underlined. Borrow errors name both conflicting sites. Type errors show expected and found types. The only suggestion in Stage 1 is the elision hint from section 2.

## 8. Roadmap and finish line

| Stage | Deliverable | Spec |
|---|---|---|
| 1 | Rust-hosted `rush` compiler; compiles and runs real single-threaded programs on all targets | This document |
| 2 | Green threads and channels, `Send` rule, per-thread GC root ranges, cross-directory `import`, formatting | Written after Stage 1 ships |
| 3 | Compiler rewritten in Rush and bootstrapped with the Stage 1 binary | Written after Stage 2 ships |

Stage 1 is done when the section 6 suite passes on Windows with `tcc`, and the generated C for every program in `tests/programs` compiles and runs with `gcc` or `clang` on Linux and macOS.

## Plan sequence inside Stage 1 (decided 2026-09-17)

| Plan | Delivers |
|---|---|
| 1 | Pipeline end to end, primitives, functions, control flow, CLI, golden tests (shipped) |
| 2 | `struct`, `enum`, `case`/`in` with exhaustiveness, tuples, generics with monomorphization, traits with default methods and supertraits, `Show` interpolation, `Eq` (shipped) |
| 3a | Ownership: moves, `Copy`/`Clone`/`Drop`, `derive`, drop insertion with flags, references as pointers with auto-ref/auto-deref, `Gc[T]` and the conservative collector, associated functions, debug overflow checks (shipped) |
| 3b | NLL borrow checker: conflicts, liveness, lifetime elision for returned references, references in fields, `Gc` runtime exclusivity, scope-exit drops (shipped) |
| 4a | Closures and blocks, `move`, currying and partial application, `\|>`, function values, `for`, `loop`, `break`/`next`, ranges, symbols (shipped) |
| 4b | `?`, `Result`, higher-kinded traits (Functor/Applicative/Monad), `>>=`, `mdo` |
| 5 | Stdlib (`List`, `Map`, `StringBuilder`, `Iterator` with associated types, `Ord`, IO), list patterns, `Char`, sized integers, `import`, `rush test`, Linux/macOS verification |

## Known corners cut in Stage 1

- No lifetime annotations; functions that need them must return owned values.
- No trait objects; all polymorphism is static.
- No paren-less command calls.
- Conservative GC may retain garbage that a stack word happens to resemble.
- When several `Gc` objects die in one collection, a `Drop` that reads another of them sees it already dropped (its strings empty); nothing is freed until every drop has run.
- No package manager or multi-directory modules.
- Borrow checking has no lifetime syntax; a borrowing type has one lifetime, so borrowing one of its fields extends the others; a generic call unions the loans of its reference-holding arguments.
- Moving a field out of a struct is only possible by destructuring the whole value in a pattern (`let Pair { first: a, second: b } = p`), never by `p.first` alone.
- Field names cannot be keywords (`next`, `in`, `type`, ...).
- Trait method signatures and inherent methods must annotate parameters; a trait impl method may omit types and take them from the trait. A trait signature without a return type returns `Unit`.
- Generic trait methods (a method with its own type parameters) are rejected at monomorphization until a plan needs them.
- Unannotated mutually recursive functions are inferred monomorphically within their group.
- `for` iterates over a `Range[Int]` only; iterators and `each`/`map` over collections come in Plan 5.
- No call-once closures: a closure body cannot move a capture out, and a `move` closure's captures are read-only.
- Every `move` closure with captures allocates its environment on the GC heap, even when it is passed directly and never stored; escape analysis could keep that case on the stack later.
