# Rush Plan 4b: `Result`, `?`, Higher-Kinded Traits, `>>=`, and `mdo`

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** `Result[T, E]` and the `?` operator, plus real higher-kinded traits: `Functor`, `Applicative`, and `Monad` with instances for `Option` and `Result[_, E]`, the `>>=` operator, and `mdo` blocks.

**Architecture:** `Type` gains `Hole` and `App`, so a type constructor is an ordinary type with one abstracted parameter (`Option[_]` is `Con("Option", [Hole])`) and a type parameter can be applied (`F[A]` is `App(Param("F"), A)`). Unification decomposes `F[A]` against a concrete `Con`, which is what makes a bound like `F: Monad` resolvable. Trait dispatch keys on a type as it does today, so an instance head is just a constructor-kinded type; method-level type parameters ride along on `Callee::Trait`. `?` and `mdo` are lowerings, not runtime features: `?` becomes a discriminant test with an early `Return`, and `mdo` is desugared by the parser into nested `bind` calls with `move` closures.

**Tech Stack:** Rust 1.98, no crates. C99. `tcc` on Windows.

**Spec:** `docs/superpowers/specs/2026-09-17-rush-stage1-design.md`, sections 3 and 5. Plan 4a (closures, function values, currying, control flow) shipped and is the base branch.

## Global Constraints

- Compiler in Rust with no crates; emits one C99 translation unit; the runtime stays in `runtime/rush_rt.c`/`.h`.
- Every `tests/programs` program must still build and run with `tcc`.
- Diagnostics: file, line, column, one-line message, underlined span; borrow errors carry the "`x` is borrowed here" note.
- `export PATH="$HOME/.cargo/bin:$PATH"` in Git Bash before `cargo`.
- Work on branch `plan4b`, stacked on `plan4a`; PR against `plan4a`.

**Decisions taken for this plan with the owner (2026-09-20):**
- **Higher-kinded traits with inferred kinds.** A type parameter may be applied (`F[A]`); kinds are never written. A trait over a constructor is `trait Functor[F]`, its methods name the parameter (`self: F[A]`), and instances name the constructor: `impl Functor for Option`, `impl[E] Functor for Result[_, E]`.
- **`?` is a suffix operator with an exact error type.** `?` joins the preceding word only right after `def`, `.`, or `:`, so `def empty?`, `o.is_some?`, and `:ok?` keep their meaning; everywhere else `?` is the try operator. It works on `Result[T, E]` and `Option[T]` inside a function returning the same constructor, and the error type must match exactly. No conversion trait in Stage 1.
- **`mdo` blocks with `<-`.** `mdo` ... `end`, where `x <- e` binds monadically, `let x = e` binds purely, and the last expression is the block's value. It desugars to nested `bind` calls with `move` closures.
- **Return-type dispatch for `pure`.** A trait function with no `self` parameter dispatches on its expected return type. When the type is still unknown after inference the error is "cannot infer which instance of `pure` to use; annotate the type".

**Defaults, for owner review:**
1. **The hole is the first type parameter.** Decomposing `F[A]` against `Con(n, args)` binds `F` to `Con(n, [Hole] ++ args[1..])` and `A` to `args[0]`. Rush writes the value parameter first (`Result[T, E]`), so `Result[_, E]` is the only shape a `Result` instance can have, and an instance over the error type is not expressible. `map_err` is a prelude function instead.
2. **Instance heads.** For a higher-kinded trait, a bare constructor name in an impl head means that constructor with a hole in its first parameter: `impl Functor for Option` is `Option[_]`. A head for a constructor with more parameters writes the hole: `impl[E] Functor for Result[_, E]`. Exactly one `_` per head, and `_` is allowed nowhere else in a type.
3. **Supertraits stay bare names.** `trait Applicative[F]: Functor` and `trait Monad[F]: Applicative`; the parameter is implied, because a higher-kinded trait has exactly one.
4. **Typed `self`.** A trait method may write `self: F[A]`. It is the only way to give `self` a type; `&self` and `self` keep their current meaning, and a typed `self` is always by value.
5. **`?` inside a closure** targets the closure's return type, as in Rust. Using `?` directly in an `mdo` block is the error "`?` inside an `mdo` block would return from the block; bind the value with `<-` instead", because the block desugars to closures.
6. **`>>=` is the loosest binary operator**, below `|>`, and left-associative. `a >>= f >>= g` is `(a >>= f) >>= g`, and the parser rewrites `a >>= f` to `a.bind(f)`.
7. **`mdo` desugaring is strictly right to left.** `x <- e` becomes `e.bind(move { |x| rest })`; a `let` line, an expression statement, and a `case`/`if` statement stay statements inside the closure body that follows them. Every bound name is a fresh immutable binding. Because the closures are `move`, an outer non-`Copy` variable used inside the block is moved into the first closure that names it.
8. **`pure` is in scope under its plain name.** A trait function with no `self` is a global under its method name as well as `Trait::method`; a user `def` with the same name in the same file is the usual duplicate-definition error.
9. **Instances shipped:** `Functor`, `Applicative`, and `Monad` for `Option` and for `Result[_, E]`. `List` waits for Plan 5, which is when `List` itself arrives.
10. **`?` on an `Option` in a `Result` function** is an error, not a conversion: "`?` on an `Option[Int]` needs the function to return an `Option`, but it returns `Result[Int, String]`".

## Language rules added by this plan

```ruby
enum Result[T, E]
  Ok(T)
  Err(E)
end

trait Functor[F]
  def fmap[A, B](self: F[A], f: &(A -> B)) -> F[B]
end

trait Applicative[F]: Functor
  def pure[A](v: A) -> F[A]
  def ap[A, B](self: F[A -> B], v: F[A]) -> F[B]
end

trait Monad[F]: Applicative
  def bind[A, B](self: F[A], f: &(A -> F[B])) -> F[B]
end

impl Functor for Option
  def fmap(self, f)
    case self
    in Some(v) then Some(f(v))
    in None then None
    end
  end
end

impl[E] Monad for Result[_, E]
  def bind(self, f)
    case self
    in Ok(v) then f(v)
    in Err(e) then Err(e)
    end
  end
end

def parse_pair(a: &String, b: &String) -> Result[Int, String]
  let x = to_int(a)?                       # returns Err(e) from this function
  let y = to_int(b)?
  Ok(x + y)
end

def sum_two[M: Monad](p: M[Int], q: M[Int]) -> M[Int]
  mdo
    x <- p
    let doubled = x * 2
    y <- q
    pure(doubled + y)
  end
end

def main
  puts("#{parse_pair(&"2", &"3")} #{parse_pair(&"2", &"x")}")
  puts("#{sum_two(Some(1), Some(2))} #{sum_two(None, Some(2))}")
  puts("#{Some(2).fmap({ |v| v + 1 })} #{Some(1) >>= move { |x| Some(x + 1) }}")
end
```

Output: `Ok(5) Err(not a number: x)`, then `Some(4) None`, then `Some(3) Some(2)`.

- **Kinds.** A type parameter applied anywhere in an item's signature is constructor-kinded there; using it bare in the same signature is "type parameter `F` is used both as a type and as a type constructor". A constructor used where a type is expected keeps the existing message, "type `Option` takes 1 type arguments, found 0".
- **Dispatch.** `self.fmap(f)` resolves through the constructor of the receiver's type; `pure(v)` resolves through the constructor of the expected type.
- **`?`.** `e?` where `e: Result[T, E]` in a function returning `Result[U, E]` evaluates to `T` or returns `Err(e)`. The same holds for `Option[T]` in a function returning `Option[U]`.

## Compilation scheme

**Types.**

```rust
pub enum Type {
    Var(u32),
    Param(String),
    Con(String, Vec<Type>),
    Fn(Box<Type>, Box<Type>),
    /// The abstracted parameter of a type constructor: `Option[_]` is `Con("Option", [Hole])`.
    Hole,
    /// `F[A]`, kept only while the head is a `Var` or `Param`.
    App(Box<Type>, Box<Type>),
}

/// `apply(Con("Option", [Hole]), Int)` is `Option[Int]`; a variable head stays an `App`.
pub fn apply(head: Type, arg: Type) -> Type {
    match head {
        Type::Con(n, args) => Type::Con(n, args.into_iter().map(|a| if a == Type::Hole { arg.clone() } else { a }).collect()),
        h => Type::App(Box::new(h), Box::new(arg)),
    }
}
```

Unification adds three cases: `(App(h1, a1), App(h2, a2))` unifies heads and arguments; `(App(h, a), Con(n, args))` with a non-empty `args` unifies `h` with `Con(n, [Hole] ++ args[1..])` and `a` with `args[0]`; `(Hole, Hole)` succeeds. A `Con(n, [])` against an `App` is "`{n}` takes no type arguments, so it cannot be used as `F[A]`".

**Dispatch.** `Callee::Trait` gains the method's own type arguments:

```rust
Trait { trait_name: String, method: String, self_ty: Type, targs: Vec<Type> }
```

`self_ty` is the type dispatch keys on: the receiver's type for an ordinary method, the constructor-kinded type for a higher-kinded trait (`Option[_]`), and the expected return type's constructor for a function without `self`. `mono::resolve_trait` matches it against impl heads, then instantiates the impl's method with the impl's generics followed by `targs`, which is what lifts today's "generic trait methods are not supported" restriction.

**`?`.** `e?` on `Result[T, E]` in a function returning `Result[U, E]`:

```
_t = e
_d = discriminant(_t)
if _d == 1 goto err_bb else ok_bb          # 1 is Err's index
err_bb: _0 = Err(move (_t as Err).0); return
ok_bb:  _r = move (_t as Ok).0
```

The existing drop pass inserts scope-exit drops on the new `Return` edge, so a `?` that returns early still drops the locals it leaves.

**`mdo`.** The parser rewrites right to left, so

```ruby
mdo
  x <- p
  let k = x * 2
  y <- q
  pure(k + y)
end
```

becomes `p.bind(move { |x| let k = x * 2 ; q.bind(move { |y| pure(k + y) }) })`, with the `let` as a statement of the first closure's body. Nothing reaches the MIR that `bind` and closures do not already cover.

## File structure

| File | Change |
|---|---|
| `src/lexer.rs` | `?`/`!` join a word only after `def`, `.`, or `:`; `?` is otherwise the `Op("?")` token |
| `src/ast.rs` | `TypeExpr::Hole`, `ExprKind::Try`; `mdo` and `<-` are desugared in the parser and add no node |
| `src/parser.rs` | `_` as a type argument, typed `self`, postfix `?`, `>>=`, `mdo` blocks with `<-` |
| `src/types/mod.rs` | `Type::{Hole, App}`, `apply`, `Display`, `subst`, `is_copy`/`contains_in` arms, `from_ast` for `F[A]` and `_`, kind checking |
| `src/types/decls.rs` | Higher-kinded trait and impl heads: a bare constructor name gets a hole; one hole per head; no-`self` trait functions as plain globals |
| `src/types/infer.rs` | Unification for `App`/`Hole`, `Try` rules, return-type dispatch, method-level type arguments, the `pure` ambiguity error |
| `src/mir.rs` | `Callee::Trait.targs`; `Try` lowering |
| `src/mono.rs` | Method-level type arguments in `resolve_trait`; the rejection at `src/mono.rs:75` goes away |
| `src/cgen.rs` | Nothing new; `Hole` and `App` never reach it |
| `std/prelude.rush` | `Result[T, E]` with `Show`/`Eq`/`Clone` and methods; `Functor`/`Applicative`/`Monad` with `Option` and `Result[_, E]` instances |
| `tests/programs/*.rush` | `results`, `monads`, `mdo` |
| `tests/errors/*.rush` | `try_not_result`, `try_wrong_return`, `try_error_mismatch`, `pure_ambiguous`, `no_monad_instance`, `mdo_ends_with_bind`, `arrow_outside_mdo`, `kind_mismatch` |

---

## Tasks

### Task 1: `Result[T, E]` in the prelude

**Files:** `std/prelude.rush`; `tests/programs/results.rush` (created here, extended in Task 8).

- Add `enum Result[T, E]` with `Ok(T)` and `Err(E)` next to `Option` at `std/prelude.rush:34`.
- `impl[T: Show, E: Show] Show for Result[T, E]` with `to_s` returning `"Ok(#{v})"` and `"Err(#{e})"`, mirroring `Show for Option[T]` at `std/prelude.rush:98`.
- `impl[T: Eq, E: Eq] Eq for Result[T, E]` matching on `(self, other)` like `Eq for Option[T]` at `std/prelude.rush:143`.
- `impl[T: Clone, E: Clone] Clone for Result[T, E]`.
- Inherent methods:

```ruby
impl[T, E] Result[T, E]
  def is_ok?(&self) -> Bool
    case self
    in Ok(_) then true
    in Err(_) then false
    end
  end

  def is_err?(&self) -> Bool
    not self.is_ok?
  end

  def ok(self) -> Option[T]
    case self
    in Ok(v) then Some(v)
    in Err(_) then None
    end
  end

  def unwrap_or(self, default: T) -> T
    case self
    in Ok(v) then v
    in Err(_) then default
    end
  end
end
```

- `def map_err[T, E, F](r: Result[T, E], f: &(E -> F)) -> Result[T, F]` as a prelude function, since default 1 makes an instance over the error type inexpressible.

- [ ] Tests: a program that builds `Ok(1)` and `Err("x")`, prints both (`Ok(1)` and `Err(x)`), compares them with `==`, clones one, and calls each method; a unit test in `src/types/infer.rs` that `Ok(1)` infers `Result[Int, ?]` and unifies with an annotated `Result[Int, String]`. Commit `feat: Result in the prelude`.

### Task 2: `Hole`, `App`, and kinds

**Files:** `src/ast.rs`, `src/parser.rs` (`type_atom`, `src/parser.rs:408`), `src/types/mod.rs`, `src/types/infer.rs` (`unify`, `src/types/infer.rs:37`).

- `ast.rs`: add `TypeExpr::Hole(Span)` and extend `TypeExpr::span` at `src/ast.rs:131`.
- `parser.rs`: in `type_atom`, an identifier `_` produces `TypeExpr::Hole` before the generic-argument branch.
- `types/mod.rs`: add `Type::Hole` and `Type::App(Box<Type>, Box<Type>)` plus the `apply` helper from the compilation scheme; extend `subst` (substitute both sides of an `App`, then re-`apply` so a resolved head collapses), `Display` (`Hole` prints `_`, `App(h, a)` prints `{h}[{a}]`), `contains_in`, `is_copy` (neither a `Hole` nor an unresolved `App` is `Copy`), `head`, and `peel`.
- `from_ast` at `src/types/mod.rs:567`: a name in `env.generics` with arguments becomes a left-nested `App` instead of today's error; `TypeExpr::Hole` becomes `Type::Hole`, and is rejected unless a new `TypeEnv.allow_hole` is set ("`_` is only allowed in an impl head").
- Kind check, once per item after its signature resolves: collect the generics used applied and the generics used bare; an intersection is "type parameter `F` is used both as a type and as a type constructor".
- `unify`: the three cases from the compilation scheme, placed before the final mismatch arm.

- [ ] Tests (unit): `apply(Con("Option",[Hole]), Int)` is `Option[Int]`; `Con("Result",[Hole, Param E])` displays as `Result[_, E]`; `subst` of `F := Option[_]` through `App(Param F, Int)` is `Option[Int]`; unifying `App(Var, Var)` with `Result[Int, String]` binds the head to `Result[_, String]` and the argument to `Int`; unifying `App(Var, Var)` with `Int` is the takes-no-type-arguments error; `def f[F](x: F[Int], y: F) -> Int` is the both-kinds error; `_` outside an impl head errors. Commit `feat: type constructors, application, and kinds`.

### Task 3: Higher-kinded traits and instance heads

**Files:** `src/parser.rs` (`def_header`, `src/parser.rs:193`), `src/types/mod.rs` (`TraitInfo`, `src/types/mod.rs:306`), `src/types/decls.rs`.

- `def_header`: accept `self: TypeExpr` in the parameter list, stored as a new typed-receiver variant beside `&self` and `&mut self`. A typed `self` is by value.
- `TraitInfo` gains `param: Option<String>`: the trait's single type parameter when any method signature applies it, which is how a trait is known to be higher-kinded.
- `decls.rs`: resolving an impl head for a higher-kinded trait turns a bare constructor name into `Con(name, [Hole, fresh impl generics...])` with the hole first, so `impl Functor for Option` is `Con("Option", [Hole])`; a head that writes its own `_` resolves as written. Validate exactly one `Hole` in a higher-kinded head, none in any other ("`{trait}` is not higher-kinded, so its instance head cannot contain `_`"), and keep the existing arity error otherwise.
- A trait method's `self: F[A]` resolves with `F` bound to the trait's parameter; inside an impl, `F` is the impl head, so `self` has type `apply(head, A)`.
- Supertraits of a higher-kinded trait are bare names (default 3), and `decls.rs` passes the same parameter down when it checks them.

- [ ] Tests: `trait Functor[F]` with `def fmap[A, B](self: F[A], f: &(A -> B)) -> F[B]` plus `impl Functor for Option` type-checks; `impl Functor for Int` is the takes-no-type-arguments error; `impl Functor for Result` without a hole is "type `Result` takes 2 type arguments, found 0"; `impl[E] Show for Result[_, E]` is the not-higher-kinded error; a typed `self` round-trips in a parser AST test. Commit `feat: higher-kinded traits and instance heads`.

### Task 4: Type arguments for trait methods

**Files:** `src/mir.rs` (`Callee`, `src/mir.rs:125`), `src/types/infer.rs`, `src/mono.rs` (`resolve_trait`, `src/mono.rs:59`).

- `mir.rs`: add `targs: Vec<Type>` to `Callee::Trait`, the method's own type arguments in the order of its scheme vars after the trait's parameter. Existing traits pass `vec![]`.
- `infer.rs`: record the instantiated method-level arguments for a trait method call the way `TypeInfo.insts` already records them for a generic global, and carry them into the MIR callee.
- `mono.rs`: build the instantiation as the impl's generics from the head match followed by the call's `targs`; the guard becomes `n_vars == imp.generics.len() + targs.len()`, and the user-facing rejection at `src/mono.rs:75` becomes an internal invariant message.
- Trait default methods are instantiated with the same list.

- [ ] Tests: a `mono` unit test that `fmap` on `Option[Int]` with `A = Int, B = String` resolves to the impl body mangled with those arguments, and that a second instantiation at `B = Int` produces a second body; a trait with an ordinary generic method (`trait Pair` with `def with[U](&self, u: U) -> Unit`) now compiles, which is the corner the spec listed as rejected. Commit `feat: type arguments for trait methods`.

### Task 5: `Functor`, `Applicative`, `Monad`, and return-type dispatch

**Files:** `std/prelude.rush`, `src/types/decls.rs`, `src/types/infer.rs` (`solve_pending`, `src/types/infer.rs:470`).

- Prelude: the three traits and six instances from the language-rules section, with bare supertrait names.
- `decls.rs`: a trait function with no `self` parameter is registered as a global under its plain name as well as `Trait::method` (default 8).
- `infer.rs`: calling such a global instantiates its scheme with a fresh variable for the trait's parameter and records a pending constraint on it; the call's dispatch type is that variable, resolved at the end of the body.
- `solve_pending`: a leftover constraint whose type is still a `Var` and whose trait has a parameter reports "cannot infer which instance of `{method}` to use; annotate the type", pointing at the call.
- Lowering: `Callee::Trait { trait_name: "Applicative", method: "pure", self_ty: <resolved constructor>, targs: vec![A] }`.

- [ ] Tests: `let o: Option[Int] = pure(1)` is `Some(1)`; a bare `pure(1)` is the ambiguity error; `Some(2).fmap({ |v| v + 1 })` is `Some(3)` and the same on a `Result[Int, String]` is `Ok(3)`; `Some({ |x: Int| x + 1 }).ap(Some(2))` is `Some(3)`; `def twice[M: Monad](m: M[Int], f: &(Int -> M[Int])) -> M[Int]` compiles and runs with `Option` and with `Result`; `1.fmap(f)` is "no instance of `Functor` for `Int`". Commit `feat: Functor, Applicative, and Monad`.

### Task 6: The `?` operator

**Files:** `src/lexer.rs:135`, `src/ast.rs`, `src/parser.rs`, `src/types/infer.rs`, `src/mir.rs`.

- `lexer.rs`: a trailing `?` or `!` joins the word only when the word directly follows `def`, `.`, or `:` (the symbol case); otherwise `?` is `Op("?")`. Keep the existing guard that `!=` never joins.
- `ast.rs`: `ExprKind::Try(Box<Expr>)`, walked like any unary expression.
- `parser.rs`: postfix `?` in the same loop that parses calls, `.`, and indexing, so `f(x)?.field` parses left to right.
- `infer.rs`: the operand must resolve to `Result[T, E]` or `Option[T]` ("`?` needs a `Result` or an `Option`, found `{ty}`"; an unresolved variable is "cannot infer the type of the value before `?`"). The frame's `ret_ty` (`src/types/infer.rs:101`) must be the same constructor, with `E` unified exactly ("`?` on a `Result[{T}, {E}]` needs the function to return `Result[_, {E}]`, but it returns `{ret}`", and default 10's message for the `Option` case). Inside an `mdo` block, report default 5's message. The expression's type is `T`.
- `mir.rs`: the lowering from the compilation scheme, reusing the `Downcast` projection and `MoveOut` that `case` already emits, and `Terminator::Return` so the drop pass runs.

- [ ] Tests: lexer — `def empty?`, `o.is_some?`, `:ok?`, `x?` (identifier `x` then `Op("?")`), and `a != b` unchanged; parser — `f(x)?` is `Try(Call)`; infer — the four error messages; MIR dump — a discriminant test, an `Err` return, and a move of the `Ok` payload; a program where `?` returns early from inside a loop still drops a `Drop` local. Commit `feat: the ? operator`.

### Task 7: `>>=` and `mdo`

**Files:** `src/parser.rs`, `src/ast.rs`.

- `>>=`: a binary operator at the loosest precedence, below `|>`, left-associative, rewritten in the parser to `a.bind(f)`.
- `mdo`: parse `mdo` NEWLINE statements `end`, where a statement is `name <- expr`, an ordinary `let`, or an expression. Desugar right to left per default 7: `name <- e` with a non-empty rest becomes `e.bind(move { |name| rest })` with `rest` the block of the statements that follow; other statements stay where they were written.
- Errors: "an `mdo` block must end in an expression" when the last statement is a bind or a `let`; "an `mdo` block needs at least one statement"; "`<-` is only allowed in an `mdo` block" from the ordinary statement parser.

- [ ] Tests (AST shape and programs): `a >>= f >>= g` is `a.bind(f).bind(g)`; `x |> f >>= g` groups as `(x |> f) >>= g`; an `mdo` with one bind, with a `let` between two binds, and with a trailing `pure`; the three error messages; a program running the `sum_two` example over `Option` and `Result`. Commit `feat: >>= and mdo blocks`.

### Task 8: Golden and error programs

**Files:** `tests/programs/`, `tests/errors/`.

- `tests/programs/results.rush`: `Ok`/`Err`, `Show`, `Eq`, `Clone`, `is_ok?`, `ok`, `unwrap_or`, `map_err`, and a `?` chain across three functions, one of which returns early; a `Drop` local declared before a `?` that returns `Err`, to show the drop still runs.
- `tests/programs/monads.rush`: `fmap`, `ap`, and `bind` on `Option` and on `Result[Int, String]`; `pure` with an annotated `let`; a generic `def twice[M: Monad]` called with both; a closure returned from `bind`.
- `tests/programs/mdo.rush`: an `mdo` over `Option` that short-circuits on `None`, an `mdo` over `Result` that short-circuits on `Err`, a `let` line between binds, an `mdo` nested inside a closure, and an `mdo` whose value feeds `>>=`.
- Error programs, one each: `try_not_result` (`1?`), `try_wrong_return` (`?` in a function returning `Int`), `try_error_mismatch` (a `Result[_, String]` in a function returning `Result[_, Int]`), `pure_ambiguous`, `no_monad_instance` (`1 >>= f`), `mdo_ends_with_bind`, `arrow_outside_mdo`, `kind_mismatch` (`def f[F](x: F[Int], y: F)`).
- All Plan 1, 2, 3a, 3b, and 4a programs still pass.

- [ ] Commit `feat: Result, try, and monad golden and error programs`.

### Task 9: Docs and PR

- [ ] README: a short `Result`/`?` example and a two-line `mdo` example. Spec: mark plan row 4b shipped; add the four owner decisions and the defaults to the decision table; update section 3 to name type constructors, `F[A]`, and kind inference, and section 5 to say which instances exist; remove "Generic trait methods ... are rejected at monomorphization" from the known corners and add: the hole is the first type parameter, no functor over an error type, `?` has no error conversion, and no `List` instances until Plan 5.
- [ ] `cargo build --release`, `cargo test --release`, all programs, `git status` clean, push `plan4b`, PR against `plan4a`.

---

## Self-review against the spec

- **Covered:** `Result[T, E]` and `?` (section 1's errors decision and section 5's types); higher-kinded `Functor`/`Applicative`/`Monad` with instances (sections 3 and 5); `>>=` and `mdo` (section 1's keyword list and the FP features decision row); generic trait methods, which the spec's known corners list as rejected "until a plan needs them" — this is that plan.
- **Not covered, by design:** `List` and its instances, `Iterator`, and the rest of the stdlib (Plan 5); error conversion at `?`; an instance over a `Result`'s error type; written kind syntax.
- **Differs from the spec's wording:** the spec writes `Result[_, E]` for the instance without saying which parameter the hole is; default 1 fixes it as the first, the only choice that lets a `Monad` thread `Result[T, E]`'s value parameter.
- **Owner review points:** the ten defaults at the top.
