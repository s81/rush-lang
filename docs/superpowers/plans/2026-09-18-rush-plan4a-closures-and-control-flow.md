# Rush Plan 4a: Closures, Function Values, Currying, and Control Flow

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Functions are values. Blocks `{ |x| ... }` and `do |x| ... end` are closures that capture by reference, or by move with `move`. Every function is curried: a named function, method, associated function, or variant constructor can be passed as a value or partially applied, and `x |> f(a)` pipes. Control flow gains `loop`/`break e`/`next`, `for x in a..b`, ranges, and symbols.

**Architecture:** Inference records each closure's captures and capture modes. Lowering turns a closure literal into a separate MIR body plus a `MakeFn` rvalue that builds its environment, and calls through values with `Callee::Value`. The borrow checker tracks function values like references, so a closure that borrows cannot escape. After monomorphization every function type has a known arity. cgen emits one entry function per `MakeFn` site and calls values through a code pointer.

**Tech Stack:** Rust 1.98, no crates. C99. `tcc` on Windows.

**Spec:** `docs/superpowers/specs/2026-09-17-rush-stage1-design.md`, sections 1–3. Plan 4b (`?`, `Result`, higher-kinded traits, Functor/Applicative/Monad, `>>=`, `mdo`) follows.

## Global Constraints

- Compiler in Rust with no crates; emits one C99 translation unit; the runtime stays in `runtime/rush_rt.c`/`.h`.
- Every `tests/programs` program must still build and run with `tcc`.
- Diagnostics: file, line, column, one-line message, underlined span; borrow errors carry the "`x` is borrowed here" note.
- `export PATH="$HOME/.cargo/bin:$PATH"` in Git Bash before `cargo`.

**Decisions taken for this plan with the owner (2026-09-18):**
- Plan 4 splits into 4a (this plan) and 4b (monads and higher-kinded traits). Symbols are in 4a.
- **Owned and borrowed closures.** `A -> B` is an owned function value: named functions, `move` closures, and closures that capture nothing. It is `Copy`, its environment lives on the GC heap, and it can be stored and returned. A closure without `move` that captures something has type `&(A -> B)`. Its environment is on the stack and it holds loans on what it captures, so the borrow checker stops it from escaping. A function that takes a plain block declares `f: &(T -> Unit)`.
- **`|>` supplies the last argument.** `x |> f(a)` is `f(a, x)`, and `x |> f` is `f(x)`.
- **Function values:** besides defs and closures, variant constructors (`Some`, `Rect(2.0)`), associated functions (`Point.new`), and methods named through their type (`Shape.area : &Shape -> Float`) are values and can be partially applied.
- **`move` captures are read-only.** The body of a `move` closure cannot assign to or mutably borrow a captured variable: "cannot assign to captured `count` in a move closure". Shared mutable state goes in a `Gc`.
- **`return` in a block** returns from the block, as in Rust. `break` and `next` refer to loops inside the block; outside one they are "`break` outside of a loop".

**Defaults, for owner review:**
1. **Capture modes (non-`move`).** A captured variable is borrowed `&mut` if the body assigns to it, borrows it `&mut`, or calls a `&mut self` method on it (the variable must be `let mut`). A captured variable of type `&mut T` is captured as a reborrow `&mut *r`. Everything else is captured by `&`. `move` captures copy `Copy` values and move the others.
2. **No call-once closures.** A closure body cannot move a captured variable out: "cannot move captured `s` out of a closure; clone it instead". Every closure can be called any number of times.
3. **Borrowing function values stay local.** A function value that holds a loan (a borrowing closure copied out of its reference, or a partial application with a borrowed argument) cannot be passed to a parameter whose type contains an owned function type, stored in `Gc`, or returned. The message is "function value borrows `total` and cannot be passed as an owned function; use `move` or take `&(A -> B)`". This is the rule that stops an `&(A -> B)` closure from escaping through a copy.
4. **Closures and references.** A closure's returned reference must borrow from its one reference parameter (elision over its declared parameters). Returning a borrow of a captured variable is "cannot return a reference to a captured variable". The result of calling a function value gets the loans of every argument and of the value itself (rule 4 of Plan 3b).
5. **`|>` evaluation order.** `x |> f(a)` is rewritten in the parser to `f(a, x)`, so `a` is evaluated before `x`.
6. **Blocks.** `{ |x, y: Int| e }`, `do |x| ... end`, and `move` in front of either. Parameters are names with optional types; the return type is inferred. A block right after a call's `)`, after a bare call name, or after a method call is appended as the last argument. On its own, `{` starts a block only when followed by `|` (a zero-parameter block is `{ || e }`), which leaves `{ "k" => v }` free for Plan 5 maps. A zero-parameter block has type `Unit -> R` and is called with `f()`.
7. **Ranges and `for`.** `a..b` includes `b`, `a...b` excludes it (Ruby). A range is the prelude struct `Range[T] { start: T, stop: T, exclusive: Bool }` and shows as `1..5`. In 4a, `for` iterates over a `Range[Int]` only. Anything else is "`for` needs a `Range[Int]` in this version", and iterators come in Plan 5. `..` binds more loosely than `or`, and `|>` more loosely still.
8. **Loops.** `loop` yields the value of its `break e`; a `loop` with no `break` has an unconstrained type, which defaults to `Unit`. `break` in `while` and `for` takes no value. `break` and `next` drop the locals of the scopes they leave, in reverse order.
9. **Symbols.** `:name` is a `Symbol`: `Copy`, compared with `==`, usable as a `case` pattern (a `case` on symbols needs `_` or `else`). `to_s` is `"name"`, `inspect` (and derived `Show`) is `":name"`. A `:` starts a symbol only when an identifier character follows it and it does not directly follow an identifier or closing bracket, so `x: Int` and `{ f:v }` keep their meaning.
10. **Runtime shape.** A function value is a pointer to an object whose first word is a code pointer. After monomorphization the arity of a function type is its number of top-level arrows, so a call that supplies every argument is one indirect C call, and one that supplies fewer builds a partial application on the GC heap. A closure without captures, a named function, and a constructor with no bound arguments need no allocation.

## Language rules added by this plan

```ruby
enum Shape
  Circle(Float)
  Rect(Float, Float)
end

impl Shape
  def area(&self) -> Float
    case self
    in Circle(r) then 3.0 * r * r
    in Rect(w, h) then w * h
    end
  end
end

def each_to(n: Int, f: &(Int -> Unit))
  for i in 1..n
    f(i)
  end
end

def adder(k: Int) -> Int -> Int
  move { |x| x + k }                     # owned: can be returned
end

def twice(f: &(Int -> Int), x: Int) -> Int
  f(f(x))
end

def add(a: Int, b: Int) -> Int
  a + b
end

def main
  let mut total = 0
  each_to(3) { |i| total += i }          # borrows total mutably for the call
  puts(&int_to_s(total))                 # 6
  let inc = add(1)                       # partial application: Int -> Int
  puts(&int_to_s(twice(&inc, 5)))        # 7
  puts(&int_to_s(5 |> adder(10)))        # 15
  let area = Shape.area                  # &Shape -> Float
  puts(&float_to_s(area(&Rect(2.0, 3.0))))
  let wrap = Some                        # Int -> Option[Int]
  puts("#{wrap(1)}")                     # Some(1)
  let found = loop
    total += 1
    if total > 8
      break total
    end
  end
  puts("#{found} #{:done} #{:done.inspect}")   # 9 done :done
  # let f = { |x| total += x }           # ok, f: &(Int -> Unit)
  # adder_store(f)                       # error: function value borrows `total` ...
end
```

- **Closure types.** A closure literal with parameter types `A1..An` and result `R` has type `A1 -> ... -> An -> R`. It is `&(...)` when it is not `move` and captures at least one variable.
- **Captures.** A name inside a closure body that resolves to a local of an enclosing function (or enclosing closure) is a capture of every closure between the use and the binding. Nested closures capture transitively.
- **Passing blocks.** A parameter `f: &(A -> B)` accepts a borrowing closure literal as it is. It accepts an owned value temporary (a named function, a `move` or capture-free closure) by auto-borrow, and a named local `g` as `&g`. A parameter `f: A -> B` accepts owned values only. A borrowing closure literal there is the rule 3 error, reported early by inference with the same message and span.
- **Calling a value.** `f(a, b)` where `f` is a local or an expression of type `A -> B -> C` or `&(A -> B -> C)`. Supplying fewer arguments than the arity builds a partial application. `f()` on a `Unit -> R` value passes `()`.
- **Over-application.** `add3(1, 2)(3)` and `adder(1, 2)` (a def with one parameter whose result is a function) both work. The def is called with its parameters, and the rest are applied to the result.
- **Control flow.** `loop`/`end`, `break`, `break e`, `next`, `for x in r`/`end`. `x` is a fresh immutable binding per iteration.

## Compilation scheme

Closure literal `{ |x| total += x }` inside `main` (the second closure in `main`):

```
MIR main:   _7 = &mut _1                                  # total, mutable capture
            _8 = make_fn closure main#c1 [_7] stack       # _8: Int -> Unit
            _9 = &_8                                      # the value of the literal: &(Int -> Unit)
MIR main#c1(_1: &Tuple[&mut Int], _2: Int) -> Unit
            (*(*_1).0) = (*(*_1).0) + _2
C:          struct rush_env_main_1 { void *code; rush_Tuple_L_Ref_mut_Int_R env; };
            static rush_unit rush_entry_main_1(rush_fn *self, int64_t a1)
            { return rush_main_c1(&((struct rush_env_main_1 *)self)->env, a1); }
```

- `Rvalue::MakeFn { code: FnCode, env: Vec<Operand>, alloc: Alloc }` with `Alloc::{Static, Stack, Heap}`:
  - `FnCode::Closure { name, targs }`: env operands are the captures in `ClosureInfo` order;
  - `FnCode::Global(Callee)`: a def, method, associated function, or trait method, and env operands are its first bound arguments;
  - `FnCode::Variant(Type, usize)`: env operands are the first bound fields.
- `Static` when env is empty. `Stack` for a non-`move` closure with captures (cgen declares the env struct as a local of the C function). `Heap` for everything else, allocated with `rush_gc_alloc` and a generated drop function when a field needs drop glue.
- `Callee::Value(Operand)` calls a function value. The operand has type `A -> B` or `&(A -> B)`. With `k` arguments and arity `n` (known after mono): `k == n` is one indirect call; `k < n` builds a heap partial application whose entry calls the value with the bound arguments and the rest.
- A closure body is an ordinary `Body` named `{parent}#c{k}` (`k` counts closures in source order within the parent). Its `_1` is the environment reference `&Tuple[field types]` (`&Unit` when empty), and the declared parameters follow. Its type parameters are the parent's. Body field `captures: Vec<String>` names the env fields, for diagnostics.
- An entry function per `MakeFn` site has signature `R entry(rush_fn *self, A1..An)` for the site's concrete type. It unpacks the env, calls the target with the bound values and the first arguments, and applies any remaining arguments to the result.

## File structure

| File | Change |
|---|---|
| `src/lexer.rs` | `:sym` token; `..`/`...` already lex |
| `src/ast.rs` | `ExprKind::{Closure, Loop, Break, Next, For, Range, Symbol}`, `Lit::Symbol`, `ClosureParam` |
| `src/parser.rs` | Blocks, trailing blocks, `move`, `\|>` rewrite, `loop`/`break`/`next`/`for`, ranges, symbol literals and patterns |
| `src/types/mod.rs` | `Symbol` Copy and primitive; `ClosureInfo`, `Capture`, `CaptureMode`; `TypeInfo.closures`; `GlobalKind::Closure`; `DotRes::MethodValue`; `contains_fn`, `may_borrow`, `arity` |
| `src/types/infer.rs` | Closure frames and capture recording; function values; value calls; loops, `for`, ranges, symbols; move-capture and escape errors |
| `src/types/exhaust.rs` | Symbol literals are an infinite domain |
| `src/mir.rs` | `MakeFn`, `FnCode`, `Alloc`, `Callee::Value`, `Const::Symbol`; closure bodies; partial and over-application; loop contexts; `for` lowering |
| `src/ownck.rs` | Moves into `move` envs; no move out of captures |
| `src/borrowck.rs` | Track `may_borrow` locals; loans through `MakeFn`; owned-function argument rule; value-call result loans; closure elision |
| `src/mono.rs` | Instantiate closure bodies and `FnCode`/`Callee::Value` types |
| `src/cgen.rs` | `rush_fn*`, env structs, entry functions, indirect and partial calls, symbols |
| `runtime/rush_rt.c`, `.h` | `rush_fn`, `rush_sym_to_s` |
| `std/prelude.rush` | `Range[T]` with `Show`; `Show`, `Eq`, `Clone`, `Copy` for `Symbol`; `sym_to_s` extern |
| `tests/programs/*.rush` | `closures`, `fn_values`, `control`, `closure_drop` |
| `tests/errors/*.rush` | Escape, move-capture, move-out, borrow-conflict, loop-control, `for` errors |

---

### Task 1: Symbols and ranges, end to end

**Files:** `src/lexer.rs`, `src/ast.rs`, `src/parser.rs`, `src/types/mod.rs`, `src/types/infer.rs`, `src/types/exhaust.rs`, `src/mir.rs`, `src/cgen.rs`, `runtime/rush_rt.c`, `runtime/rush_rt.h`, `std/prelude.rush`

**Interfaces:**
- Produces: `Tok::Sym(String)`, `ExprKind::Symbol(String)`, `Lit::Symbol(String)`, `ExprKind::Range(Box<Expr>, Box<Expr>, bool /* exclusive */)`, `Const::Symbol(String)`, type `Symbol`, prelude `struct Range[T]`.

- Lexer: `:` followed by an identifier start, where the previous character is not an identifier character, `)`, or `]`, lexes `Tok::Sym(name)`; the name may end in `?` or `!`.
- Parser: symbol literal in `primary` and in patterns (`Lit::Symbol`). Ranges: a new level `range := binary(1) [(".." | "...") binary(1)]`, called from `expr`; non-associative. Test: `1..n - 1` parses as `1..(n - 1)`.
- Types: `Symbol` is `Copy`, `is_primitive` (so `==` is `Binary(Eq)`), and a pattern literal type. `Range(a, b, _)` unifies `a` and `b` and has type `Range[T]`. It lowers as `Aggregate(Struct(Range[T]), [a, b, Const::Bool(exclusive)])`.
- exhaust: symbol literal patterns behave like string literals (need a catch-all).
- Prelude:
  ```ruby
  extern "C" def sym_to_s(s: Symbol) -> String

  struct Range[T]
    start: T
    stop: T
    exclusive: Bool
  end

  impl[T: Show] Show for Range[T]
    def to_s(&self)
      if @exclusive
        "#{@start}...#{@stop}"
      else
        "#{@start}..#{@stop}"
      end
    end
  end

  impl Show for Symbol
    def to_s(&self)
      sym_to_s(*self)
    end
    def inspect(&self)
      ":#{sym_to_s(*self)}"
    end
  end
  ```
  Also add `Eq`, `Clone`, and `Copy` for `Symbol`, following the `Bool` ones.
- cgen: `c_type(Symbol)` is `const char *`. Each distinct symbol gets `static const char rush_sym_<n>[] = "name";` and `Const::Symbol` is `rush_sym_<n>`. Primitive `==` on symbols compares pointers. Runtime: `rush_str rush_sym_to_s(const char *s)` returns a `cap == 0` string over `s`.

- [ ] Tests: lexer `:a`, `f(:ok?)`, `x: Int` (no symbol), `{ f:v }` (no symbol); parser range precedence; infer `Symbol` and `Range[Int]`; a non-exhaustive symbol `case` errors; cgen output contains one static per distinct symbol. A small program printing `#{:a} #{:a.inspect} #{:a == :a} #{:a == :b} #{1..3} #{1...3}` prints `a :a true false 1..3 1...3`. Commit `feat: symbols and ranges`.

### Task 2: `loop`, `break`, `next`, `for`

**Files:** `src/ast.rs`, `src/parser.rs`, `src/types/infer.rs`, `src/mir.rs`

**Interfaces:**
- Consumes: `Range[T]` from Task 1.
- Produces: `ExprKind::Loop(Block)`, `ExprKind::Break(Option<Box<Expr>>)`, `ExprKind::Next`, `ExprKind::For { var: String, var_span: Span, iter: Box<Expr>, body: Block }`; infer's `loops: Vec<LoopKind>` (`Loop(Type)`, `While`), saved and reset per closure frame in Task 4.

- Parser: `loop` NEWLINE block `end`; `break` with an optional expression on the same line; `next`; `for NAME in expr` NEWLINE block `end` (`_` allowed as the name).
- infer: `loop` pushes `Loop(fresh)` and has that type; `break e` unifies with it; `break` alone unifies `Unit`; `break`/`next` in `while`/`for` take no value (`break e` there is "`break` with a value is only allowed in `loop`"); outside any loop: "`break` outside of a loop" / "`next` outside of a loop". `for`: the iterator must unify with `Range[Int]`, else "`for` needs a `Range[Int]` in this version"; the variable is an immutable `Int` in the body's scope; the `for` has type `Unit`. `while` and `for` push `While`.
- MIR: `Lowerer.loops: Vec<LoopCtx { break_bb, next_bb, value: Option<LocalId>, scope_depth: usize }>`. `break`/`next` emit `StorageDead` for every local of the scopes deeper than `scope_depth`, innermost first and in reverse declaration order (the same list scope-end uses), then `Goto`. After a `break`/`next`/`return`, lowering continues in a fresh unreachable block, as `return` does today. `for i in r` lowers to:
  ```
  r_t = <iter>; i_t = r_t.start; stop = r_t.stop; ex = r_t.exclusive
  head:  c = if ex { i_t < stop } else { i_t <= stop }; if c goto body else exit
  body:  (scope) i = i_t; <body>; goto step          # next -> step
  step:  if !ex and i_t == stop goto exit; i_t = i_t + 1; goto head
  exit:
  ```
  The `i_t == stop` check comes before the increment, so `for i in 0..MAX` never overflows.

- [ ] Tests: infer types for `let x = loop ... break 5 ... end` (`Int`) and a `loop` without `break` (`Unit`); the three error messages; MIR dump: `break` out of two nested scopes drops inner locals first; `next` in `for` goes to the step block. Program: sum `1..4` (10) and `1...4` (6), `next` on even numbers, `break` from `while`, `loop` yielding a value, a `Drop` value declared in a loop body that is dropped on `break`. Commit `feat: loop, break, next, and for over ranges`.

### Task 3: Parsing blocks, `move`, trailing blocks, and `|>`

**Files:** `src/ast.rs`, `src/parser.rs`

**Interfaces:**
- Produces: `ExprKind::Closure { params: Vec<ClosureParam>, body: Block, is_move: bool }`, `pub struct ClosureParam { pub name: String, pub ty: Option<TypeExpr>, pub span: Span }`.

- `primary`: `{` followed by `|` parses `{ |params| stmts }`. The body is a statement list up to `}`, so `{ |x| a; b }` is not allowed (no semicolons); a multi-line brace body is allowed. `||` is two `|` tokens meaning no parameters. `do [|params|] NEWLINE block end`. `move` before either sets `is_move`.
- Trailing block: after `call_args` of a call, after a bare identifier callee (`each_item { |x| .. }` is `Call(each_item, [block])`), and after a method call with or without arguments, a `{ |` or `do` on the same line is parsed and appended to the arguments. For a `Dot` with `args: None`, the args become `Some(vec![block])`. `move` may precede a trailing block. A `{` after a bare name that is not followed by `|` or `||` is the existing struct literal path (CamelCase) or an error.
- `|>`: the lowest precedence level, left associative, `pipe := range ("|>" range)*`. Rewrite at parse time: rhs `Call(f, args)` becomes `Call(f, args ++ [lhs])`; rhs `Dot { args: Some(a) }` becomes `Dot { args: Some(a ++ [lhs]) }`; rhs `Dot { args: None }` becomes `Dot { args: Some([lhs]) }`; any other rhs (a name, a closure, a parenthesized expression) becomes `Call(rhs, [lhs])`. A line ending in `|>` continues onto the next line (it is an operator).

- [ ] Tests (AST shape): `{ |x| x + 1 }`, `{ |x: Int, y| x }`, `{ || 1 }`, `do |a| ... end`, `move { |x| x }`, `f(1) { |x| x }`, `f { |x| x }`, `xs.each do |x| ... end`, `o.m(1) { |x| x }`, `x |> f`, `x |> f(a) |> g`, `x |> o.m(1)`, a multi-line pipe; `Point { x: 1 }` still a struct literal. Commit `feat: parse blocks, trailing blocks, move, and pipes`.

### Task 4: Types for closures and function values

**Files:** `src/types/mod.rs`, `src/types/infer.rs`

**Interfaces:**
- Consumes: `ExprKind::Closure` (Task 3); `loops` (Task 2).
- Produces:
  ```rust
  pub enum CaptureMode { Shared, Mut, Reborrow, Move }
  pub struct Capture { pub name: String, pub ty: Type, pub mode: CaptureMode }
  pub struct ClosureInfo { pub name: String /* parent#cK */, pub captures: Vec<Capture>, pub is_move: bool, pub params: Vec<Type>, pub ret: Type }
  TypeInfo { ..., pub closures: HashMap<ExprId, ClosureInfo> }
  GlobalKind::Closure { parent: String }   // scheme vars = the parent's
  DotRes::MethodValue(MethodRes)           // `Shape.area`
  impl TypeInfo { pub fn contains_fn(&self, t: &Type) -> bool; pub fn may_borrow(&self, t: &Type) -> bool /* contains_ref || contains_fn */ }
  pub fn arity(t: &Type) -> usize          // top-level arrows of a (non-reference) function type
  ```

- Closure frames: `frames: Vec<Frame { base: usize /* scopes.len() at entry */, id: ExprId, is_move: bool, ret: Type, captures: Vec<Capture>, saved_loops: Vec<LoopKind> }>`. Entering a closure pushes a frame, then a scope holding the parameters (annotated or fresh). The body's value and every `return e` inside unify with the frame's `ret`, and `return` uses the innermost frame's `ret` when there is one. Leaving pops the frame and restores `loops`.
- `lookup(name)` finds the scope index `i` of the binding. Every frame with `base > i` records a capture of `name`, with mode `Move` in a `move` frame and `Shared` otherwise, unless one is already recorded. Inside a `move` frame the binding reads as immutable: the existing "not declared `mut`" check reports "cannot assign to captured `x` in a move closure" instead, and "cannot borrow captured `x` as mutable in a move closure" for `&mut`/`&mut self`.
- Mutating uses (the places that already check `mut`: assignment, compound assignment, `&mut x`, a `&mut self` receiver auto-ref) upgrade a `Shared` capture of their root variable to `Mut`. A captured variable whose type is `&mut T` is always `Reborrow`.
- Closure type: `Type::func(params, ret)`, wrapped in `&` when the frame is not `move` and has captures. Record `ClosureInfo` at frame exit. Register `GlobalKind::Closure` globals when the parent's scheme is generalized, with the parent's scheme vars and `n_params = params.len() + 1`.
- Function values: `global_var` already gives defs and variants with parameters their function types, so inference needs no change for them (the MIR rejection is removed in Task 5). `Type.name` with no arguments, where `name` is an associated function with parameters, is `DotRes::Assoc` with the function type. Where it is a method of `Type` (inherent or trait), it is `DotRes::MethodValue` with type `Fn(self_param, rest)`.
- Calls on values: `Call(f, args)` with `f` not a global name types `f`, peels one `&`/`&mut` when the result is a reference to a function type, and `apply`s. `f()` with no arguments on a function value applies one `Unit` argument.
- Escape at inference: in `adapt_arg`, when the parameter resolves to a bare function type and the argument is a non-`move` closure literal whose type is `&(...)`, report rule 3's message with the first capture's name. When the parameter is `&(A -> B)` and the argument has an owned function type and is not a place, record it in `autorefs` like other temporaries.
- `is_copy(Fn)` stays `true`.

- [ ] Tests (inferred types and errors): capture-free closure is `Int -> Int`; closure reading `x` is `&(Int -> Int)` with `x: Shared`; `total += i` gives `Mut`; `&mut T` variable gives `Reborrow`; `move` closure is owned with `Move`; nested closure captures through its parent; assigning a move capture errors with the message; `return 1` in a block types against the block; `break` in a block outside a loop errors; `Shape.area` is `&Shape -> Float`; `Point.new` is a function value; `Some` is `T -> Option[T]`; `f()` on `Unit -> Int`; passing a borrowing closure literal to `f: Int -> Int` errors; `contains_fn` on a struct with a function field. Commit `feat: closure and function value types with capture inference`.

### Task 5: Lowering closures, function values, and partial application

**Files:** `src/mir.rs`

**Interfaces:**
- Consumes: `TypeInfo.closures`, `DotRes::MethodValue`, `arity`.
- Produces: `Rvalue::MakeFn { code: FnCode, env: Vec<Operand>, alloc: Alloc }`, `enum FnCode { Closure { name: String, targs: Vec<Type> }, Global(Callee), Variant(Type, usize) }`, `enum Alloc { Static, Stack, Heap }`, `Callee::Value(Operand)`, `Body.captures: Vec<String>`. `lower` returns closure bodies alongside the others. Dump syntax: `make_fn closure main#c1 [_7] stack`, `call value _8(_2)`.

- Closure literal: for each capture, build the env operand. `Shared`/`Mut` give `Ref(false/true, place)`, `Reborrow` gives `Ref(true, (*x))`, and `Move` gives `Use(place)`, which moves or copies. Then `t = MakeFn { Closure { name, targs: parent's generics as Params }, env, alloc }`. For a borrowing closure the literal's value is `&t` (`eval_to_temp(Ref(false, t))`); otherwise it is `t`.
- Closure body lowering: a new `Lowerer` for the same parent context, with `_1: &Tuple[field types]` where field types are `&T`, `&mut T`, `&mut T`, `T` per mode (`&Unit` for no captures). The declared params follow, and `captured: HashMap<String, Place>` maps a captured name to `(*_1).k` for `Move` and `*((*_1).k)` otherwise. `lookup` falls back to `captured`. `return` in the body returns from the closure body. The loop stack starts empty.
- Function values: `Var(n)` for a def with parameters is `MakeFn { Global(callee), [], Static }`; for a variant with fields it is `MakeFn { Variant(ty, idx), [], Static }`. `DotRes::Assoc` with no arguments and `DotRes::MethodValue` are `MakeFn { Global(..), [], Static }`.
- Partial application of a global: `k < n_params` arguments (calls, variants, associated functions, and method calls with too few arguments) give `MakeFn { Global(callee) or Variant, args, Heap }`. Receiver adjustments and argument autoborrows apply to the bound arguments as in a full call.
- Over-application: `k > n_params` calls with the first `n_params` arguments, then `Call(Callee::Value(result), rest)`. Remove the three "not supported in this version" errors and the `partial_application_rejected_for_now` test.
- Value calls: `Call(f, args)` where `f` is not a global name lowers `f` to an operand (the reference itself when `f: &(...)`), then `Call(Callee::Value(op), args)`. `f()` on a function value passes `Const::Unit`.

- [ ] Tests (dump): borrowing closure makes a stack `make_fn` and a `&` temp; `move` closure moves a `String` capture into a heap env; closure body reads `*((*_1).0)`; `add(1)` is a heap `make_fn` with one bound arg; `add` alone is static; `Some` alone is a static variant; `adder(1)(2)` calls then `call value`; `f(1)` on a local is `call value`; nested closure's body builds its own `make_fn` from `_1` places. Commit `feat: lower closures, function values, and partial application`.

### Task 6: Ownership and borrow checking of closures

**Files:** `src/ownck.rs`, `src/borrowck.rs`

**Interfaces:**
- Consumes: `MakeFn`, `Callee::Value`, `Body.captures`, `may_borrow`.

- ownck: `MakeFn` env operands are uses like `Aggregate` operands, so `Move` captures move the variable. A move out of a place rooted at a closure body's `_1` reports rule 2's message, with the capture name taken from `Body.captures`. `describe_place` renders `(*_1).k` and `*((*_1).k)` in closure bodies as the capture's name.
- borrowck:
  - Tracked locals are those whose type `may_borrow`, not only `contains_ref`. Parameters whose type `contains_ref` get entry loans as before, and `_1` of a closure body gets one too.
  - `loans(MakeFn)` is the union over its env operands, like `Aggregate`.
  - `Callee::Value` calls: the result gets the loans of the callee operand and of every argument. The liveness `uses` include the callee operand.
  - Owned-function argument rule (default 3): at every `Call` whose callee is a `Def`, `Trait`, `Value`, or `Gc::new`, take each parameter's type (the callee's scheme instantiated with the call's type arguments, or the value's type). If it `contains_fn` outside a `&`/`&mut` and the argument holds any loan, report the rule 3 message naming the loan's place, with the "`x` is borrowed here" note (an entry loan names the parameter and has no note).
  - Return rule: when the function has no elided parameter and the returned value holds an entry loan, the message is "cannot return a value that borrows `s`; return an owned value instead". In a closure body, an entry loan of `_1` in the returned value is "cannot return a reference to a captured variable". Closure bodies take their elided parameter from the declared parameters (never `_1`). A returned reference with two candidate parameters is the elision error at the closure literal.
  - A borrowing closure's loans on its captures live while the `&` temp (or any copy of the function value) is live. This is the existing holds and liveness logic, so `let f = { || total += 1 }; puts(total); f()` is "cannot use `total` because it is mutably borrowed".

- [ ] Tests, each a small program checked for acceptance or its exact message:
  - accepted: a closure mutating `total` then reading `total` after the closure's last use; a block passed to `f: &(Int -> Unit)` in a loop; a `move` closure returned from a function; a partial application with an owned argument returned; a closure that returns a borrow of its one reference parameter;
  - rejected: reading `total` while a mutating closure is live; `Gc.new(*f)` for a borrowing `f`; passing `*f` to `g: Int -> Int`; returning a borrowing closure (the local capture "does not live long enough"); returning `add_ref(&s)` for a parameter `s` (return rule); moving a captured `String` out; a closure returning `&captured`.

  Commit `feat: ownership and borrow checking for closures`.

### Task 7: Code generation for function values

**Files:** `src/mono.rs`, `src/cgen.rs`, `runtime/rush_rt.c`, `runtime/rush_rt.h`

**Interfaces:**
- Consumes: everything above.
- Produces: `typedef struct rush_fn { void *code; } rush_fn;` in the runtime header; `c_type(Fn)` is `rush_fn *`.

- mono: `FnCode::Closure { name, targs }` requests the closure body instance like a `Def`. `FnCode::Global(callee)` goes through `callee`. Types in `MakeFn`, `Variant`, and `Callee::Value` are substituted.
- cgen, per `MakeFn` site in an instantiated body (site id `<body>_<n>`):
  - `struct rush_env_<site> { void *code; <c_type(Tuple[env types])> env; };`. The environment is the existing tuple struct, so a closure body's `_1: &Tuple[..]` is a plain pointer to the `env` member, and the environment's drop glue is the tuple's;
  - entry `static R rush_entry_<site>(rush_fn *self, A1 a1, .., An an)`, where `n = arity(site type)`. The body casts `self` to the env struct. A closure target is called as `body(&e->env, a1..am)`. A global or variant target gets the bound values `e->env.f0..` followed by `a1..am`, where `m` is the target's remaining parameters or fields. If `n > m`, the result is called as a value with `a(m+1)..an`;
  - `Static`: a file-scope `static struct rush_env_<site> rush_obj_<site> = { rush_entry_<site> };` and `target = (rush_fn *)&rush_obj_<site>;`
  - `Stack`: a C local `struct rush_env_<site> env<n>;` declared with the function's locals; fill it, then `target = (rush_fn *)&env<n>;`
  - `Heap`: `rush_gc_alloc(sizeof(struct rush_env_<site>), drop)`, where `drop` is a generated `rush_drop_env_<site>(void *p)` that runs the tuple's drop glue on `&((struct rush_env_<site> *)p)->env`, or `NULL` when the tuple needs none.
- Names: `mangle_fn` maps the `#` in closure body names (`main#c1`) to `_c`, so the C name is `rush_main_c1`.
- Value call `Call(Value(f), args)` with the concrete type of `f` (`&` peeled: load `*f`) and `n = arity`:
  - `k == n`: `target = ((R (*)(rush_fn *, A1..An))f->code)(f, a1..an);`
  - `k < n`: a heap partial application site with env `{ code, rush_fn *g, a1..ak }` and an entry that calls `g` with the bound values and the remaining parameters.
- Symbols from Task 1 and every existing path are unchanged.

- [ ] Tests: cgen unit test that a static function value emits no allocation; C compiles for a stack closure, a heap closure with a `String` field and its drop function, a partial application of a value, and an over-application. Run the Task 5 and 6 example programs end to end. Commit `feat: C code for closures, function values, and partial application`.

### Task 8: Golden and error programs

- `tests/programs/closures.rush`: the language-rules example (without the non-Rush line and the commented errors), with expected output written from the rules before running.
- `tests/programs/fn_values.rush`: defs, variant constructors, associated functions, and methods as values; partial application of each; over-application; `|>` chains mixing names, calls, and methods; a generic `def apply[T, R](f: &(T -> R), x: T) -> R` used with a closure and with a named function; a closure returning a closure (`move`), called with two arguments at once.
- `tests/programs/control.rush`: `loop` with `break e`, `next` in `for` and `while`, inclusive and exclusive ranges, a range printed, symbols in `case` and interpolation, a `return` from inside a block.
- `tests/programs/closure_drop.rush`: a `Drop` value captured by `move` is dropped once, when the environment is collected (`gc_collect_now` after the last use); a `Drop` value borrowed by a stack closure is dropped at its own scope end.
- Error programs, one each: `closure_escape` (borrowing closure to an owned parameter), `closure_returned` (returning a borrowing closure), `move_capture_assign`, `move_out_of_capture`, `closure_borrow_conflict`, `break_outside_loop`, `for_not_range`, `borrowed_fn_into_gc`.
- All Plan 1, 2, 3a, and 3b programs still pass.

- [ ] Commit `feat: closure and control flow golden and error programs`.

### Task 9: Docs and PR

- [ ] README: add a short closures example (`each_to` with a block, `adder`, `|>`). Spec: split the plan table's row 4 into 4a (shipped) and 4b; add the owner decisions and the defaults to the decision table once approved; update section 2's closure paragraph to name `A -> B` versus `&(A -> B)`, and add to known corners: `for` over ranges only until Plan 5, no call-once closures, `move` captures are read-only.
- [ ] `cargo build --release`, all programs, `git status` clean, push `plan4a`, PR against `plan3b`.

---

## Self-review against the spec

- **Covered:** closures and blocks with both syntaxes and trailing position; `move`; capture by shared or mutable reference as the body needs; escape errors for non-`move` closures; stack environments for closures passed as arguments and GC environments for `move` closures; every function curried with full application as one C call and partial application allocating; partial applications carrying borrows are checked as borrows; `|>`; `loop`, `break e`, `next`, `for`, ranges, symbols.
- **Not covered, by design:** `?`, `>>=`, `mdo`, higher-kinded traits (Plan 4b); `for` over iterators, `each`/`map` on collections (Plan 5); command-call syntax (spec: never in Stage 1).
- **Differs from the spec's wording:** the spec allocates a `move` closure on the stack when it is passed directly and not stored. This plan puts every `move` environment with captures on the GC heap, because an owned `A -> B` is `Copy` and may be stored by the callee. Escape analysis can bring the stack case back later.
- **Owner review points:** the ten defaults at the top.
