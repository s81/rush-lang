# Rush Plan 3a: Ownership, Drops, and the GC Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Values are owned and moved; use after move is a compile error; heap-owning values (`String`, structs and enums containing them) are freed deterministically by compiler-inserted drops; `Copy`, `Clone`, `Show`, `Eq` can be derived; references are real pointers in the generated C with Rust-style auto-ref on receivers and auto-deref of `Copy` values; `Gc[T]` moves a value onto a conservative mark-sweep heap in the C runtime.

**Architecture:** References become a type constructor (`&T`, `&mut T`) with pointer codegen, but their *lifetimes and conflicts are not checked in this plan*; that is Plan 3b. Plan 3a adds a move-and-drop dataflow pass over the MIR (`ownck.rs`), drop-glue generation in cgen, a derive expander that synthesizes Rush source for impls, associated functions (`Type.name`), `Gc` intrinsics, and the collector in `rush_rt.c`.

**Tech Stack:** Rust 1.98, no crates. C99 with `setjmp.h` for register spilling. `tcc` on Windows.

**Spec:** `docs/superpowers/specs/2026-09-17-rush-stage1-design.md`

**Decisions taken for this plan with the owner (2026-09-17):**
- Plan 3 is split: 3a is this document; 3b adds NLL borrow checking, lifetime elision rules, references in fields and return types, and runtime exclusivity for `Gc` borrows.
- `Gc.new(v)`; this introduces associated functions `Type.name(args)` in general.
- Copies of heap-owning values are explicit through `Clone`; use after move is an error.
- Call sites borrow named variables explicitly with `&x`; method receivers auto-borrow.

**Adjustments proposed by the implementer, for owner review:**
1. Temporaries auto-borrow: an rvalue argument (literal, interpolation, call result, aggregate literal) passed to a `&T` parameter is borrowed implicitly. A named variable is not: `puts(s)` errors with "expected `&String`, found `String`; write `&s`".
2. `+` and `==` on strings borrow both operands (auto-ref, never move), so `s + "x"` and `a == b` never consume `s`, `a`, or `b`. `Eq::eq` therefore takes `other: &Self`.
3. Match ergonomics: `case` on a `&T` scrutinee matches through the reference and binds fields by reference. Combined with auto-deref of `Copy` values, `in Circle(r) then r * r` works with `r: &Float`.
4. Drops happen at function exit and on reassignment, not at inner scope exit. Memory is reclaimed a little later than Rust would; observable only through user `Drop` impls, which run late. Scope-exit drops are a Plan 3b/5 refinement noted with a `ponytail:` comment.
5. `Gc.borrow` and `Gc.borrow_mut` return raw payload pointers without the runtime exclusivity flag until 3b knows when a borrow ends.
6. String literals are owned `String` values backed by static storage (capacity 0, so dropping is a no-op). `let s = "abc"` owns `s`.

## Language rules added by this plan

```ruby
struct Person
  derive Show, Eq, Clone
  name: String
  age: Int
end

struct Point
  derive Copy, Show
  x: Float
  y: Float
end

impl Person
  def birthday(&mut self)
    @age += 1
  end
  def greet(&self) -> String
    "hi #{@name}"
  end
  def anonymous(age: Int) -> Person
    Person { name: "anon", age: age }
  end
end

impl Drop for Person
  def drop(&mut self)
    puts("bye #{@name}")
  end
end

def shout(p: &Person) -> String
  p.greet + "!"
end

def main
  let mut p = Person { name: "Ann", age: 30 }
  p.birthday
  puts(shout(&p))
  let q = p.clone
  let r = p            # p moved into r
  # puts(p.greet)      # error: use of moved value `p`
  let shared = Gc.new(Person.anonymous(5))
  puts(shared.borrow.greet)
  let pt = Point { x: 1.0, y: 2.0 }
  let pt2 = pt          # Copy, pt still usable
  puts("#{pt} #{pt2} #{q == r}")
end
```

- **Types.** `&T` and `&mut T` are types (`Type::Con("&", [T])`, `Type::Con("&mut", [T])`). In this plan they may appear in parameter types, `self`, `let` bindings, and expression types, but not in struct or enum fields or return types (error: "references in this position are not supported until Plan 3b"), except the `Gc` intrinsics.
- **Copy.** `Int`, `Float`, `Bool`, `Unit`, `&T`, `&mut T` (this plan only), `Gc[T]`, tuples of `Copy`, and user types with `derive Copy` (all fields must be `Copy`: "cannot derive `Copy` for `Person`: field `name` is not `Copy`"). Everything else moves.
- **Moves.** Using a whole local of a non-`Copy` type as a value moves it. A later read is "use of moved value `x`" pointing at the read, with a note "value moved here" as a second line. Moving out of a field, a tuple element, or through a reference is "cannot move out of `p.name`; use `.clone`". Assigning to a moved local re-initializes it.
- **Explicit borrows.** `&x` and `&mut x` are expressions of type `&T` / `&mut T`. `&mut x` requires `x` to be `let mut`. `*r` reads through a reference. `&` of an rvalue borrows a temporary.
- **Auto-ref/deref.** A method with `&self`/`&mut self` auto-borrows its receiver; `&mut self` requires a mutable place. Field access and method calls through `&T` auto-deref. A value of type `&T` where `T: Copy` is implicitly copied out where a `T` is expected (operands, arguments, assignments, returns, struct fields). A non-`Copy` `&T` where `T` is expected errors: "expected `Person`, found `&Person`; use `.clone`".
- **Operators.** `+` on strings and `==`/`!=` on any type borrow both operands. Arithmetic and comparison on `&Int` etc. auto-deref.
- **Drops.** Locals holding non-`Copy` values are dropped at function exit if still owned, and before reassignment. Each such local gets a drop flag. `String` frees its buffer when its capacity is non-zero. A user `impl Drop for T` runs before fields are dropped. Externs that take `String` by value take ownership (none in the prelude do; IO takes `&String`).
- **Clone.** `trait Clone` with `def clone(&self) -> Self`. `derive Clone` is field-wise. Prelude provides `Clone` for primitives, `String`, `Option[T: Clone]`, and `Copy` types get `Clone` from `derive Copy` (which implies `Clone`).
- **Derive.** `derive A, B` as the first line of a `struct` or `enum` body. Supported: `Copy`, `Clone`, `Show`, `Eq`. `Show` prints `Person { name: "Ann", age: 30 }` for structs, `Circle(1.0)` / `Rect { w: 1.0, h: 2.0 }` / `Empty` for variants; a `String` field prints quoted inside a derived `Show` (via a prelude `Show` helper `show_str`), not when printed directly. `Eq` is field-wise. Generic types derive with bounds on every parameter (`impl[A: Show, B: Show] Show for Pair[A, B]`).
- **Associated functions.** A `def` inside an `impl` without `self` is called as `Type.name(args)`. `Gc.new(v)` is one. Variants and associated functions live in different namespaces; `Type.name` looks up only impls.
- **Gc.** `Gc[T]` is a built-in type. `Gc.new(v)` moves `v` to the collected heap and returns a `Copy` handle. `g.borrow` returns `&T`, `g.borrow_mut` returns `&mut T`. The payload's drop glue runs when the collector frees the object.
- **Integer overflow.** With `--debug`, `+ - *` on `Int` panic on overflow; without it they wrap.
- **Prelude signature changes.** `puts(s: &String)`, `print(s: &String)`, `str_concat(a: &String, b: &String) -> String`, `Eq::eq(&self, other: &Self)`, `Show::to_s(&self) -> String` returns an owned string (for `String` it clones).

## File structure

| File | Change |
|---|---|
| `src/ast.rs` | `ExprKind::Ref(bool, Box<Expr>)`, `ExprKind::Deref`, `ExprKind::Path { ty, name }`, `derives: Vec<String>` on `StructDef`/`EnumDef` |
| `src/parser.rs` | Stop erasing `&`/`*`; parse `derive` lines and `Type.name` |
| `src/derive.rs` | New: expands `derive` into impl items by synthesizing and parsing Rush source, then re-spanning to the derive line |
| `src/types/mod.rs` | Reference constructors, `is_copy`, `Adjust`, `TypeInfo.adjust`, `TypeInfo.derefs`, `ImplInfo.assoc`, `GlobalKind::Intrinsic` |
| `src/types/decls.rs` | Reference position checks, `Gc` intrinsics and impl, associated functions, `derive Copy` field check |
| `src/types/infer.rs` | Coercions, auto-ref/deref, match ergonomics, `Path`, `Ref`/`Deref`, impl lookup through references |
| `src/types/exhaust.rs` | Peel references from the scrutinee type |
| `src/mir.rs` | `Proj::Deref`, `Rvalue::Ref`, `Statement::Drop`, spans on statements, adjustments applied during lowering |
| `src/ownck.rs` | New: move checking and drop insertion with drop flags |
| `src/mono.rs` | Intrinsics pass through; request `Drop` impls for droppable types |
| `src/cgen.rs` | Pointer types, `&`/`*`, drop glue, intrinsics, debug arithmetic |
| `runtime/rush_rt.c`, `.h` | Owned strings with capacity, `rush_str_drop`, `rush_str_clone`, checked arithmetic, the collector |
| `std/prelude.rush` | `Clone`, `Copy`, `Drop`, `Gc` declarations, updated signatures, `show_str` |
| `src/driver.rs` | Run `derive::expand` and `ownck` in the pipeline; pass `--debug` to cgen |
| `tests/programs/*.rush` | `ownership`, `derive`, `gc`, `drop`, `refs` |
| `tests/errors/*.rush` | `use_after_move`, `move_out_of_field`, `borrow_named`, `derive_copy`, `ref_in_field`, `mut_borrow_immutable` |

---

### Task 1: References and `derive` in the AST and parser

**Files:** `src/ast.rs`, `src/parser.rs`

**Interfaces produced:**
```rust
// ast.rs additions
ExprKind::Ref(bool, Box<Expr>)        // &e / &mut e
ExprKind::Deref(Box<Expr>)            // *e
ExprKind::Path { ty: String, name: String }   // Gc.new, Person.anonymous (value; Call applies it)
pub struct StructDef { ..., pub derives: Vec<String> }
pub struct EnumDef { ..., pub derives: Vec<String> }
```
- Parser: `unary` produces `Ref`/`Deref` instead of erasing. `derive` is a keyword; `derive A, B` newline is accepted only as the first line of a struct or enum body. In `primary`, a CamelCase identifier followed by `.` and a lowercase identifier becomes `Path` (the postfix loop then handles `(args)`); CamelCase followed by `{` stays a struct literal.
- Existing tests `refs_are_erased` becomes `refs_parse`; add tests for `derive` and `Path`.

- [ ] Write failing parser tests, implement, `cargo test` green, commit `feat: parse references, derive lines, and Type.name paths`.

---

### Task 2: Derive expansion

**Files:** `src/derive.rs`, `src/driver.rs`

**Interface:** `pub fn expand(prog: &mut Program, next_id: &mut ExprId) -> Result<(), Diagnostic>`. Runs after parsing the prelude and user file, before `types::check`.

**Algorithm:** for each struct/enum with derives, build Rush source per derive and parse it with `parser::parse`, then walk the resulting items setting every `Span` to the span of the derive line (a `respan` visitor over items, defs, blocks, statements, expressions, patterns, type expressions), and append them to `prog.items`. Unknown derive name → "cannot derive `Foo`; supported: Copy, Clone, Show, Eq".

Generated shapes (with `G` the generics list and bounds `[A: Trait, B: Trait]`):

- `Show` struct: `impl[..] Show for Name[..]` / `def to_s(&self)` / `"Name { f1: #{show_str(&@f1)}... }"` where the helper `show_str` (prelude) is `def show_str[T: Show](x: &T) -> String` returning `x.to_s` and the derived code for a field of declared type `String` uses `"\"#{@f}\""` instead. Unit-like structs (no fields) print `Name`.
- `Show` enum: `case self` with one arm per variant: unit `in V then "V"`, tuple `in V(a0, a1) then "V(#{a0}, #{a1})"`, named `in V { f: a0 } then "V { f: #{a0} }"`.
- `Eq` struct: `def eq(&self, other: &Name[..])` body `@f1 == other.f1 and ...` (`true` for no fields).
- `Eq` enum: `case (self, other)` arms `in (V(a0), V(b0)) then a0 == b0`, `in (V, V) then true`, final `in (_, _) then false` (omitted when the enum has one variant).
- `Clone` struct: `Name { f: @f.clone, ... }`; enum: per-variant rebuild with `.clone` on each field.
- `Copy`: `impl[..] Copy for Name[..]` with an empty body, plus a `Clone` impl whose `clone` returns `*self` (a copy). `Copy` on a type whose field types are not all `Copy` is rejected in decls (Task 4), not here.

- [ ] Tests in `derive.rs`: generated item count and names for a struct and an enum; respan makes every span equal the derive line; unknown derive error. Commit `feat: derive expansion for Copy, Clone, Show, Eq`.

---

### Task 3: Runtime: owned strings, checked arithmetic, the collector

**Files:** `runtime/rush_rt.h`, `runtime/rush_rt.c`

**Header additions:**
```c
typedef struct { uint8_t *ptr; size_t len; size_t cap; } rush_str;   /* cap == 0: static or borrowed, never freed */
void rush_str_drop(rush_str *s);
rush_str rush_str_clone(const rush_str *s);
rush_str rush_str_concat(const rush_str *a, const rush_str *b);
bool rush_str_eq(const rush_str *a, const rush_str *b);
rush_unit rush_puts(const rush_str *s);
rush_unit rush_print(const rush_str *s);
int64_t rush_add_i64_checked(int64_t a, int64_t b);   /* and sub, mul */
typedef void (*rush_drop_fn)(void *);
void *rush_gc_alloc(size_t size, rush_drop_fn drop);
void rush_gc_collect(void);
```
`rush_str_lit` keeps `cap = 0`. `rush_int_to_s` and friends return `cap = len`.

**Collector:** every object is `struct rush_gc_hdr { size_t size; rush_drop_fn drop; struct rush_gc_hdr *next; uint8_t mark; uint8_t pad[7]; }` followed by the payload. `rush_rt_init` records the address of a local as the stack base and sets the threshold to 1 MiB. `rush_gc_alloc` collects first when `bytes_since_gc > threshold`, then mallocs. Collection: `setjmp` into a local `jmp_buf` (spills registers), scan from the current stack pointer (address of a local) to the base, word by word, aligned; for each word check whether it points inside any object (binary search over a sorted array of object ranges rebuilt at the start of collection); mark and push on an explicit mark stack; pop and scan payloads the same way. Sweep: unlink, call `drop` if non-null, `free`. New threshold: `max(1 MiB, 2 * live_bytes)`. `rush_gc_collect` is exported for tests via `extern "C" def gc_collect() -> Unit`, plus `gc_live_objects() -> Int` for the golden test.

- [ ] Write `runtime/gc_test.c` (compiled and run by a Rust integration test with the found C compiler) that allocates 100 000 objects, keeps 10 on the stack, collects, and asserts live count 10 and that drop fns ran 99 990 times. Commit `feat: owned strings, checked arithmetic, conservative mark-sweep GC`.

---

### Task 4: Types for references, Copy, adjustments, intrinsics, associated functions

**Files:** `src/types/mod.rs`, `src/types/decls.rs`, `src/types/infer.rs`, `src/types/exhaust.rs`, `std/prelude.rush`

**Interfaces produced:**
```rust
impl Type { pub fn r#ref(mutable: bool, t: Type) -> Type; pub fn as_ref(&self) -> Option<(bool, &Type)>; pub fn peel(&self) -> &Type; }
pub enum Adjust { AutoRef(bool), AutoDeref }         // recorded on the receiver expr id
pub struct TypeInfo { ..., pub adjust: HashMap<ExprId, Adjust>, pub derefs: HashSet<ExprId>, pub is_copy_cache: .. }
pub fn is_copy(info: &TypeInfo, bounds: &.., t: &Type) -> bool
pub struct ImplInfo { ..., pub assoc: HashMap<String, String> }   // associated function name -> global
GlobalKind::Intrinsic
```
- `from_ast` converts `Ref`. decls rejects references in field and return positions (except intrinsics) and `Self` inside `derive`d code is fine.
- decls registers `Gc`: arity 1 in `adts`, an inherent `ImplInfo { generics: [T], self_ty: Gc[T], methods: { borrow: "Gc::borrow", borrow_mut: "Gc::borrow_mut" }, assoc: { new: "Gc::new" } }`, and the three globals with `GlobalKind::Intrinsic` and schemes `T -> Gc[T]`, `&Gc[T] -> &T`, `&Gc[T] -> &mut T`.
- decls registers associated functions from impl defs without `self` under `ImplInfo.assoc` with globals named like methods; `derive Copy` checks all fields (after generic substitution with the impl's params treated as `Copy` by bound) are `Copy`.
- infer:
  - `Ref(m, e)`: type `&T`; `&mut` requires the operand to be a mutable place (`assign_target` logic reused for the mutability check). `Deref(e)`: `e` must be `&T`/`&mut T`, type `T`.
  - `Path { ty, name }`: inherent impls for `ty` with `assoc[name]` → instantiate like a global (record insts). Else "no associated function `name` on `Ty`".
  - Coercion `fn coerce(&mut self, e: &Expr, found: &Type, expected: &Type) -> Type`: if `found` is a reference to `T`, `expected` is not a reference (after resolve), and `T` is `Copy` → record `derefs.insert(e.id)`, return `T`. If `T` is not `Copy` and `expected` is a concrete non-reference type that unifies with `T` → error "expected `T`, found `&T`; use `.clone`". Otherwise return `found`. Applied in `apply` (arguments), binary operands, assignment values, `return`, struct literal fields, `if`/`while` conditions.
  - Binary `Add` on strings and `Eq`/`Ne`: operands are typed by peeling references; MIR borrows them.
  - `dot`: peel the receiver type for field and method lookup, recording `Adjust::AutoDeref` on the receiver when it is a reference and the field is read or the method takes `self`/`&self` by matching the method's declared `self_param`; record `Adjust::AutoRef(mutable)` when the receiver is a value and the method takes `&self`/`&mut self`; `&mut self` on an immutable named place errors "cannot borrow `x` as mutable; it is not declared `mut`".
  - Trait resolution through references: `find_impl(trait, &T)` falls back to `T` when no impl matches `&T`; the resulting call passes the reference itself as `self` when the method takes `&self`.
  - `check_pat`: when `expected` is a reference and the pattern is not `Wild`/`Bind`, check against the pointee with `by_ref = true`; bindings under `by_ref` get type `&FieldType` (or `&mut` for `&mut` scrutinees). `pat_types` stores the peeled type; a new `pat_by_ref: HashSet<PatId>` marks reference bindings for MIR.
  - Arguments to `&T` parameters: a named place (`Var`, field chain, tuple index) of type `T` errors "expected `&T`, found `T`; write `&x`"; an rvalue of type `T` is auto-borrowed (`derefs` counterpart: `autorefs: HashSet<ExprId>`).
- exhaust: `check_case` peels the scrutinee type.
- prelude: `trait Clone`, `trait Copy: Clone`, `trait Drop def drop(&mut self) -> Unit end`, `Clone`/`Copy` impls for `Int`, `Float`, `Bool`, `Unit`; `Clone` for `String` via `extern "C" def str_clone(s: &String) -> String`; `impl[T: Clone] Clone for Option[T]`; `impl[T] Copy for Gc[T]` and its `Clone`; `Eq::eq(&self, other: &Self)`; IO takes `&String`; `Show for String` clones; `show_str`.

- [ ] Tests: reference types display; `Copy` decisions for tuples, Gc, derived types; coercion of `&Int` in arithmetic; `.clone` error for `&String` where `String` expected; auto-ref/deref adjustments recorded for `p.greet`, `r.greet` with `r: &Person`, `p.birthday` on immutable `p` errors; `Path` resolution and `Gc.new` typing `Gc[Int]`; `g.borrow` typing `&Int`; match ergonomics binding `&Float`; `&s` required for named args; rvalue auto-borrow accepted; references in fields rejected; derive Copy on a String field rejected. Commit `feat: reference types, Copy, coercions, intrinsics, associated functions`.

---

### Task 5: MIR: derefs, refs, spans; ownership checking and drop insertion

**Files:** `src/mir.rs`, `src/ownck.rs`, `src/driver.rs`

**MIR changes:** `Proj::Deref`; `Rvalue::Ref(bool, Place)`; `Statement::Assign(Place, Rvalue, Span)` and `Statement::Drop(Place, Span)`; `Body.droppable: Vec<LocalId>` filled by ownck; lowering applies `adjust`, `derefs`, `autorefs`, and `pat_by_ref`; `Path` lowers like a global call; intrinsic calls are `Callee::Def { name: "Gc::new", targs }`; string `+`, `==`, interpolation parts, and trait `&self` arguments borrow places (temps for rvalues).

**ownck algorithm** (`pub fn check_and_insert_drops(bodies: &mut [Body], info: &TypeInfo) -> Result<(), Diagnostic>`), per body:
1. Determine droppable locals: non-`Copy` type (with the body's generic bounds: a `Param` is droppable unless bounded by `Copy`). Parameters count as initialized on entry.
2. Forward dataflow over blocks with state = set of maybe-moved locals and set of maybe-initialized locals (bit sets). Transfer per statement: reading a local operand while maybe-moved → error "use of moved value `x`" at the statement span (plus "value moved here" line from the recorded move span). A move is an `Operand::Place` with an empty projection of droppable type used in `Use`, `Call` args, `Aggregate`, or assignment to `_0`. A place with projections of droppable type in those positions → "cannot move out of `p.f`; use `.clone`" (through `Deref` → "cannot move out of a reference"). `Rvalue::Ref` and `Discriminant` and `Binary` operands are reads, not moves. Assignment to a local marks it initialized and not moved.
3. Drop insertion: for each droppable local `x` add a `Bool` flag local `x_live`, `false` at entry (parameters `true`). After `x = ...`: if `x` may already be live at that point, emit `Drop(x)` guarded by the flag before the assignment; then `x_live = true`. After a move of `x`: `x_live = false`. Before every `Return`: for every droppable local (except `_0`), `if x_live then Drop(x)`. Guards are emitted as `If(x_live, drop_bb, cont_bb)` block splits. Unconditionally-live locals skip the flag (flag optimization: a local never moved and assigned exactly once dominating the return can be dropped unconditionally; keep simple: always use flags, note `ponytail:`).
4. `_0` (return slot) is never dropped by the callee.
Runs after `lower`, before `mono`, on generic MIR.

- [ ] Tests (dump-based): move sets flag false and use-after-move errors; conditional move keeps flag; reassignment drops old value; parameters dropped at exit; `Copy` locals untouched; moving out of a field errors; `&x` does not move. Commit `feat: MIR references and ownership checking with drop flags`.

---

### Task 6: Codegen for references, drops, intrinsics; mono for Drop impls

**Files:** `src/cgen.rs`, `src/mono.rs`, `src/driver.rs`

- `c_type(&T)` → `const rush_T*` is avoided (casts get noisy): both `&T` and `&mut T` map to `rush_T*`; immutability is enforced by the checker, not C.
- Place with `Deref` → `(*expr)`; `Rvalue::Ref` → `&expr`; a `Ref` of a constant operand never occurs (MIR materializes temps).
- `Statement::Drop(place)` → `rush_drop_<mangled>(&place);` Drop glue: for each droppable concrete type seen in bodies, emit `static void rush_drop_T(T *v)`: `String` → `rush_str_drop(v)`; struct/tuple → drop droppable fields; enum → `switch (v->tag)`; user `Drop` impl → call `rush_Drop_N_drop__T(v)` first (mono requests these impls for every droppable ADT type reachable from bodies, including through fields).
- Intrinsics inside `Assign`: `Gc::new` → `{ T *p = rush_gc_alloc(sizeof(T), drop_or_null); *p = v; target = p; }`; `Gc::borrow`/`borrow_mut` → `target = g;` (the handle already is the payload pointer).
- `c_type(Gc[T])` → `rush_T*`.
- Debug arithmetic: `gen(bodies, info, debug: bool)`; `Int` `+ - *` emit `rush_add_i64_checked` etc. when `debug`.
- Extern signatures for `&String` params: `const rush_str *`; cgen passes `&temp`/`&place` as the MIR says.

- [ ] Tests: drop glue emitted for `Person` and `Option[String]`, `switch` for enums; `&`/`*` emission; `Gc::new` expansion; debug flag switches arithmetic. Commit `feat: codegen for references, drop glue, Gc intrinsics, debug overflow checks`.

---

### Task 7: Golden and error programs

`tests/programs/ownership.rush` (expected output in comments):

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
  def greet(&self) -> String
    "hi #{@name}"
  end
  def anonymous(age: Int) -> Person
    Person { name: "anon", age: age }
  end
end

def shout(p: &Person) -> String
  p.greet + "!"
end

def main
  let mut p = Person { name: "Ann", age: 30 }
  p.birthday
  puts(shout(&p))                 # hi Ann!
  let q = p.clone
  let r = p
  puts("#{q == r} #{q}")          # true Person { name: "Ann", age: 31 }
  puts(Person.anonymous(5).greet) # hi anon
end
```

`tests/programs/drop.rush`: a struct with `impl Drop` printing its name; three locals, one moved into a function that lets it go out of scope, one reassigned, one conditionally moved. Expected order verifies: callee drops its parameter at its return, reassignment drops the old value immediately, conditional move drops exactly once.

`tests/programs/gc.rush`: allocates 200 000 `Gc.new(Person { .. })` in a loop keeping only the last, calls `gc_collect`, prints `gc_live_objects` (expected `1` plus whatever the loop variable holds, settled when the test is written) and the survivor's name.

`tests/programs/refs.rush`: `case` on `&Shape` with `r * r`, auto-deref field reads, `*r` explicit deref, `&mut` method on a `let mut` struct, `Copy` struct used after assignment.

`tests/programs/derive.rush`: derived `Show` for a generic struct and an enum with all three variant shapes; derived `Eq` on both; `Copy` struct.

Error programs: `use_after_move.rush` → "use of moved value `p`"; `move_out_of_field.rush` → "cannot move out of `p.name`; use `.clone`"; `borrow_named.rush` (`puts(s)` with `s: String`) → "expected `&String`, found `String`; write `&s`"; `derive_copy.rush` → "cannot derive `Copy` for `Person`: field `name` is not `Copy`"; `ref_in_field.rush` → "references in this position are not supported until Plan 3b"; `mut_borrow_immutable.rush` → "cannot borrow `p` as mutable; it is not declared `mut`"; `clone_needed.rush` (`let s2: String = ...` from `&String`) → "expected `String`, found `&String`; use `.clone`".

- [ ] Write programs, run, fix, all Plan 1 and 2 programs still pass (their prelude calls now auto-borrow rvalues; `puts(int_to_s(x))` passes an rvalue). Commit `feat: ownership, derive, gc, drop, refs golden programs`.

---

### Task 8: Docs and PR

- [ ] README: add the `Person` example. Spec: mark Plan 3a shipped in the plan table; add the adjustments above to the decision table once the owner has approved them; add "drops at function exit" and "Gc borrows unchecked at runtime" to the known corners list until 3b.
- [ ] `cargo build --release`, run all programs, `git status` clean, push `plan3a`, PR against `plan2`.

---

## Self-review against the spec

- **Covered:** moves, `Copy`, `Clone`, `Drop`, drop insertion on every control-flow path (via flags at return and reassignment), `Gc[T]` with a small conservative mark-sweep collector, `Gc.new`, `derive`, references as real pointers with auto-ref receivers and auto-deref of `Copy`, integer overflow checks in debug builds, owned `String` freeing (closes Plan 1's `ponytail:` leak).
- **Deferred to 3b:** borrow conflicts and NLL liveness, lifetime elision for returned references, references in fields, `Gc` runtime exclusivity flag, scope-exit drops, `&mut T` non-`Copy` semantics and reborrows.
- **Owner review points:** the six adjustments listed at the top.
