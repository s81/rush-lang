# Rush Plan 3b: Borrow Checking, Scope-Exit Drops, and Gc Exclusivity

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** References are checked: at every program point a place has one live `&mut` or any number of live `&`, a place cannot be moved, assigned, or go out of scope while borrowed, and a borrow ends at its last use (NLL). Functions may return references under Rust's elision rules, and structs, enums, and tuples may hold references. Drops run at scope exit in reverse declaration order. `Gc.borrow`/`borrow_mut` panic at runtime on a conflicting borrow and release when the returned reference dies.

**Architecture:** MIR lowering gains `Statement::StorageDead` at scope and statement ends. `ownck.rs` turns those into guarded drops. A new `borrowck.rs` runs after `ownck` on generic MIR: a forward dataflow of the loans each local may hold, a backward liveness of locals, and a conflict check per statement against the loans that are live at that point. The same pass inserts the runtime releases for `Gc` borrows. With no lifetime syntax, the only inter-procedural fact is elision, which decls records per function.

**Tech Stack:** Rust 1.98, no crates. C99. `tcc` on Windows.

**Spec:** `docs/superpowers/specs/2026-09-17-rush-stage1-design.md`, section 2.

**Decisions taken for this plan with the owner (2026-09-18):**
- References in fields: a type holding references has one implicit lifetime. All of its reference fields share it. It carries the loans of every reference stored in it, cannot go into `Gc`, and counts as a reference for elision.
- `Gc` runtime borrows are released at the last use of the returned reference, as computed by the borrow checker, using flags where a path may not hold the borrow.
- Drops run at the end of the enclosing lexical scope, in reverse declaration order. Temporaries of an expression statement drop at the end of that statement. Temporaries of a `let` initializer live to the end of the enclosing scope.
- Two-phase receiver borrows: an auto-borrowed `&mut self` receiver is borrowed after the arguments are evaluated, so `p.set_age(p.age + 1)` compiles.

**Defaults following Rust, for owner review:**
1. `&mut T` is no longer `Copy`. `let r2 = r` moves `r`. Passing a `&mut` local as a call argument or receiver reborrows it (`&mut *r`) instead of moving it.
2. Loans are per place with field precision: `&mut p.a` and `&p.b` do not conflict. Enum variant fields count as fields. Indexing does not exist yet.
3. Diagnostics gain notes. Borrow errors point at the conflicting access and add a note "`x` is borrowed here" at the loan. Use after move gains the "value moved here" note that Plan 3a described but `Diagnostic` could not carry.
4. At a call, a result that carries references gets the loans of the elided argument. When the callee's declared return type has no references but the instantiated one does (a generic like `def id[T](x: T) -> T` called with `&s`), the result gets the loans of every argument whose type carries references.

## Language rules added by this plan

```ruby
struct Words
  first: &String
  rest: &String
end

impl Person
  def name_ref(&self) -> &String     # elided: tied to self
    &@name
  end
  def set_age(&mut self, a: Int)
    @age = a
  end
end

def pick(s: &String) -> Words        # elided: tied to s
  Words { first: s, rest: s }
end

def main
  let mut p = Person { name: "Ann", age: 30 }
  let n = p.name_ref
  puts(n)
  p.set_age(p.age + 1)               # ok: n is dead, receiver borrowed after args
  let r = &mut p
  # puts(&p.name)                    # error: cannot borrow `p.name` as shared because it is mutably borrowed
  r.set_age(40)
  puts(&p.name)                      # ok: r is dead
  let g = Gc.new(Person { name: "Bo", age: 1 })
  let a = g.borrow
  # let b = g.borrow_mut             # runtime panic: Gc value is already borrowed
  puts(&a.name)
  let b = g.borrow_mut               # ok: a's borrow was released after its last use
  b.age += 1
end
```

- **Borrowing types.** `contains_ref(t)`: `&T`, `&mut T`, a tuple with a component that contains a reference, or a struct or enum any of whose field types, after substitution, contains a reference. References may now appear in field types and return types. `Gc.new(v)` with `v` of a borrowing type errors "cannot store a value holding references in `Gc`".
- **Copy.** `&T` is `Copy`, `&mut T` is not. `derive Copy` on a type with a `&mut` field fails the existing field check.
- **Elision.** If a declared return type contains a reference, the output lifetime comes from the `&self`/`&mut self` receiver if present. Otherwise it comes from the single parameter whose type contains a reference. Otherwise decls reports "cannot infer the lifetime of the returned reference; return an owned value instead" at the return type. Trait method signatures follow the same rule. `GlobalInfo.elided: Option<usize>` records the parameter index (self is 0).
- **Conflicts.** At each MIR statement, every place access is checked against the loans live at the point before it:

  | Access | Conflicts with live | Message |
  |---|---|---|
  | read (copy, `Discriminant`, operand of `Binary`/`Unary`) | `&mut` loans | cannot use `x` because it is mutably borrowed |
  | shared borrow `&x` | `&mut` loans | cannot borrow `x` as shared because it is mutably borrowed |
  | mutable borrow `&mut x` | any loan | cannot borrow `x` as mutable because it is already borrowed |
  | assign `x = ...` / `x.f = ...` | any loan | cannot assign to `x` because it is borrowed |
  | move / `MoveOut` | any loan | cannot move out of `x` because it is borrowed |
  | `Drop(x)` with drop glue, `StorageDead(x)` | any loan whose place is rooted at `x` without a `Deref` | `x` does not live long enough |

  Two places overlap when one's projection list is a prefix of the other's. `x` in messages is the source path (`p.name`), rendered by a shared `describe_place` that names fields, not indexes. Every conflict carries the note "`x` is borrowed here" at the loan's span.
- **Returns.** At `Return`, `_0` is live, and every local gets an implicit `StorageDead`. So `return &local` fails with "`local` does not live long enough". A returned value holding the entry loan of a parameter other than the elided one fails with "returned reference must borrow from `s`" (the elided parameter's name).
- **Writes behind parameters.** A value assigned through a `Deref` of a local that holds a parameter's entry loan (`*out = Some(&local)`, `@items = ...` through `&mut self`) may carry only that same entry loan. Otherwise the error is "cannot store a borrowed value behind `out`; it may outlive the borrow". At a call site, the loans of every other argument flow into the place behind each `&mut` argument whose pointee contains a reference (a weak update of that loan's root local), so a generic `set(&mut o, &tmp)` ties `o` to `tmp`. This replaces the Plan 3a rejection of `&mut` parameters whose pointee holds references.
- **Scope-exit drops.** A local is dropped when its scope ends (the end of an `if`/`else`/`while`/`case` arm body or the function), in reverse declaration order, if still owned. `return` drops everything still owned, in reverse declaration order. Reassignment still drops the old value first.
- **Gc exclusivity.** The Gc header gets a borrow count: `0` free, `n > 0` shared, `-1` mutable. `g.borrow` panics with "Gc value is mutably borrowed" if the count is `-1`. `g.borrow_mut` panics with "Gc value is already borrowed" if the count is not `0`. The compiler releases each such borrow once the returned reference, and every value derived from it, is dead.

## Borrow checker algorithm (`src/borrowck.rs`)

`pub fn check(bodies: &mut [Body], info: &TypeInfo) -> Result<(), Diagnostic>` runs per body, after `ownck`, before `mono`.

1. **Loans.** Number every `Rvalue::Ref(m, place)` statement as a loan `{ place, mutable: m, span }`. Each parameter whose type contains a reference gets an entry loan `E_i` with no place. Each `Gc::borrow`/`Gc::borrow_mut` call gets a runtime loan `R_k` with no place.
2. **Holds (forward, may).** `holds[l]` is a bit set of loans that local `l` may carry. Entry: parameter `i` holds `{E_i}`. On `Assign(target, rv)`, `loans(rv)` is:
   - `Ref(_, p)`: the new loan, plus `holds[p.local]` when `p` passes through a `Deref` (reborrow);
   - `Use`/`MoveOut`/`Aggregate`: the union over the operand locals;
   - `Call`: the union over the elided argument's locals (rule 4 above), plus `R_k` for `Gc` borrows;
   - anything else: empty.
   - after a `Call`, for each argument holding a mutable loan `L` whose pointee type contains a reference: `holds[L.place.local] |= ` the loans of the other arguments.

   A whole-local target is a strong update (`holds[t] = loans(rv)`). A projected target is a weak update (`holds[t] |= loans(rv)`). Only locals whose type `contains_ref` are tracked. Merge is union.
3. **Liveness (backward, may).** A local is used by any operand or place that reads it, by `Drop(x)` when `x`'s type needs drop glue, and by `Return` for `_0`. A whole-local assignment kills it. `StorageDead` neither uses nor kills.
4. **Live loans** at a point are `⋃ holds[l]` over the locals `l` live at that point, restricted to loans with a place.
5. **Check** each statement's accesses (table above) against the live loans before it. The loan created by the statement itself is excluded. The implicit `StorageDead` of every local at `Return` is checked the same way, and so is the returned-reference rule.
6. **Gc release insertion.** For each runtime loan `R_k`, add locals `gcb_k: &T` (the payload pointer) and flag `gcb_k_held: Bool`. After the call statement, emit `gcb_k = result` and `gcb_k_held = true`. Emit a guarded release (`if gcb_k_held { gc_release(gcb_k, mutable); gcb_k_held = false }`) in three places: after each statement where `R_k` is live before and dead after; at the entry of each block where `R_k` is dead on entry but live at the exit of some predecessor; and before `Return`. The guarded-block machinery is `ownck::Emit`, moved to `mir.rs` as a shared helper.

The dataflow reuses the worklist style of `ownck.rs`. Bit sets are `Vec<u64>` words (loans per body are few).

## File structure

| File | Change |
|---|---|
| `src/diag.rs` | `Diagnostic.notes: Vec<(Span, String)>`, `with_note`; `render` prints `note:` lines with carets |
| `src/mir.rs` | `Statement::StorageDead(LocalId, Span)`; scope/statement temp ownership; two-phase receiver order; `&mut` reborrow at call arguments; `Emit` moved here; `describe_place` with field names; `dump` prints `dead(_n)` |
| `src/ownck.rs` | Drop at `StorageDead` (guarded), reverse order at `Return`, "value moved here" note, flags only for types that need drop glue |
| `src/borrowck.rs` | New: loans, holds, liveness, conflicts, return checks, Gc release insertion |
| `src/types/mod.rs` | `contains_ref`, `&mut` not `Copy`, `GlobalInfo.elided`, `GlobalKind::Intrinsic` elision for `Gc::borrow*` |
| `src/types/decls.rs` | Lift the Plan 3a position check; elision check; references allowed in fields |
| `src/types/infer.rs` | `Gc.new` of a borrowing type errors |
| `src/cgen.rs` | `StorageDead` emits nothing; `Gc::borrow*` call runtime checks; `gc_release` intrinsic |
| `runtime/rush_rt.c`, `.h` | Borrow count in the header; `rush_gc_borrow`, `rush_gc_borrow_mut`, `rush_gc_release` |
| `src/driver.rs` | Pipeline: `lower → ownck → borrowck → mono → cgen` |
| `tests/programs/*.rush` | `borrows`, `scopes`, `gc_borrow`; update `drop.out` for the new order |
| `tests/errors/*.rush` | Conflict, lifetime, elision, `Gc` storage, runtime panic cases; `ref_in_field` removed |

---

### Task 1: Diagnostics with notes

**Files:** `src/diag.rs`, `src/ownck.rs`, `src/driver.rs`, `tests/programs.rs`

- `Diagnostic { span, msg, notes: Vec<(Span, String)> }`, `Diagnostic::new` keeps its signature, `fn with_note(self, span, msg) -> Self`. `render` appends `path:line:col: note: msg` plus the source line and caret for each note.
- ownck's use-after-move adds the note "value moved here" at the recorded move span.
- The error golden files compare the full rendered output, so they now include notes. Update `use_after_move.err`.

- [ ] Tests: render with one note; use after move carries the note. Commit `feat: diagnostic notes; use after move points at the move`.

### Task 2: MIR scopes, temporaries, two-phase receivers, reborrows

**Files:** `src/mir.rs`

- `Statement::StorageDead(LocalId, Span)`, dumped as `dead(_n)`.
- The `Lowerer` tracks `scope_locals: Vec<Vec<LocalId>>`, pushed and popped with `scopes`. `new_local` and `temp` register in the innermost scope.
- Expression statements: temps created during the statement get `StorageDead` after it, in reverse order. The exception is the operand that is the block's value, which moves to the parent scope's list.
- `let`: its temps stay in the enclosing scope.
- Scope end (`block`): `StorageDead` for the scope's remaining locals, in reverse order, except the result operand's local, which moves to the parent.
- `Return(e)` emits no `StorageDead`, because the checkers treat `Return` as killing everything.
- Two-phase: in `DotRes::Method`, when the receiver's adjustment is `AutoRef(true)`, lower the receiver, then the arguments, then apply `adjusted_recv`. Other adjustments keep today's order.
- Reborrow: a call argument (or receiver without adjustment) whose operand is a place of type `&mut T` becomes `t = &mut *place` and passes `t`.
- Move `Emit` from `ownck.rs` into `mir.rs` (`pub(crate)`), and move `describe_place` here, printing field names from `TypeInfo` (`p.name`, `*r`, `t.0`).

- [ ] Tests (dump): `dead` order at scope end; tail temp not killed early; `if` arm locals die at the arm's end; two-phase order for `p.set_age(p.age + 1)`; reborrow temp for a `&mut` argument. All existing tests pass. Commit `feat: MIR storage-dead at scope ends, two-phase receivers, reborrows`.

### Task 3: Types: borrowing types, elision, `&mut` moves

**Files:** `src/types/mod.rs`, `src/types/decls.rs`, `src/types/infer.rs`

```rust
impl TypeInfo { pub fn contains_ref(&self, t: &Type) -> bool }   // memoized per ADT; recursion guarded by a visiting set
pub struct GlobalInfo { ..., pub elided: Option<usize> }
```
- `is_copy`: `&mut T` is false.
- decls: remove the Plan 3a field and return position check. For each def and trait method whose return type contains a reference, compute `elided` or report the elision error at the return type span. `Gc::borrow`/`borrow_mut` get `elided: Some(0)`.
- infer: in the `Gc.new` resolution, if the argument type (resolved at the end of the function, like other deferred checks) is a borrowing type, report "cannot store a value holding references in `Gc`".

- [ ] Tests: `contains_ref` for `Words`, `Option[&Int]`, a generic struct instantiated with a reference; elision picks self, picks the single reference parameter, errors on two reference parameters and on none; `&mut` is not `Copy`; `Gc.new` of `Words` errors. Delete `tests/errors/ref_in_field.*`. Commit `feat: references in fields and returns with elision`.

### Task 4: Scope-exit drops in ownck

**Files:** `src/ownck.rs`

- `StorageDead(l)` for a tracked local: reading state says it may be live, so emit a guarded drop, set it `Dead`, and clear the flag. `StorageDead` is kept in the output for borrowck.
- `Return`: guarded drops in reverse local order.
- Drop flags only for locals whose type needs drop glue (`info.needs_drop` with the body's bounds; a type parameter needs drop unless bounded by `Copy`). Move checking still covers every non-`Copy` local.

- [ ] Tests (dump): inner scope local dropped before the code after the scope; loop body local dropped each iteration; reverse order at return; `&mut` local gets no flag. Update `tests/programs/drop.out` if the order changes, and check each change against the scope rules by hand. Commit `feat: drops at scope exit in reverse declaration order`.

### Task 5: The borrow checker

**Files:** `src/borrowck.rs`, `src/main.rs`, `src/driver.rs`

The algorithm above, steps 1–5. Step 6 is Task 6.

- [ ] Tests, each a small program checked for acceptance or its exact message:
  - accepted: NLL (`let r = &mut x; use(r); x = 1`); disjoint fields; two-phase `p.set_age(p.age + 1)`; reborrow `f(r); f(r)` with `r: &mut T`; returning `&self.field`; returning a parameter; storing `&s` in `Words` and reading through it; a loop that borrows each iteration;
  - rejected: `*out = Some(&local)` and `*out = Some(other_param)` behind `out: &mut Option[&String]`; a generic `set(&mut o, &tmp)` with `o` outliving `tmp`; read while mutably borrowed; `&mut` while shared-borrowed; assign while borrowed; move while borrowed; `return &local`; a reference stored in a `Words` that outlives its scope; `&mut` alias through two `&mut` borrows kept live; returning the wrong parameter's reference.

  Commit `feat: NLL borrow checker`.

### Task 6: Gc runtime exclusivity

**Files:** `runtime/rush_rt.c`, `runtime/rush_rt.h`, `src/borrowck.rs`, `src/cgen.rs`, `tests/runtime.rs`

- Header: replace `pad[7]` with `int32_t borrows` and `uint8_t pad[3]`, keeping 8-byte alignment of the payload (check with a `_Static_assert` if `tcc` accepts it, else a runtime test).
- `void *rush_gc_borrow(void *p)`, `void *rush_gc_borrow_mut(void *p)`, `void rush_gc_release(void *p, int mut)`. The first two panic as specified and return `p`.
- cgen: `Gc::borrow` → `target = rush_gc_borrow(*g);` and `Gc::borrow_mut` → `target = rush_gc_borrow_mut(*g);`. The new intrinsic `Gc::release` with a const `Bool` argument → `rush_gc_release(p, m);`.
- borrowck step 6 inserts the releases as `Call(Callee::Def { name: "Gc::release" }, [gcb_k, mut])` into a `Unit` temp.

- [ ] Tests: C runtime test: borrow, borrow, borrow_mut panics; release then borrow_mut succeeds. MIR dump test: release placed after the last use and on the branch that does not use the reference. Commit `feat: runtime exclusivity for Gc borrows`.

### Task 7: Golden and error programs

- `tests/programs/borrows.rush`: the language-rules example above, minus the commented errors, with expected output.
- `tests/programs/scopes.rush`: a `Drop` type printing its name. Nested `if` scopes, a `while` loop creating one per iteration, early `return` from the middle of a scope, a reassignment, and an expression-statement temporary. The expected order is written out from the scope rules before running.
- `tests/programs/gc_borrow.rush`: shared borrows twice, then `borrow_mut` after the shared references die, and a borrow held across an `if` with the use on one branch only.
- Error programs, one each: `borrow_mut_conflict`, `borrow_shared_conflict`, `assign_borrowed`, `move_borrowed`, `return_local_ref`, `elision_ambiguous`, `gc_holds_ref`, `ref_outlives_scope`.
- A runtime panic program `tests/programs/gc_conflict.rush` checks the stderr message and non-zero exit. Extend `tests/programs.rs` with an `.err`-style expected stderr for programs that panic, if the harness has none yet.
- All Plan 1, 2, and 3a programs still pass.

- [ ] Commit `feat: borrow checking golden and error programs`.

### Task 8: Docs and PR

- [ ] README: add a short borrow example (the `set_age` / `&mut` lines). Spec: mark 3b shipped in the plan table. Add the four owner decisions and the four defaults to the decision table once approved. Replace the "Until Plan 3b" known-corner line with what remains: no lifetime syntax, one lifetime per borrowing type, and conservative loan union for generic calls.
- [ ] `cargo build --release`, all programs, `git status` clean, push `plan3b`, PR against `plan3a`.

---

## Self-review against the spec

- **Covered:** single `&mut` or many `&` per place; no move, assignment, or scope end while borrowed; borrows end at last use on the CFG; elision with the suggested error; drops at scope exit on every path; `Gc` runtime checks with compile-time checked references; both sites named in borrow errors.
- **Not covered, by design:** lifetime syntax (spec: none in Stage 1); closures capturing borrows (Plan 4 builds on these loan sets); "later used here" notes.
- **Known imprecision:** a borrowing type's references share one lifetime, so borrowing one field extends the others; generic calls union argument loans.
- **Owner review points:** the four defaults at the top.
