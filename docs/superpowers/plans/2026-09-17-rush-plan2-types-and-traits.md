# Rush Plan 2: Data Types, Generics, and Traits Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Rush programs can define `struct`, `enum`, `trait`, and `impl`, use tuples, pattern-match with `case`/`in` (checked for exhaustiveness), write generic functions and generic instances that compile by monomorphization, and interpolate strings through the `Show` trait.

**Architecture:** The lexer and parser grow new items, type expressions, patterns, and string interpolation. The checker gains a type-parameter form, schemes with trait bounds, instance tables, method resolution, and an exhaustiveness pass. MIR gains places, aggregates, and discriminants. A new `mono.rs` pass instantiates generic bodies and resolves trait calls to concrete functions, so `cgen.rs` still only sees ground types. Plan 3 will add references on top of this; in this plan `&T`, `&mut T`, `&e`, and `*e` parse and are erased.

**Tech Stack:** Rust 1.98 stable, no crates. C99 runtime. `tcc` on this machine.

**Spec:** `docs/superpowers/specs/2026-09-17-rush-stage1-design.md`

**Decisions taken for this plan with the owner (2026-09-17):**
- Higher-kinded traits (Functor/Applicative/Monad, `F[_]`) move to Plan 4, where closures make them usable.
- Struct construction is `Point { x: 1.0, y: 2.0 }`. A `CamelCase` name followed by `{` is a struct literal, never a block.
- `&self`, `&mut self`, `&T`, `&mut T`, `&e`, `*e` parse and are erased: `&T` means `T` until Plan 3.
- Tuples are in. `Char`, `Symbol`, sized integers, `f32`, and `let x: T = e` are not in this plan.
- Associated types wait for Plan 5, where `Iterator` first needs them. Supertraits are in.
- `Ord` and `<` on user types wait for Plan 5. `==` on user types goes through `Eq`.
- List patterns `[p, *rest]` wait for Plan 5 with `List`.

**Plan reading note:** Tasks give complete data structures, interfaces, tests, and golden programs, plus the algorithm for each pass. Ordinary Rust that follows directly from those is written at execution time by this same session. Anything subtle has its code in the plan.

## Global Constraints

- Everything in Plan 1's Global Constraints still applies (no crates, C99 via `tcc -std=c99`, diagnostics format, `rush_` prefix, commit per task).
- Generic code compiles only by monomorphization. Polymorphic recursion is an error: "polymorphic recursion is not supported".
- Every `case` must be exhaustive. The error names one missing pattern.
- Overlapping instances are an error at declaration time. No orphan rule.
- A method call whose receiver type is still unknown is an error: "cannot infer the receiver type of `.m`; add an annotation".
- An unresolved type variable that survives inference in a non-generic position is an error: "type annotations needed".
- Recursive types without indirection (an enum that contains itself by value) are an error: "recursive type `T` has infinite size".
- Prelude code is now real Rush (traits and instances), so the prelude's expression ids come from the same counter as the user file. Diagnostics inside the prelude are compiler bugs and may render against the user file.

## Language surface added by this plan

```ruby
struct Point
  x: Float
  y: Float
end

struct Pair[A, B]
  first: A
  second: B
end

enum Shape
  Circle(Float)
  Rect(Float, Float)
  Empty
end

trait Area
  def area(&self) -> Float
  def describe(&self) -> String
    "area #{self.area}"
  end
end

trait Named: Show
  def name(&self) -> String
end

impl Area for Shape
  def area(&self)
    case self
    in Circle(r) then 3.14159 * r * r
    in Rect(w, h) then w * h
    in Empty then 0.0
    end
  end
end

impl Show for Point
  def to_s(&self)
    "(#{@x}, #{@y})"
  end
end

impl Point
  def swap(&self) -> Point
    Point { x: self.y, y: self.x }
  end
end

impl[T: Show] Show for Option[T]
  def to_s(&self)
    case self
    in Some(v) then "Some(#{v})"
    in None then "None"
    end
  end
end

def unwrap_or[T](o: Option[T], default: T) -> T
  case o
  in Some(v) then v
  in None then default
  end
end

def pair_up(a, b)
  (a, b)
end

def main
  let p = Point { x: 1.0, y: 2.0 }
  puts("#{p} swapped is #{p.swap}")
  let t = pair_up(1, "one")
  let (n, s) = t
  puts("#{t.0} #{s} #{unwrap_or(Some(3), 0)}")
  case (n, Some(s))
  in (1, Some(x)) if x == "one" then puts("matched #{x}")
  in (_, _) then puts("no")
  end
end
```

Rules:

- `@x` inside a method is `self.x`. (Pulled forward from Plan 4 because it is two lines in the parser.)
- `recv.name` with no parentheses is a field access when `recv` is a struct with that field, otherwise a zero-argument method call. `recv.name(args)` is always a method call. `t.0` is a tuple index.
- Variant constructors are global names: `Circle(1.0)`, `Some(3)`, `None`. Two enums declaring the same variant name is an error.
- Trait methods are called with method syntax only. `self` is a keyword; the first parameter of a method is `self`, `&self`, or `&mut self`.
- Generic parameters are declared in square brackets on `def`, `struct`, `enum`, and `impl`. A bound is `T: Show` or `T: Show + Eq`. A `def` without annotations is inferred and generalized; its bounds are inferred from the generic functions it calls.
- `Self` inside a `trait` is the implementing type. Inside an `impl` it is the `self_ty`.
- `==` and `!=` on `Int`, `Float`, `Bool`, `String` are built in. On any other type they call `Eq::eq`.
- `+` on `String` concatenates. `"a #{e} b"` is `"a " + e.to_s + " b"`.
- Multi-line arm bodies: `in Pattern` followed by a newline, statements, until the next `in`, `else`, or `end`. `else` is a final wildcard arm.
- `let (a, b) = e` destructures with an irrefutable pattern. A refutable pattern in `let` is an error: "refutable pattern in `let`; use `case`".

## File structure

| File | Change |
|---|---|
| `src/lexer.rs` | String interpolation token, `Self` keyword |
| `src/ast.rs` | New items, type expressions, patterns, expression kinds |
| `src/parser.rs` | All new syntax |
| `src/types.rs` | Split into `src/types/mod.rs` (Type, Scheme, TypeInfo), `src/types/decls.rs` (collect structs/enums/traits/impls), `src/types/infer.rs` (expressions, patterns, methods, generalization), `src/types/exhaust.rs` (exhaustiveness) |
| `src/mir.rs` | Places, aggregates, discriminant, pattern lowering |
| `src/mono.rs` | New: monomorphization and trait resolution |
| `src/cgen.rs` | Type definitions, aggregates, places, string concat |
| `runtime/rush_rt.c`, `.h` | `rush_str_concat` |
| `std/prelude.rush` | `Show`, `Eq`, `Option`, instances for primitives |
| `tests/programs/*.rush` | shapes, option, tuples, interp, traits, generics |
| `tests/errors/*.rush` | nonexhaustive, unknown_field, missing_impl, ambiguous, refutable_let, recursive_type |

---

### Task 1: Lexer and parser for the new syntax

**Files:**
- Modify: `src/lexer.rs`, `src/ast.rs`, `src/parser.rs`

**Interfaces produced (AST):**

```rust
pub enum Item { Def(Def), Extern(Def), Struct(StructDef), Enum(EnumDef), Trait(TraitDef), Impl(ImplDef) }

pub struct GenericParam { pub name: String, pub bounds: Vec<String>, pub span: Span }
pub struct Generics { pub params: Vec<GenericParam> }

pub enum SelfKind { Value, Ref, RefMut }

pub struct Def {
    pub name: String,
    pub generics: Generics,
    pub self_param: Option<SelfKind>,   // Some for methods
    pub params: Vec<Param>,             // excludes self
    pub ret: Option<TypeExpr>,
    pub body: Block,                    // empty for extern and required trait methods
    pub span: Span,
}

pub struct StructDef { pub name: String, pub generics: Generics, pub fields: Vec<FieldDef>, pub span: Span }
pub struct FieldDef { pub name: String, pub ty: TypeExpr, pub span: Span }
pub struct EnumDef { pub name: String, pub generics: Generics, pub variants: Vec<VariantDef>, pub span: Span }
pub struct VariantDef { pub name: String, pub fields: VariantFields, pub span: Span }
pub enum VariantFields { Unit, Tuple(Vec<TypeExpr>), Named(Vec<FieldDef>) }
pub struct TraitDef { pub name: String, pub supertraits: Vec<String>, pub methods: Vec<Def>, pub span: Span }
pub struct ImplDef { pub generics: Generics, pub trait_name: Option<String>, pub self_ty: TypeExpr, pub methods: Vec<Def>, pub span: Span }

pub enum TypeExpr {
    Name(String, Vec<TypeExpr>, Span),      // Int, List[T], Self, T
    Tuple(Vec<TypeExpr>, Span),
    Fn(Box<TypeExpr>, Box<TypeExpr>, Span),  // A -> B, right-associative
    Ref(bool, Box<TypeExpr>, Span),          // &T (false) / &mut T (true); erased in this plan
}

pub enum Stmt { Let { pat: Pattern, mutable: bool, init: Expr, span: Span }, Expr(Expr) }

pub type PatId = u32;
pub struct Pattern { pub id: PatId, pub kind: PatKind, pub span: Span }
pub enum PatKind {
    Wild,
    Bind(String),
    Lit(Lit),
    Tuple(Vec<Pattern>),
    Variant { name: String, fields: Vec<Pattern> },              // Circle(r), None
    Struct { name: String, fields: Vec<(String, Pattern)> },     // Point { x: a, y: b }, Rect { w: a, h: b }
    Or(Vec<Pattern>),
    At(String, Box<Pattern>),
}
pub enum Lit { Int(i64), Float(f64), Str(String), Bool(bool), Unit }

pub struct Arm { pub pat: Pattern, pub guard: Option<Expr>, pub body: Block, pub span: Span }

// ExprKind additions
Tuple(Vec<Expr>),
StructLit { name: String, fields: Vec<(String, Expr)> },
Dot { recv: Box<Expr>, name: String, args: Option<Vec<Expr>> },   // p.x, p.m, p.m(a)
TupleIndex(Box<Expr>, usize),
Case { scrutinee: Box<Expr>, arms: Vec<Arm> },
Interp(Vec<InterpPart>),
pub enum InterpPart { Lit(String), Expr(Expr) }
```

Pattern ids are allocated from the same counter as expression ids (`next_id`), so `pat_types` can be a separate map without collisions.

**Lexer changes:**
- Add keyword `Self`. (`self` is already a keyword.)
- String literal lexing: when `#{` appears inside a string, produce `Tok::Interp(Vec<RawPart>)` with `RawPart::Lit(String)` and `RawPart::Code(String, u32)` where the `u32` is the byte offset of the code's first character in the source. Nesting is tracked by counting `{`/`}` inside the code. A string without `#{` stays `Tok::Str`.
- The parser lexes each `Code` part with `lex`, shifts every span by the offset, and parses it with a sub-`Parser` that shares `next_id`. The sub-parse must consume everything except the trailing `Newline`/`Eof`.

**Parser changes:**
- Items: `struct`, `enum`, `trait`, `impl` per the surface above. `impl[T: Show] Show for Option[T]` and `impl Point`. Trait bodies contain `def` signatures with or without a body: a signature line ending in a newline followed by `def`/`end` has no body; otherwise the body runs to `end`. Concretely: after the header, if the next non-newline token is `def` or `end`, the method has no body.
- Generic lists: `[T, U: Show + Eq]` after the name.
- Method headers: first parameter `self`, `&self`, or `&mut self` sets `self_param`.
- Type expressions: `Name`, `Name[args]`, `(A, B)`, `A -> B`, `&T`, `&mut T`, `Self`.
- Postfix: `.ident` with optional `(args)` becomes `Dot`; `.INT` becomes `TupleIndex`.
- Primary: `(a, b)` tuple (a parenthesised expression followed by `,`), `Name { f: e, ... }` when `Name` is CamelCase and the next token is `{`, `case`, `@ident` → `Dot { recv: Var("self"), name, args: None }`, `self` → `Var("self")`, `Self` is only a type.
- Unary `&`, `&mut`, `*` parse and return the operand unchanged.
- `case e` newline, then arms: `in PAT [if GUARD] then EXPR` or `in PAT [if GUARD]` newline statements; `else` newline statements as a `Wild` arm; `end`.
- Patterns, tightest first: `x @ p`, then `p | q`. Atoms: `_`, literal, `-INT`, `ident` (binding, lowercase), `Name` (unit variant), `Name(p, ...)`, `Name { f: p, ... }`, `(p, q)`. A `Name { f }` shorthand binds `f` to field `f`.
- `let PAT = e`: a `let` whose target starts with `(` parses a pattern; otherwise an identifier.

- [ ] **Step 1: Write failing parser tests** for every bullet above. At minimum:

```rust
#[test] fn struct_and_generic_struct() { /* fields, generics.params names */ }
#[test] fn enum_with_three_variant_shapes() { /* Unit, Tuple, Named */ }
#[test] fn trait_with_required_and_default_method_and_supertrait() { /* body empty vs not; supertraits == ["Show"] */ }
#[test] fn impl_inherent_and_generic_trait_impl() { /* trait_name None/Some, generics bounds */ }
#[test] fn method_self_kinds() { /* self, &self, &mut self */ }
#[test] fn type_exprs() { /* Pair[Int, String], (Int, Bool), Int -> Int -> Bool right assoc, &mut T */ }
#[test] fn dot_field_method_and_tuple_index() { /* p.x, p.m(1), t.0 */ }
#[test] fn struct_literal_vs_block() { /* Point { x: 1.0 } is StructLit; lowercase name followed by { is an error for now */ }
#[test] fn tuple_literal_and_let_pattern() { /* (1, "a"); let (a, b) = t */ }
#[test] fn case_arms_single_and_multi_line_with_guard_and_else() {}
#[test] fn patterns_or_at_and_negative_literal() { /* x @ (1 | 2), -1 */ }
#[test] fn interpolation_parses_code_with_correct_spans() { /* "#{1 + x}" → Interp; inner Binary span offsets */ }
#[test] fn at_field_is_self_dot() { /* @x → Dot(Var self, "x", None) */ }
#[test] fn refs_are_erased() { /* &x and *x parse to Var x */ }
```

- [ ] **Step 2: Run, verify they fail to compile or fail.**
- [ ] **Step 3: Implement** lexer and parser changes. Keep the Plan 1 tests green; update them only where the AST shape changed (`Stmt::Let` now has `pat`).
- [ ] **Step 4: `cargo test` green.**
- [ ] **Step 5: Commit** `feat: parse structs, enums, traits, impls, patterns, case, interpolation`.

---

### Task 2: Type representation and declaration collection

**Files:**
- Create: `src/types/mod.rs`, `src/types/decls.rs` (move Plan 1's `types.rs` into `mod.rs` + `infer.rs` in Task 3)

**Interfaces produced:**

```rust
pub enum Type { Var(u32), Param(String), Con(String, Vec<Type>), Fn(Box<Type>, Box<Type>) }
// Tuples are Con("Tuple", args); Display prints "(A, B)". Unit stays Con("Unit").

pub struct Scheme { pub vars: Vec<String>, pub bounds: Vec<(String, String)>, pub ty: Type }
// vars are Param names; bounds are (param, trait). A monomorphic type is a Scheme with no vars.

pub enum GlobalKind { Def, Extern, Variant { enum_name: String, index: usize }, ImplMethod { impl_id: usize }, TraitDefault { trait_name: String } }
pub struct Global { pub scheme: Scheme, pub n_params: usize, pub kind: GlobalKind }

pub struct StructInfo { pub generics: Vec<String>, pub fields: Vec<(String, Type)>, pub span: Span }
pub struct VariantInfo { pub name: String, pub fields: Vec<(Option<String>, Type)> }
pub struct EnumInfo { pub generics: Vec<String>, pub variants: Vec<VariantInfo>, pub span: Span }
pub struct MethodSig { pub scheme: Scheme, pub n_params: usize, pub has_default: bool }  // scheme.vars starts with "Self"
pub struct TraitInfo { pub supertraits: Vec<String>, pub methods: HashMap<String, MethodSig>, pub span: Span }
pub struct ImplInfo { pub id: usize, pub generics: Vec<String>, pub bounds: Vec<(String, String)>, pub trait_name: Option<String>, pub self_ty: Type, pub methods: HashMap<String, String>, pub span: Span }
// methods maps method name -> global name "Trait#id::m" or "Type#id::m"

pub enum DotRes { Field(usize), Method(MethodRes) }
pub enum MethodRes { Direct { global: String, targs: Vec<Type> }, Trait { trait_name: String, method: String, self_ty: Type } }

pub struct TypeInfo {
    pub expr_types: HashMap<ExprId, Type>,
    pub pat_types: HashMap<PatId, Type>,
    pub globals: HashMap<String, Global>,
    pub structs: HashMap<String, StructInfo>,
    pub enums: HashMap<String, EnumInfo>,
    pub traits: HashMap<String, TraitInfo>,
    pub impls: Vec<ImplInfo>,
    pub insts: HashMap<ExprId, Vec<Type>>,   // type args for Var/Dot exprs that reference a generic global, aligned with scheme.vars
    pub dots: HashMap<ExprId, DotRes>,
    pub variant_names: HashMap<String, (String, usize)>,  // "Circle" -> ("Shape", 0)
}

pub fn subst(t: &Type, map: &HashMap<String, Type>) -> Type;  // replaces Params
pub fn check(prog: &Program) -> Result<TypeInfo, Diagnostic>;  // orchestrates decls + infer + exhaust
```

**decls.rs responsibilities** (`collect(prog) -> Result<Decls, Diagnostic>`, called first by `check`):
1. Register every struct and enum name with its arity, so field types can refer to each other in any order.
2. Convert field and variant types with `from_ast` under the item's generic scope. `Self` is an error outside traits and impls. Unknown type names and wrong arity are errors: "unknown type `X`", "type `Pair` takes 2 type arguments, found 1".
3. Register variant constructors as globals: `Circle: Float -> Shape` (`GlobalKind::Variant`), `Some: T -> Option[T]` with scheme vars `[T]`, `None: Option[T]` with `n_params 0`. Duplicate variant names across enums are an error.
4. Register traits: each method signature becomes a `MethodSig` whose scheme has `Self` first plus the method's own generics, bound `(Self, Trait)`. Default bodies are registered as globals `Trait::m` with `GlobalKind::TraitDefault`; their bodies are checked in Task 3 under `Self: Trait`.
5. Register impls: convert `self_ty`, check the trait exists, check every required method is present ("missing method `m` in impl of `Show` for `Point`"), check no extra methods, check supertraits have impls for the same self type. Register each impl method as a global `Show#3::to_s` with scheme vars = impl generics (+ method generics), bounds = impl bounds, type = self type followed by params and return. The declared signature must unify with the trait's signature after substituting `Self`; mismatch is "method `m` has type `A`, trait requires `B`".
6. Overlap check: for each pair of impls of the same trait, if their `self_ty` unify (treating Params as fresh vars), error "overlapping instances of `Show` for `Option[T]`".
7. Recursive type check: build a graph of by-value containment between structs/enums (ignoring generics args, conservatively by constructor name); a cycle is "recursive type `T` has infinite size".

- [ ] **Step 1: Failing tests** in `types/decls.rs`: registers struct fields and variant constructors with correct schemes; duplicate variant error; missing method error; signature mismatch error; overlapping instances error; recursive type error; supertrait impl required error; `Self` outside trait error.
- [ ] **Step 2: Implement.** `from_ast` gains a `generic_scope: &[String]` and a `self_ty: Option<&Type>`.
- [ ] **Step 3: Green. Commit** `feat: collect struct, enum, trait, and impl declarations`.

---

### Task 3: Inference for the new expressions, methods, and generics

**Files:**
- Create: `src/types/infer.rs` (Plan 1's checker moves here and grows)

**Algorithm:**

1. **Def ordering.** Build the call graph over user `def`s (Var references to globals of kind Def). Compute SCCs (Tarjan). Process SCCs in dependency order. Fully annotated defs (all params and the return annotated) get their scheme up front, so they can be used at many types before their body is checked. Unannotated defs inside an SCC share monomorphic placeholders while the SCC is checked, then each is generalized. A placeholder used at two different types within its own SCC is the ordinary "type mismatch" error.
2. **Instantiation.** A `Var` naming a global with a non-empty scheme: replace each scheme var with a fresh `Var`, record the fresh vars in `insts[expr.id]`, and push each bound as a pending constraint `(fresh, trait, span)`.
3. **Rigid params.** While checking a def with declared generics `[T: Show]`, `T` is `Type::Param("T")` and its bounds are in a `param_bounds: HashMap<String, Vec<String>>`. Unification of a `Param` with anything but itself or a `Var` is a type mismatch.
4. **Generalization.** After an unannotated def's body is checked and its type resolved, every remaining `Var` in the type becomes a `Param` named `T0`, `T1`, ... in order of appearance. Pending constraints on those vars become the scheme's bounds. Pending constraints on vars that do not appear in the type and are still unresolved are "type annotations needed". Bodies are re-resolved after generalization by walking `expr_types` and replacing those vars with the params (store the mapping and apply it in the final resolve pass).
5. **Constraint solving** (`solve_pending`, run after each def): for each `(ty, trait, span)`: resolve `ty`. `Con` → find the unique impl of `trait` whose `self_ty` unifies with it (impl generics as fresh vars); push the impl's bounds as new constraints with the unified types; none → "no instance of `Show` for `Point`". `Param(T)` → `T`'s bounds (with supertrait closure) must include `trait`, else "`T` is not bounded by `Show`; add `T: Show`". `Var` → keep pending (it may be generalized).
6. **Expressions:**
   - `Tuple` → `Con("Tuple", ts)`. `TupleIndex(e, i)` → resolve `e`; must be a tuple with more than `i` fields, else "cannot index `T` with `.i`". Unresolved → "cannot infer the receiver type of `.i`".
   - `StructLit { name, fields }`: `name` is a struct or a named-fields variant. Instantiate its generics with fresh vars, unify each provided field, require every field exactly once ("missing field `y` in `Point`", "unknown field `z` in `Point`"). Type is the struct type or the enum type. Record `insts` for later aggregate typing.
   - `Dot { recv, name, args }`: infer `recv`, resolve. If `args` is `None` and the head is a struct with field `name` → `DotRes::Field(i)`, type is the field type with the struct's generics substituted. Otherwise method lookup: (a) inherent impls for the head constructor with method `name`, (b) trait impls matching the receiver type whose trait has method `name`, (c) if the receiver is `Param(T)`, traits in `T`'s bound closure with method `name`. Exactly one hit → instantiate the method global (or `MethodRes::Trait` for (c)), unify `self` type with the receiver, then treat `args` as a curried call like Plan 1. Zero hits → "no method `m` on type `T`". More than one → "ambiguous method `m` on type `T`". Unresolved receiver → the receiver error from Global Constraints.
   - `Case`: infer the scrutinee, then each arm: check the pattern against the scrutinee type (below) in a new scope with the bindings, check the guard is `Bool`, infer the body; all bodies unify. Type is the arms' type. Zero arms is a parse error.
   - `Interp(parts)`: each `Expr` part pushes the constraint `(type, "Show")` and is recorded; the whole expression is `String`. (MIR lowering turns it into `to_s` calls and `str_concat`.)
   - `Binary(Eq | Ne)`: unify both sides; if the resolved type is a primitive, built in; otherwise push `(type, "Eq")` and record `dots[expr.id] = Method(Trait { Eq, eq, type })` for lowering. `Binary(Add)` on `String` is allowed.
   - `Let { pat, .. }`: check the pattern is irrefutable (`Wild`, `Bind`, `Tuple` of irrefutable, `Struct` of irrefutable, `Variant` of a single-variant enum); bind its names.
7. **Patterns** (`check_pat(pat, expected) -> bindings`): `Wild` anything; `Bind(x)` binds `x: expected`; `Lit` unifies; `Tuple` unifies with a fresh tuple of that arity; `Variant { name, fields }` looks up the variant, instantiates the enum's generics with fresh vars, unifies the enum type with expected, checks field count ("variant `Rect` has 2 fields, pattern has 1"), recurses; `Struct` likewise by field name; `Or` checks every alternative binds the same names with the same types ("pattern alternatives bind different names"); `At` binds and recurses. Duplicate binding in one pattern is an error. Every pattern's type is recorded in `pat_types`.
8. **Method bodies**: impl methods are checked as defs whose first scope entry is `self: self_ty` and whose generic scope is the impl's generics with bounds. Trait default bodies are checked with `Self` as a `Param` bounded by the trait, and calls on `self` resolve through rule 6(c).

- [ ] **Step 1: Failing tests** (in `types/infer.rs`, using a `check_src` helper that prepends the real `std/prelude.rush`):

```rust
#[test] fn struct_literal_field_access_and_swap_method() {}
#[test] fn generic_struct_infers_type_args() { /* Pair { first: 1, second: "a" } : Pair[Int, String] */ }
#[test] fn variant_constructors_are_functions() { /* Some : T -> Option[T]; Circle(1.0) : Shape */ }
#[test] fn case_binds_and_unifies_arms() {}
#[test] fn case_arm_type_mismatch_error() {}
#[test] fn tuple_index_and_let_destructure() {}
#[test] fn refutable_let_is_error() { assert_eq!(err("..."), "refutable pattern in `let`; use `case`"); }
#[test] fn unannotated_def_is_generalized_and_used_at_two_types() { /* pair_up : T0 -> T1 -> (T0, T1) */ }
#[test] fn inferred_bounds_from_callee() { /* def f(x) g(x) end with g[T: Show] → f's scheme has (T0, Show) */ }
#[test] fn annotated_generic_with_bound_method_call() { /* def f[T: Show](x: T) x.to_s end */ }
#[test] fn unbounded_param_method_call_error() { /* def f[T](x: T) x.to_s end → "`T` is not bounded by `Show`; add `T: Show`" */ }
#[test] fn missing_instance_error() { /* "#{p}" without impl → "no instance of `Show` for `Point`" */ }
#[test] fn generic_impl_with_bound_resolves_recursively() { /* Option[Point] Show requires Point Show */ }
#[test] fn inherent_method_and_trait_method_same_name_is_ambiguous_or_inherent_wins() { /* rule: inherent wins */ }
#[test] fn receiver_unknown_error() {}
#[test] fn ambiguous_var_error() { /* let x = None */ }
#[test] fn eq_on_user_type_requires_eq_instance() {}
#[test] fn polymorphic_recursion_error() {}
#[test] fn supertrait_methods_available_through_bound() { /* T: Named where Named: Show → x.to_s ok */ }
```

- [ ] **Step 2: Implement.** Keep all Plan 1 checker tests green.
- [ ] **Step 3: Commit** `feat: infer ADTs, tuples, case, methods, generics with bounds`.

---

### Task 4: Exhaustiveness

**Files:**
- Create: `src/types/exhaust.rs`

**Interface:** `pub fn check_case(info: &TypeInfo, scrut_ty: &Type, arms: &[Arm]) -> Result<(), Diagnostic>`; the error is at the `case` span: "non-exhaustive `case`: pattern `Rect(_, _)` not covered". Arms with guards do not count toward coverage.

**Algorithm:** the usefulness matrix (Maranget, simplified):
- A pattern is represented as `Wild`, `Ctor(id, subpatterns)`, or `Or(alts)`; `Bind`/`At` become their inner pattern; `Lit` becomes `Ctor(lit, [])` from an infinite constructor set.
- Constructor sets by type: `Bool` two ctors; enum → its variants; tuple/struct → one ctor; `Int`/`Float`/`String`/`Unit` → infinite (only a wildcard row covers).
- `useful(matrix, vector)`: standard recursion by specializing on the head column's constructors; if the matrix's head column has a complete signature, specialize per constructor; otherwise use the default matrix. Returns a witness pattern (built back up) when a vector is useful.
- The check: `useful(rows-from-arms, [Wild])`; a witness means non-exhaustive. Also report "unreachable pattern" as an error for any arm that is not useful with respect to the arms above it. (Warning infrastructure does not exist; an unreachable arm is a bug.)

- [ ] **Step 1: Failing tests**: missing variant (witness printed `Rect(_, _)`), nested missing in tuple `(Some(_), None)`, bool matrix complete with `(true, _) | (false, _)`, literal patterns need wildcard, guard does not count, `else` covers, unreachable arm error, or-pattern coverage.
- [ ] **Step 2: Implement.** Wire into `check` after inference: walk every `Case` expr.
- [ ] **Step 3: Commit** `feat: exhaustiveness and unreachable-arm checking for case`.

---

### Task 5: MIR places, aggregates, and pattern lowering

**Files:**
- Modify: `src/mir.rs`

**Interface changes:**

```rust
pub struct Place { pub local: LocalId, pub proj: Vec<Proj> }
pub enum Proj { Field(usize), Downcast(usize, usize) }   // Downcast(variant, field)
pub enum Operand { Place(Place), Const(Const) }           // Local(id) becomes Place with no proj
pub enum Agg { Struct(Type), Tuple(Type), Variant(Type, usize) }  // Type is the concrete or Param-containing ADT type
pub enum Rvalue { Use(Operand), Binary(..), Unary(..), Call(Callee, Vec<Operand>), Aggregate(Agg, Vec<Operand>), Discriminant(Place) }
pub enum Callee { Def { name: String, targs: Vec<Type> }, Extern(String), Trait { trait_name: String, method: String, self_ty: Type } }
pub enum Statement { Assign(Place, Rvalue) }
```

`dump` prints places as `_3.0.1`, downcasts as `(_3 as 1).0`, aggregates as `Point { _1, _2 }`, `(_1, _2)`, `Shape::1(_4)`, discriminant as `discr(_3)`, callee targs as `f[Int, String](_1)`, trait calls as `Show::to_s[Point](_1)`.

**Lowering additions:**
- `Tuple`, `StructLit` (struct or named variant), variant `Call` and unit-variant `Var` → `Aggregate`. The `Agg` type is the expression's type from `expr_types`.
- `Dot` with `DotRes::Field(i)` → `Operand::Place` with `Proj::Field(i)` appended to the receiver's place; if the receiver is not a place (a call result), first assign it to a temp. `TupleIndex` likewise.
- `Dot` with `Method(Direct)` → `Callee::Def { name, targs }` with `self` as the first operand. `Method(Trait)` → `Callee::Trait`. Zero-arg method with `args: None` is a full call.
- `Var` of a generic def with `insts` → `Callee::Def { targs }` on the zero-param call path; `Call(Var f)` likewise.
- `Binary(Eq)` with a recorded `dots` entry → `Callee::Trait { Eq, eq }`; `Ne` → `Unary(Not)` of that.
- `Interp` → left fold of `Callee::Extern("str_concat")` over parts; expression parts become `Callee::Trait { Show, to_s, self_ty }` calls unless the part is already `String` (then used directly).
- Assignment to a field: `p.x = e` where `p` is `let mut` → `Assign(place with Field, Use)`. Assignment through a non-place is a type error added in Task 3: "cannot assign to this expression".
- `Let` with a pattern: lower the init to a temp, then bind by walking the irrefutable pattern with projections (no tests needed).
- `Case`: evaluate the scrutinee into a temp `s`. For each arm `i` in order create `test_i`; the last failure target is a block whose terminator is `Unreachable` (exhaustiveness guarantees it is dead). Per arm: allocate one local per bound name (types from `pat_types`), emit `test(pat, place(s), fail = test_{i+1})` which for `Variant` emits `d = Discriminant(place); c = Eq(d, index); If(c, next, fail)` then recurses into `Downcast(index, k)` projections; `Lit` emits `Eq` + `If`; `Tuple`/`Struct` recurse with `Field(k)`; `Bind`/`At` emit `Assign(binding, Use(Place))`; `Or` tries alternatives in sequence, each on failure jumping to the next alternative, each on success jumping to a shared `matched` block, with all alternatives assigning the same binding locals. After the tests, a guard lowers to `If(guard, body, fail)`. The body assigns the arm result to the case temp and jumps to `join`.

- [ ] **Step 1: Failing dump tests**: struct literal + field read, tuple + index, variant construction, `case` on an enum with two arms (exact block layout), `case` with or-pattern and guard, generic call with targs, interpolation lowering, `Eq` on a struct lowering to a trait call.
- [ ] **Step 2: Implement.** Update Plan 1 dump expectations only where `Local` → `Place` changes the print (`_3` prints the same).
- [ ] **Step 3: Commit** `feat: MIR aggregates, places, and case lowering`.

---

### Task 6: Monomorphization

**Files:**
- Create: `src/mono.rs`

**Interface:** `pub fn monomorphize(bodies: Vec<Body>, info: &TypeInfo) -> Result<Vec<Body>, Diagnostic>` returning bodies whose locals, aggregates, and callees contain no `Param` and whose callees are all `Callee::Def { name: mangled, targs: [] }` or `Callee::Extern`. Body names are mangled: `f` stays `f` when it has no type args; otherwise `f__Int__String`; impl methods `Show_3_to_s__Point`. `pub fn mangle_type(t: &Type) -> String` is shared with cgen: `Int`, `Pair_L_Int_String_R`, `T_L_Int_Bool_R` for tuples.

**Algorithm:**
1. Worklist seeded with `("main", [])`. Bodies are indexed by original name.
2. Pop `(name, targs)`. Skip if already generated. Build `subst` from the global's scheme vars (or impl generics + method generics for impl methods, `Self` + method generics for defaults) to `targs`. Clone the body, substitute every `Type` in locals and aggregates.
3. For each callee: `Def { name, targs }` → substitute targs, push to the worklist, rewrite to the mangled name. `Trait { trait_name, method, self_ty }` → substitute `self_ty`; find the unique impl whose `self_ty` matches (instantiate impl generics as fresh vars, unify, read back the impl targs); if the impl defines the method, target is that impl-method global with the impl targs; else the trait default `Trait::m` with `Self := self_ty`. Push and rewrite.
4. Polymorphic recursion guard: if the worklist ever holds more than 1000 distinct instantiations of one function, error "polymorphic recursion is not supported". (Cheap and good enough; a real check would compare instantiation depth.)
5. Output order: generation order, which puts `main` first; cgen emits prototypes for all so order does not matter.

- [ ] **Step 1: Failing tests**: `unwrap_or` used at `Int` and `String` yields two bodies with mangled names and ground locals; trait call on `Option[Point]` resolves to `Show_N_to_s__Point` and pulls in `Show_M_to_s` for `Point`; default method instantiation; unused generic function produces no body; polymorphic recursion error.
- [ ] **Step 2: Implement.** Wire into `driver::compile_to_c` between `lower` and `gen`.
- [ ] **Step 3: Commit** `feat: monomorphization and trait method resolution`.

---

### Task 7: Code generation, runtime, prelude, golden programs

**Files:**
- Modify: `src/cgen.rs`, `runtime/rush_rt.c`, `runtime/rush_rt.h`, `std/prelude.rush`
- Create: golden programs and error programs listed below

**cgen changes:**
- Collect every concrete ADT and tuple type appearing in any local, aggregate, or field, transitively. Emit `typedef struct rush_<mangled> rush_<mangled>;` forward declarations for all, then full definitions in dependency order (a type is emitted after every type it contains by value; Task 2 already rejected cycles).
- Struct: `struct rush_Point { double x; double y; };`. Tuple: fields `f0, f1`. Enum: `struct rush_Shape { int32_t tag; union { struct { double f0; } v0; struct { double f0; double f1; } v1; } u; };` with the `union` omitted when no variant has fields and a variant's struct omitted when it has none. Field names are the Rush names for structs and named variants, `fN` for tuples and tuple variants.
- `Aggregate` lowers to one assignment per field: `_5.tag = 1; _5.u.v1.f0 = _2;`.
- Places: `_3.x`, `_3.f0`, `_3.u.v1.f0`. `Discriminant` → `_3.tag`.
- `Binary(Add)` on `String` → `rush_str_concat(a, b)`.
- `Callee::Def { name }` → `rush_<name>` (already mangled).

**Runtime:** `rush_str rush_str_concat(rush_str a, rush_str b)` allocating a new buffer (same ponytail leak note as Plan 1).

**Prelude** (`std/prelude.rush`):

```ruby
extern "C" def puts(s: String) -> Unit
extern "C" def print(s: String) -> Unit
extern "C" def int_to_s(v: Int) -> String
extern "C" def float_to_s(v: Float) -> String
extern "C" def bool_to_s(v: Bool) -> String
extern "C" def str_concat(a: String, b: String) -> String

trait Show
  def to_s(&self) -> String
end

trait Eq
  def eq(&self, other: Self) -> Bool
end

enum Option[T]
  Some(T)
  None
end

impl Show for Int
  def to_s(&self)
    int_to_s(self)
  end
end

impl Show for Float
  def to_s(&self)
    float_to_s(self)
  end
end

impl Show for Bool
  def to_s(&self)
    bool_to_s(self)
  end
end

impl Show for String
  def to_s(&self)
    self
  end
end

impl Show for Unit
  def to_s(&self)
    "()"
  end
end

impl[T: Show] Show for Option[T]
  def to_s(&self)
    case self
    in Some(v) then "Some(#{v})"
    in None then "None"
    end
  end
end

impl Eq for Int
  def eq(&self, other: Int)
    self == other
  end
end

impl Eq for String
  def eq(&self, other: String)
    self == other
  end
end

impl Eq for Bool
  def eq(&self, other: Bool)
    self == other
  end
end

impl[T: Eq] Eq for Option[T]
  def eq(&self, other: Option[T])
    case (self, other)
    in (Some(a), Some(b)) then a == b
    in (None, None) then true
    in (_, _) then false
    end
  end
end
```

**Golden programs** (each with a `.out`):

`tests/programs/shapes.rush`:

```ruby
enum Shape
  Circle(Float)
  Rect(Float, Float)
  Empty
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
    in Circle(r) then 3.0 * r * r
    in Rect(w, h) then w * h
    in Empty then 0.0
    end
  end
end

def main
  puts(Circle(1.0).describe)
  puts(Rect(2.0, 3.0).describe)
  puts(Empty.describe)
end
```

Expected: `area 3.0`, `area 6.0`, `area 0.0`.

`tests/programs/option.rush`:

```ruby
def unwrap_or[T](o: Option[T], default: T) -> T
  case o
  in Some(v) then v
  in None then default
  end
end

def main
  puts("#{Some(3)} #{None}")
  puts(int_to_s(unwrap_or(Some(3), 0)))
  puts(unwrap_or(None, "fallback"))
  puts(bool_to_s(Some(1) == Some(1)))
  puts(bool_to_s(Some("a") == None))
end
```

Expected: `Some(3) None`, `3`, `fallback`, `true`, `false`. (`None` alone in the first line needs a type: give it `#{unwrap_or(None, 0)}`-free form by writing `let n: Option[Int] = None`? No `let` annotations in this plan, so write the first line as `puts("#{Some(3)} #{unwrap_or(Some(None), None)}")` where `unwrap_or(Some(None), None)` has type `Option[?]` still ambiguous. Use instead: `let none = if true then None else Some(0) end` which fixes `T = Int`. Final program text is settled in Step 1 of this task; the point is that `None` must be fixed by context, and the `ambiguous.rush` error program demonstrates the failure mode.)

`tests/programs/tuples.rush`:

```ruby
def pair_up(a, b)
  (a, b)
end

def main
  let t = pair_up(1, "one")
  let (n, s) = t
  puts("#{t.0} #{s} #{n == 1}")
  case (n, pair_up(true, 2.5))
  in (1, (true, f)) if f > 2.0 then puts("big #{f}")
  in (1, (true, f)) then puts("small #{f}")
  in (_, _) then puts("other")
  end
end
```

Expected: `1 one true`, `big 2.5`.

`tests/programs/interp.rush`:

```ruby
struct Point
  x: Float
  y: Float
end

impl Show for Point
  def to_s(&self)
    "(#{@x}, #{@y})"
  end
end

impl Point
  def swap(&self) -> Point
    Point { x: self.y, y: self.x }
  end
end

def main
  let p = Point { x: 1.0, y: 2.0 }
  puts("#{p} swapped is #{p.swap} and #{1 + 2} is #{true}")
  puts("nested #{"inner #{p.x}"}")
end
```

Expected: `(1.0, 2.0) swapped is (2.0, 1.0) and 3 is true`, `nested inner 1.0`.

`tests/programs/traits.rush`:

```ruby
trait Named: Show
  def name(&self) -> String
end

struct Dog
  age: Int
end

impl Show for Dog
  def to_s(&self)
    "Dog(#{@age})"
  end
end

impl Named for Dog
  def name(&self)
    "rex"
  end
end

def introduce[T: Named](x: T) -> String
  "#{x.name} is #{x}"
end

def twice(x)
  introduce(x) + " / " + introduce(x)
end

def main
  puts(twice(Dog { age: 3 }))
end
```

Expected: `rex is Dog(3) / rex is Dog(3)`.

`tests/programs/generics.rush`:

```ruby
struct Pair[A, B]
  first: A
  second: B
end

impl[A: Show, B: Show] Show for Pair[A, B]
  def to_s(&self)
    "<#{@first}, #{@second}>"
  end
end

def flip[A, B](p: Pair[A, B]) -> Pair[B, A]
  Pair { first: p.second, second: p.first }
end

def main
  let p = Pair { first: 1, second: "x" }
  puts("#{p} #{flip(p)} #{flip(flip(p))}")
  let mut q = Pair { first: true, second: 2.5 }
  q.first = false
  puts("#{q}")
end
```

Expected: `<1, x> <x, 1> <1, x>`, `<false, 2.5>`.

**Error programs** (`tests/errors/*.rush` with `.err` holding the expected substring):

- `nonexhaustive.rush`: `case` on `Shape` missing `Rect` → `error: non-exhaustive \`case\`: pattern \`Rect(_, _)\` not covered`.
- `unknown_field.rush`: `p.z` → `error: no field or method \`z\` on type \`Point\``.
- `missing_impl.rush`: `"#{p}"` with no `Show` → `error: no instance of \`Show\` for \`Point\``.
- `ambiguous.rush`: `let x = None` and nothing else → `error: type annotations needed`.
- `refutable_let.rush`: `let Some(x) = Some(1)` → `error: refutable pattern in \`let\`; use \`case\``.
- `recursive_type.rush`: `enum Tree` containing `Tree` by value → `error: recursive type \`Tree\` has infinite size`.
- `unbounded.rush`: `def f[T](x: T)` calling `x.to_s` → `error: \`T\` is not bounded by \`Show\`; add \`T: Show\``.

- [ ] **Step 1: Write the golden and error programs** above (settle the `option.rush` first line as described).
- [ ] **Step 2: Run `cargo test --test programs`**, verify the new programs fail.
- [ ] **Step 3: Implement cgen, runtime, prelude.**
- [ ] **Step 4: `cargo test` green**, including all Plan 1 programs.
- [ ] **Step 5: Commit** `feat: codegen for ADTs and tuples, Show/Eq prelude, string concat`.

---

### Task 8: Docs and PR

- [ ] Update `README.md` with a short example using a struct, an enum, `case`, and interpolation.
- [ ] Update the spec's section 8 table only if a deferred item changed plans (HKT → Plan 4, associated types → Plan 5, `Ord` → Plan 5) and add these to the "Known corners cut" list. Commit `docs: record plan 2 deferrals in the spec`.
- [ ] `cargo build --release`, run every program in `tests/programs` by hand once, `git status` clean.
- [ ] Push `plan2` and open a PR against `plan1` (or `main` if PR #1 has merged).

---

## Self-review against the spec

- **Covered:** structs, enums with unit/tuple/named variants, traits with default methods and supertraits, inherent and trait impls, generic instances with bounds, `case`/`in` with guards and `else`, all pattern forms except list patterns, exhaustiveness, tuples, generic functions with declared or inferred bounds, monomorphization, `Show` interpolation, `Eq` for `==` on user types, `@field`, parse-and-erase references.
- **Deferred with owner agreement:** HKT (Plan 4), associated types and `Iterator` (Plan 5), `Ord` on user types (Plan 5), list patterns (Plan 5), `Char`/`Symbol`/sized ints/`let` annotations (Plan 5 or later as the owner decides), `derive` for `Copy`/`Eq`/`Show` (not in spec text; raise before Plan 3).
- **Type consistency:** `Callee::Def { name, targs }` is produced by Task 5 and consumed by Task 6; `mangle_type` is defined in Task 6 and used by Task 7; `DotRes`/`MethodRes` are defined in Task 2, filled in Task 3, read in Task 5; `pat_types` keyed by `PatId` from the shared id counter introduced in Task 1.
