/-
`grind` is inspired by automated reasoning techniques developed in the world of Satisfiability Modulo Theories (SMT).

However, it is not an SMT solver and is not designed to solve massive combinatorial problems.
For example, it would crash if we tried to feed it some of the bit-blasted formulas produced by
`bv_decide`.

At the core of grind, we use a custom congruence closure algorithm for dependent type theory.
We accumulate terms that are known to be equal. You should think of it as a blackboard where
we keep all the facts we know about the current goal.
Remark: Terms known to be true (false) belong to the equivalence class of the term `True` (`False`).
-/

set_option grind.warning false -- Disables warning messages stating that `grind` is WIP.

example (a b c : α) (f : α → α) : f a = c → a = b → c = f b := by
  grind

/-
`grind` normalizes terms before adding them to the `grind` state.
Goals:
- We want to minimize the number of different things we need to handle.
- We want to canonicalize instances, implicit terms, etc.
- We want to hash cons terms, i.e., structural equality == pointer equality (performance).
- ...
-/

set_option trace.grind.assert true in -- Trace asserted facts
example : a = 1 + 2 → b = 3 → a = b := by
  grind

/-
`grind` applies many "constraint" propagation rules. They are used
to apply many builtin principles such as
- Injectivity of constructors.
- Beta reduction
- Extensionality theorems.
- Logical connectives.
- ...
-/

set_option trace.grind.eqc true in -- Trace equivalence classes being merged
example (f : Nat → List Nat) : f a = [1, 2] → f b = [] → a ≠ b := by
  grind

/-
`grind` does not case-split like a SMT solver. It uses the structure of the formula,
and splits on `if-then-else`-expressions, `match`-expressions, inductive predicates
marked with `[grind cases]`, etc.
-/
set_option trace.grind.split true in -- Trace case-splits performed by `grind`
example : (match x with
           | 0 => 1
           | _ + 1 => 2) > 0 := by
  grind

example : (match x with
           | 0 => 1
           | _ + 1 => 2) > 0 := by
  fail_if_success grind (splits := 0) -- `grind` fails if we don't allow it case-split.
  sorry

/-
`grind` shows you the case-splits performed when it fails.
-/
example : (match x with
           | 0 => 1
           | _ + 1 => 2) > 1 := by
  fail_if_success grind
  sorry

/-
`simp` uses theorems as rewriting rules.
`grind` instantiates the theorems using E-matching.
Each theorem is annotated with patterns.
Whenever, it finds an instance of the pattern modulo
the equalities in its state, it instantites the theorem.
There is no rewriting happening. It is just accumulating facts.
-/

opaque f : Nat → Nat
opaque g : Nat → Nat
-- `[grind =]` instructs `grind` to use the left-hand side of the conclusion as the pattern.
@[grind =] theorem fg : f (g x) = x := sorry

set_option trace.grind.assert true in
set_option trace.grind.ematch.instance true in
example : f a = b → a = g c → b = c := by
  grind

/-
We have the following variants:
- `[grind =_]`: use right-hand side of the conclusion.
- `[grind _=_]`: use both right and left-hand side of the conclusion.
- `[grind →]`: use terms in the antecedents as patterns. "Forward reasoning"
- `[grind ←]`: use terms in the conclusion as patterns. "Backward reasoning"
- `[grind =>]`: look for patterns from left to right.
- `[grind <=]`: look for patterns from right to left.
-/

opaque R : Nat → Nat → Prop
@[grind →] theorem Rtrans : R x y → R y z → R x z := sorry
@[grind →] theorem Rsymm : R x y → R y x := sorry

set_option trace.grind.assert true in
example : R a b → R c b → R d c → R a d := by
  grind

/-
The attributes above are for convenience.
If an user wants total control over the selected pattern
they may use the command `grind_pattern`.
-/

opaque bla : Nat → Nat
theorem blaThm : bla (bla x) = bla x := sorry

grind_pattern blaThm => bla (bla x)

set_option trace.grind.assert true in
example : bla a = b → bla b = b := by
  grind


/-
We also have
- `[grind ←=]`: equality driven backward reasoning.
-/

opaque U : Type
axiom mul : U → U → U
axiom one : U
axiom inv : U → U

/--
In the following example, `grind` instantiates the theorem
whenever it learns a disequality `t = s` where `t` or `s` E-matches `inv a`
-/
@[grind ←=] theorem inv_of_mul : mul a b = one → inv a = b :=
  sorry

/-
Like `simp`, we also have `grind only`
-/
example : R a b → R c b → R d c → R a d := by
  fail_if_success grind only -- `Rtrans` and `Rsymm` were not applied
  sorry

example : R a b → R c b → R d c → R a d := by
  grind only [→ Rtrans, → Rsymm]

example : R a b → R c b → R d c → R a d := by
  grind only [Rtrans, ← Rsymm]

/-
We also have `grind?`.

We currently do not try to minimize the number of generated arguments, but
we will do it in the future.
It behaves like `simp?`. If something was used, it will appear in the result.
-/

example : R a b → R c b → R d c → R a d := by
  grind?


/-
We can instruct `grind` to case-split on inductive predicates and types,
and use the constructors of an inductive predicate as E-matching theorems.
-/

abbrev Variable := String
def State := Variable → Nat
inductive Stmt : Type where
  | skip : Stmt
  | assign : Variable → (State → Nat) → Stmt
  | seq : Stmt → Stmt → Stmt
  | ifThenElse : (State → Prop) → Stmt → Stmt → Stmt
  | whileDo : (State → Prop) → Stmt → Stmt
infix:60 ";; " => Stmt.seq
export Stmt (skip assign seq ifThenElse whileDo)
set_option quotPrecheck false in
notation s:70 "[" x:70 "↦" n:70 "]" => (fun v ↦ if v = x then n else s v)
inductive BigStep : Stmt → State → State → Prop where
  | skip (s : State) : BigStep skip s s
  | assign (x : Variable) (a : State → Nat) (s : State) : BigStep (assign x a) s (s[x ↦ a s])
  | seq {S T : Stmt} {s t u : State} (hS : BigStep S s t) (hT : BigStep T t u) :
    BigStep (S;; T) s u
  | if_true {B : State → Prop} {s t : State} (hcond : B s) (S T : Stmt) (hbody : BigStep S s t) :
    BigStep (ifThenElse B S T) s t
  | if_false {B : State → Prop} {s t : State} (hcond : ¬ B s) (S T : Stmt) (hbody : BigStep T s t) :
    BigStep (ifThenElse B S T) s t
  | while_true {B S s t u} (hcond : B s) (hbody : BigStep S s t) (hrest : BigStep (whileDo B S) t u) :
    BigStep (whileDo B S) s u
  | while_false {B S s} (hcond : ¬ B s) : BigStep (whileDo B S) s s
notation:55 "(" S:55 "," s:55 ")" " ==> " t:55 => BigStep S s t

example {B S T s t} (hcond : B s) : (ifThenElse B S T, s) ==> t → (S, s) ==> t := by
  grind [cases BigStep]

theorem cases_if_of_true {B S T s t} (hcond : B s) : (ifThenElse B S T, s) ==> t → (S, s) ==> t := by
  grind [cases BigStep]

theorem cases_if_of_false {B S T s t} (hcond : ¬ B s) : (ifThenElse B S T, s) ==> t → (T, s) ==> t := by
  grind [cases BigStep]

theorem if_iff {B S T s t} : (ifThenElse B S T, s) ==> t ↔ (B s ∧ (S, s) ==> t) ∨ (¬ B s ∧ (T, s) ==> t) := by
  grind [cases BigStep, intro BigStep]

example {B S T s t} : (ifThenElse B S T, s) ==> t ↔ (B s ∧ (S, s) ==> t) ∨ (¬ B s ∧ (T, s) ==> t) := by
  grind [BigStep] -- shortcut for `cases BigStep` and `intro BigStep`

/-
`grind` already has support for offset equalities and inequalities:
- `x + k ≤ y`, `x ≤ y + k`, `x + k = y`, ... where `k` is a numeral.
- Efficient algorithm.
- Very compact proofs.
- Exhaustive propagation, but it does not case-split on disequalities.

Very effective for examples using the notation `a[i]`
-/

-- Standard library will be
attribute [grind =] Array.size_set Array.get_set_eq Array.get_set_ne

example (as bs cs ds : Array α) (v₁ v₂ v₃ : α)
        (i₁ i₂ i₃ j : Nat)
        (h₁ : i₁ < as.size)
        (h₂ : as.set i₁ v₁ = bs)
        (h₃ : i₂ < bs.size)
        (h₃ : bs.set i₂ v₂ = cs)
        (h₄ : i₃ < cs.size)
        (h₅ : ds = cs.set i₃ v₃)
        (h₆ : j ≠ i₁ ∧ j ≠ i₂ ∧ i₃ ≠ j)
        (h₇ : j < ds.size)
        (h₈ : j < as.size)
        : ds[j] = as[j] := by
  set_option diagnostics true in
  grind

/-
`grind` has support for splitting on `match`-expressions with overlapping patterns.
It is quite complex in the dependent case, and many `cast`-operations have to be performed.
-/
namespace Ex
def f : List Nat → List Nat → Nat
  | _, 1 :: _ :: _ => 1
  | _, a :: _ => if a > 1 then 2 else 3
  | _, _  => 0

example : z = a :: as → y = z → f x y > 0 := by
  grind [f.eq_def]
end Ex

/- It gets quite messy with dependent pattern matching. -/
inductive Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n+1)

def h (v w : Vec α n) : Nat :=
  match v, w with
  | _, .cons _ (.cons _ _) => 20
  | .nil, _  => 30
  | _, _    => 40

example : b = .cons 1 .nil → h a b = 40 := by
  grind [h.eq_def]

/-
`try?` tactic is a driver around `grind` (and other tactics).
It tries many different things (e.g., applies function induction principle for you)
-/
def app : List α → List α → List α
  | [], bs => bs
  | a::as, bs => a :: app as bs

-- TODO(kmill): reenable test after stage0 update
-- theorem app_assoc : app as (app bs cs) = app (app as bs) cs := by
--   try?

/-
`grind` has a notion of term "generation". It is useful for avoiding
unbounded instantiation.
-/
opaque bomb : Nat → Nat
@[grind =] theorem bombEx : bomb x = bomb (bomb x) + 1 := sorry

example : bomb x > 10 := by
  fail_if_success grind
  sorry

/-
Roadmap:
- Improve `try?`
- Improve diagnostics. There are so many possible improvements.
- Improve heuristics (e.g., "weights", `grind` specific `[grind ext]`).
- Bug fixes.
- Linear integer arithmetic.
- More examples like `constProp.lean`.
- Commutative rings support (Q2).
- Annotate standard library (Q2).
- `grind?` argument minimization (Q2).
- Fixing `induction a <;> grind?` (Q2).
- `bv_decide` integration (Q2).
- E-matching modulo associativity and commutativity?
-/
