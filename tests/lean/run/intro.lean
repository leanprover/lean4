/-!
Tests of the `intro` tactic
-/

/-!
No arguments, introduce one hypothesis.
-/
/--
trace: n✝ : Nat
⊢ n✝ = 1 → n✝ + 1 = 2
---
trace: n✝ : Nat
a✝ : n✝ = 1
⊢ n✝ + 1 = 2
-/
#guard_msgs in
example : ∀ n : Nat, n = 1 → n + 1 = 2 := by
  intro
  trace_state
  intro
  trace_state
  subst_vars
  rfl

/-!
`_` uses hygienic name derived from binder name
-/
/--
trace: n✝ : Nat
h : n✝ = 1
⊢ n✝ + 1 = 2
-/
#guard_msgs in
example : ∀ n : Nat, n = 1 → n + 1 = 2 := by
  intro _ h
  trace_state
  subst_vars
  rfl

/-!
`rfl` pattern applies `substEq`.
Order doesn't matter, and HEq is allowed.
-/
/-- trace: ⊢ 1 + 1 = 2 -/
#guard_msgs in
example : ∀ n : Nat, n = 1 → n + 1 = 2 := by
  intro _ rfl
  trace_state
  subst_vars
  rfl
/-- trace: ⊢ 1 + 1 = 2 -/
#guard_msgs in
example : ∀ n : Nat, 1 = n → n + 1 = 2 := by
  intro _ rfl
  trace_state
  subst_vars
  rfl
/-- trace: ⊢ 1 + 1 = 2 -/
#guard_msgs in
example : ∀ n : Nat, n ≍ 1 → n + 1 = 2 := by
  intro _ rfl
  trace_state
  subst_vars
  rfl
/-- trace: ⊢ 1 + 1 = 2 -/
#guard_msgs in
example : ∀ n : Nat, 1 ≍ n → n + 1 = 2 := by
  intro _ rfl
  trace_state
  subst_vars
  rfl

/-!
Introduces `let`s and `have`s
-/
/--
trace: x : Nat := 1
y : Nat := 2
⊢ x + y = 3
-/
#guard_msgs in
example : let n := 1; have m := 2; n + m = 3 := by
  intro x y
  trace_state
  rfl

/-!
Unfolds definitions if necessary.
-/
/--
trace: n : Nat
⊢ n ≥ 0
-/
#guard_msgs in
example : id (∀ n, n ≥ 0) := by
  intro n
  trace_state
  exact Nat.zero_le n

/-!
Patterns.
-/
/--
trace: x : Nat
y : Int
⊢ (x, y) = (x, y)
-/
#guard_msgs in
example : ∀ p : Nat × Int, p = p := by
  intro (x, y)
  trace_state
  rfl
/--
trace: x : Nat
y : Int
⊢ (x, y) = (x, y)
-/
#guard_msgs in
example : ∀ p : Nat × Int, p = p := by
  intro ⟨x, y⟩
  trace_state
  rfl

/-!
Can give type ascriptions, and elaboration is interleaved with unification.
Without interleaving, this test would fail because the ascription would elaborate to `(1 : Nat) = _`
-/
/--
trace: h : (1 : Int) = (1 : Int)
⊢ True
-/
#guard_msgs in
set_option pp.numericTypes true in
example : (1 : Int) = 1 → True := by
  intro (h : 1 = _)
  trace_state
  trivial

/-!
Error if there are too many arguments.
-/
/--
error: Tactic `introN` failed: There are no additional binders or `let` bindings in the goal to introduce

a : Nat
b : a = 1
⊢ a + 1 = 2
-/
#guard_msgs in
example : ∀ n : Nat, n = 1 → n + 1 = 2 := by
  intro a b c

/-!
Error if substitution isn't between variables.
-/
/--
error: Tactic `subst` failed: invalid equality proof, it is not of the form (x = t) or (t = x)
  1 = 2

a✝ : 1 = 2
⊢ False
-/
#guard_msgs in
example : 1 = 2 → False := by
  intro rfl

/-!
Error if type ascription doesn't unify
-/
/--
error: Type mismatch: Hypothesis `n` has type
  Nat
but is expected to have type
  Int
due to the provided type annotation
-/
#guard_msgs in
example : ∀ (n : Nat), n = n := by
  intro (n : Int)

/-!
Error if type ascription has unsolved metavariables.
-/
/--
error: don't know how to synthesize placeholder
context:
⊢ ?_
---
error: don't know how to synthesize placeholder for argument `β`
context:
⊢ Sort _
---
error: unsolved goals
n : Nat
⊢ n = n
-/
#guard_msgs in
set_option pp.mvars false in
example : ∀ (n : Nat), n = n := by
  intro (n : Function.const _ Nat _)
