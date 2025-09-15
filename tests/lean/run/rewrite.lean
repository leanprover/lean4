/-!
# Tests exercising basic behaviour of `rw`.

See also `tests/lean/rewrite.lean`.
-/

-- Rewriting by `iff`
example (h : P ↔ Q) (q : Q) : P := by
  rw [h]
  exact q
example (h : P ↔ Q) (q : Q) : P := by
  rw [← h] at q
  exact q

def f (_ : Nat) : Nat := 0
def g (n : Nat) : Nat := f n

theorem t (n : Nat) : f n = f 0 := rfl
theorem s (n m : Nat) : f n = f m := rfl

example : f 1 = f 2 := by
  rw [s 1 2] -- closes the goal `f 2 = f 2` via `rfl`
example : f 1 = f 2 := by
  rw [t] -- does not close the goal, because `rw` calls `rfl` under `withReducible`
  rfl

example (h : f (f 1) = 0) : f (g 1) = 0 := by
  fail_if_success rw [h] -- Can not see through definition of `g`
  erw [h] -- "Expensive" rewrite can

-- Check `(config := ...)` works:
example (h : f (f 1) = 0) : f (g 1) = 0 := by
  rw (config := {transparency := .default}) [h] -- This is just `erw`.

attribute [reducible] f in
example : f 1 = f 2 := by
  rw [] -- Empty rewrite closes the goal via `rfl`
example : f 1 = f 2 := by
  rw [t] -- Closes the goal via `rfl`
example : f 1 = f 2 := by
  rw [s 1 3, s 3 4] -- Closes the goal via `rfl`

set_option allowUnsafeReducibility true
-- For the remaining tests we prevent `rfl` from closing the goal.
attribute [irreducible] f

-- Multiple rewrites
example : f 3 = f 7 := by
  rw [s 3 5, s 5 7]

-- Rewrite only modifies the main goal.
example (h : f 2 = f 3) : f 1 = f 2 := by
  rw [s 2 3, s 1 2]
  assumption

-- Rewrite `at`
example (h : f 2 = f 3) : f 1 = f 2 := by
  rw [s 2 1] at h
  rw [s 2 3]
  assumption

-- Rewriting only affects the first occurrence.
-- Providing an argument allows rewriting other occurrences.
example : [f 1, f 2] = [f 0, f 0] := by
  rw [t]
  rw [t]
  rw [t 2]

-- We can rewrite backwards.
example : f 1 = f 0 := by
  rw [← t 2]
  rw [t]
  rw [t 2]

-- Rewriting simultaneously replaces all occurrences of the first match.
example : [f 1, f 2, f 1] = [f 0, f 0, f 0] := by
  rw [t]
  rw [t 2]

-- Rewriting by lemmas with undetermined arguments creates additional goals.
example : f 2 = f 3 := by
  rewrite [s]
  rfl

-- These are often solved by the implicit `rfl` at the end of `rw`.
example : f 2 = f 3 := by
  rw [s]

-- We can rewrite at multiple locations,
-- specializing the arguments differently at each location.
-- This behaviour was accidentally broken by
-- https://github.com/leanprover/lean4/pull/2317
-- and required a revert.
example (w₁ : f 1 = 0) (w₂ : f 2 = 0) : f 3 = 0 ∧ f 0 = 0 := by
  rw [t] at w₁ w₂ ⊢
  exact ⟨w₁, w₂⟩

class P (n : Nat)

theorem t' (n : Nat) [P n] : f n = f 0 := t n

-- Rewriting uses typeclass synthesis to fill arguments.
example [∀ n, P n] : f 2 = f 0 := by
  rw [t']

example : f 2 = f 0 := by
  fail_if_success rw [t']      -- failed to synthesize P 2
  fail_if_success rw [@t' 2 _] -- failed to synthesize P 2
  -- By putting placeholders in a typeclass argument
  -- we can return the problem to the user.
  rw [@t' 2 ?_]
  constructor

/-!
Conditional theorems create side goals, and they can be discharged with a `by` clause.
-/
example (xs : List Nat) (h : xs ≠ []) : xs.head? = some xs.head! := by
  rw [List.head?_eq_head] by
    exact h
  cases xs
  · simp at h
  · rfl

/-!
Side goals are added in order.
-/
example (h : ∀ (n : Nat), 0 < n → n + 1 = 3) (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    (a + 1) + (b + 1) = 6 := by
  rw [h a, h b] by
    · exact ha
    · exact hb

/-!
Side goals are added in order in `conv` mode `rw`.
-/
example (h : ∀ (n : Nat), 0 < n → n + 1 = 3) (a b c : Nat) (ha : 0 < a) (hb : 0 < b) (hc : c = 6):
    (a + 1) + (b + 1) = c := by
  conv =>
    lhs
    rw [h a, h b] by
      · exact ha
      · exact hb
  rw [hc]

/-!
Local definitions can be unfolded and refolded.
-/
/--
trace: x y : Nat
f : Nat → Nat → Nat := fun a b => a + b
⊢ x + y = y + x
---
trace: x y : Nat
f : Nat → Nat → Nat := fun a b => a + b
⊢ f x y = y + x
-/
#guard_msgs in
example (x y : Nat) : let f (a b : Nat) := a + b; x + y = f y x := by
  intro f
  rw [f]
  trace_state
  rw [← f]
  trace_state
  rw [f, Nat.add_comm]

/-!
Local definitions defined after hypotheses can be used to refold, reordering the local context.
-/
/--
trace: x y : Nat
f : Nat → Nat → Nat := fun a b => a + b
h : f x y = 0
⊢ y + x = 0
-/
#guard_msgs in
example (x y : Nat) (h : x + y = 0) : y + x = 0 := by
  let f (a b : Nat) := a + b
  rw [← f] at h
  trace_state
  rw [Nat.add_comm, ← f]
  exact h
