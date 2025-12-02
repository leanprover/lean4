/-
Test file for the ∎ (QED) macro which expands to `try?`
-/

import Lean.Elab.Tactic.Try

-- Basic tactic mode usage - should suggest tactics
/--
info: Try these:
  [apply] rfl
  [apply] simp
  [apply] simp only [Nat.reduceAdd]
  [apply] grind
  [apply] grind only
  [apply] simp_all
-/
#guard_msgs in
example : 1 + 1 = 2 := by
  ∎

-- Term mode usage - should suggest terms with "by"
/--
info: Try these:
  [apply] by rfl
  [apply] by simp
  [apply] by simp only [Nat.reduceAdd]
  [apply] by grind
  [apply] by grind only
  [apply] by simp_all
-/
#guard_msgs in
example : 1 + 1 = 2 :=
  ∎

-- With hypotheses in term mode
/--
info: Try these:
  [apply] by solve_by_elim
  [apply] by simp [*]
  [apply] by simp only [h]
  [apply] by grind
  [apply] by grind only
  [apply] by simp_all
-/
#guard_msgs in
example (a b : Nat) (h : a = b) : b = a :=
  ∎

-- Check that error messages are appropriate when try? fails
/--
error: Tactic `try?` failed: consider using `grind` manually, or `try? +missing` for partial proofs containing `sorry`

⊢ False
-/
#guard_msgs in
example : False := by
  ∎
