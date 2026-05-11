module

import Std

set_option mvcgen.warning false

open Std.Do

/-!
# Tests for `while` loops and `Spec.forIn_loop`

Verifies that `while`/`repeat` loops, `Spec.forIn_loop`, and the `mvcgen` `[spec]` registration
round-trip through both terminating loops (`sqrt`) and conditionally terminating loops
(`possiblyDivergentLoop`).
-/

/-- `sqrt n` computes the integer square root of `n` using a `while` loop. -/
def sqrt (n : Nat) : Id Nat := do
  if n = 0 then return 0
  let mut i := 0
  while i * i ≤ n do
    i := i + 1
  return i - 1

theorem sqrt_correct :
    ⦃⌜True⌝⦄ sqrt n ⦃⇓ res => ⌜res * res ≤ n ∧ n < (res + 1) * (res + 1)⌝⦄ := by
  mvcgen [sqrt]
  invariants
  | inv1 => fun i => (n + 2) - i
  | inv2 => fun r => match r with
    | .inl i => ∀ j, j < i → j * j ≤ n
    | .inr i => (∀ j, j < i → j * j ≤ n) ∧ n < i * i
  with try grind
  | vc2 b hcase _ =>
    intro h
    refine ⟨?_, ?_⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj'
      · exact h j hj'
      · subst hj'; exact hcase
    · have hb : b ≤ n := by
        rcases Nat.eq_zero_or_pos b with hb0 | hpos
        · omega
        · calc b ≤ b * b := Nat.le_mul_of_pos_left b hpos
            _ ≤ n := hcase
      omega
  | vc5.isFalse.post.success r =>
    intro h hn
    have hr : r ≥ 1 := by
      rcases Nat.eq_zero_or_pos r with hr0 | hr_pos
      · subst hr0; simp at hn
      · exact hr_pos
    have heq : r - 1 + 1 = r := by omega
    refine ⟨h (r - 1) (by omega), ?_⟩
    rw [heq]; exact hn

#guard Id.run (sqrt 0) == 0
#guard Id.run (sqrt 1) == 1
#guard Id.run (sqrt 4) == 2
#guard Id.run (sqrt 8) == 2
#guard Id.run (sqrt 9) == 3
#guard Id.run (sqrt 15) == 3
#guard Id.run (sqrt 16) == 4
#guard Id.run (sqrt 100) == 10

/-- A loop that does not terminate for all inputs — only for `x ≤ 20`. -/
def possiblyDivergentLoop (x : Nat) : Id Nat := do
  let mut i := x
  while i ≠ 20 do
    i := i + 1
  return i

example (hx : x ≤ 20) : ⦃⌜True⌝⦄ possiblyDivergentLoop x ⦃⇓ r => ⌜r = 20⌝⦄ := by
  mvcgen [possiblyDivergentLoop]
  invariants
  | inv1 => fun i => 20 - i
  | inv2 => fun r => match r with
    | .inl i => i ≤ 20
    | .inr i => i = 20
  with grind
