module

import Std

set_option mvcgen.warning false
-- Extrinsic `Repeat.mk` expansion is only wired through the new `do` elaborator.
set_option backward.do.legacy false

open Std.Do

/-!
# Tests for extrinsic `repeat`/`while` loops

These tests verify that the new `Repeat` type and its verification infrastructure work correctly.
-/

/-- `sqrt n` computes the integer square root of `n` using a `while` loop. -/
def sqrt (n : Nat) : Id Nat := do
  if n = 0 then
    return 0
  let mut i := 0
  while i * i ≤ n
  do
    i := i + 1
  return i - 1

/-- The `sqrt` function returns the correct integer square root. -/
theorem sqrt_correct :
    ⦃⌜True⌝⦄ sqrt n ⦃⇓ res => ⌜res * res ≤ n ∧ n < (res + 1) * (res+1)⌝⦄ := by
  mvcgen [sqrt]
  invariants
  | inv1 => fun i => (n + 2) - i
  | inv2 => ⇓ cursor => match cursor with
    | .repeat i => ⌜∀ j, j < i → j * j ≤ n⌝
    | .done i => ⌜(∀ j, j < i → j * j ≤ n) ∧ n < i * i⌝
  with (try grind)
  | vc2 =>
    apply Lean.Repeat.IsPlausibleStep.wf_of_wp_measure (fun i => (n + 2) - i)
    intro r
    mvcgen with try grind
    | vc1 hsqr =>
      have : r ≤ n := Nat.le_trans (Nat.le_mul_self r) hsqr
      grind
  | vc3 =>
    rename_i b hsqr _ hinv
    intro j hj
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hlt | rfl
    · exact hinv j hlt
    · exact hsqr
  | vc6 res h =>
    have : res - 1 < res := by grind
    grind

set_option backward.do.while true in
/-- Test: `backward.do.while true` should expand to `Loop.mk`. -/
def loopBackwardCompat (n : Nat) : Nat := Id.run do
  let mut i := 0
  repeat
    if i < n then
      i := i + 1
    else
      break
  return i

-- Verify the backward-compat loop computes correctly
#guard loopBackwardCompat 5 == 5
#guard loopBackwardCompat 0 == 0

/-- Test: default setting should expand to `Repeat.mk`. -/
def loopDefault (n : Nat) : Nat := Id.run do
  let mut i := 0
  repeat
    if i < n then
      i := i + 1
    else
      break
  return i

-- Verify the default loop computes correctly
#guard loopDefault 5 == 5
#guard loopDefault 0 == 0

-- Verify sqrt computes correctly
#guard Id.run (sqrt 0) == 0
#guard Id.run (sqrt 1) == 1
#guard Id.run (sqrt 4) == 2
#guard Id.run (sqrt 8) == 2
#guard Id.run (sqrt 9) == 3
#guard Id.run (sqrt 15) == 3
#guard Id.run (sqrt 16) == 4
#guard Id.run (sqrt 100) == 10
