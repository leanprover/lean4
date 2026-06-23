module

import Std

set_option mvcgen.warning false

open Std.Do

/-!
# Tests for `Loop`-based `repeat`/`while` loops with `repeatM`

These tests verify that the `Loop.forIn` implementation using `repeatM` and its
verification infrastructure work correctly with `MonadTail`.
-/

/-- `sqrt n` computes the integer square root of `n` using a `while` loop. -/
def sqrt (n : Nat) : Id Nat := do
  if n = 0 then
    return 0
  let mut i := 0
  while i * i ≤ n do
    i := i + 1
  return i - 1

/-- The `sqrt` function returns the correct integer square root. -/
theorem sqrt_correct :
    ⦃⌜True⌝⦄ sqrt n ⦃⇓ res => ⌜res * res ≤ n ∧ n < (res + 1) * (res+1)⌝⦄ := by
  mvcgen [sqrt]
  invariants
  | inv1 => fun i => ULift.up ((n + 2) - i)
  | inv2 => ⇓ r => match r with
    | .inl i => spred(⌜∀ j, j < i → j * j ≤ n⌝)
    | .inr i => spred(⌜∀ j, j < i → j * j ≤ n⌝ ∧ ⌜n < i * i⌝)
  with (try grind)
  | vc2 r _ hsqr _ _ =>
    have : r ≤ n := Nat.le_trans (Nat.le_mul_self r) hsqr
    grind
  | vc5 res h =>
    have : res - 1 < res := by grind
    grind

-- Verify sqrt computes correctly
#guard Id.run (sqrt 0) == 0
#guard Id.run (sqrt 1) == 1
#guard Id.run (sqrt 4) == 2
#guard Id.run (sqrt 8) == 2
#guard Id.run (sqrt 9) == 3
#guard Id.run (sqrt 15) == 3
#guard Id.run (sqrt 16) == 4
#guard Id.run (sqrt 100) == 10

/-- `sqrtState n` is the same as `sqrt` but uses `StateT`. -/
def sqrtState (n : Nat) : StateM Nat Nat := do
  set 0
  while (← get) * (← get) ≤ n do
    modify fun i => i + 1
  return (← get) - 1

/-- The `sqrtState` function returns the correct integer square root. -/
theorem sqrtState_correct :
    ⦃⌜True⌝⦄ sqrtState n ⦃⇓ res => ⌜res * res ≤ n ∧ n < (res + 1) * (res+1)⌝⦄ := by
  mvcgen [sqrtState]
  invariants
  | inv1 => fun _ i => ULift.up ((n + 2) - i)
  | inv2 => ⇓ r i => match r with
    | .inl _ => spred(⌜∀ j, j < i → j * j ≤ n⌝)
    | .inr _ => spred(⌜∀ j, j < i → j * j ≤ n⌝ ∧ ⌜n < i * i⌝)
  with (try grind)
  | vc1 r _ hsqr _ =>
    have : r ≤ n := Nat.le_trans (Nat.le_mul_self r) hsqr
    grind
  | vc4 res h =>
    have : res - 1 < res := by grind
    grind

/-- A loop that only terminates when the initial value satisfies `i ≤ x`. -/
def loopWithTerminationPrecond (x : Nat) : Id Nat := do
  let mut i := 0
  while i ≠ x do
    i := i + 1
  return i

example : ⦃⌜True⌝⦄ loopWithTerminationPrecond x ⦃⇓ r => ⌜r = x⌝⦄ := by
  mvcgen [loopWithTerminationPrecond] invariants
  | inv1 => fun i => ULift.up (x - i)
  | inv2 => ⇓ r => match r with
    | .inl i => spred(⌜i ≤ x⌝)
    | .inr i => spred(⌜i = x⌝)
  with grind

/-- A loop that only terminates when the initial *state* satisfies some invariant. -/
def loopWithStatefulTerminationPrecond (x : Nat) : StateM Nat Nat := do
  set 0
  while (← get) ≠ x do
    modify fun i => i + 1
  get

example : ⦃⌜True⌝⦄ loopWithStatefulTerminationPrecond x ⦃⇓ r => ⌜r = x⌝⦄ := by
  mvcgen [loopWithStatefulTerminationPrecond] invariants
  | inv1 => fun _ s => ULift.up (x - s)
  | inv2 => ⇓ r => match r with
    | .inl _ => spred(fun s => ⌜s ≤ x⌝)
    | .inr _ => spred(fun s => ⌜s = x⌝)
  with (try grind)

/-- A loop that does not terminate for all inputs. -/
def possiblyDivergentLoop (x : Nat) : Id Nat := do
  let mut x := x
  while x ≠ 20 do
    x := x + 1
  return x

example : ⦃⌜x ≤ 20⌝⦄ possiblyDivergentLoop x ⦃⇓ r => ⌜r = 20⌝⦄ := by
  mvcgen [possiblyDivergentLoop] invariants
  | inv1 => fun i => ULift.up (20 - i)
  | inv2 => ⇓ r => match r with
    | .inl i => spred(⌜i ≤ 20⌝)
    | .inr i => spred(⌜i = 20⌝)
  with grind

def terminatesSometimes (n : Nat) (p : Nat → Bool) :  Option Nat := do
  let mut n := n
  while !p n do
    n := n + 2
  return n

example (n m : Nat) (h : n ≤ m) (heven : n % 2 = 0) (hmeven : m % 2 = 0) (h : p m) :
    ⦃⌜True⌝⦄ terminatesSometimes n p ⦃⇓ r => ⌜r % 2 = 0⌝⦄ := by
  mvcgen [terminatesSometimes] invariants
  | inv1 => fun i => ULift.up (m + 1 - i)
  | inv2 => ⇓ r => match r with
    | .inl i => spred(⌜i % 2 = 0 ∧ i ≤ m⌝)
    | .inr i => spred(⌜i % 2 = 0 ∧ p i⌝)
  with grind
