import Std.WP

set_option sym.debug true

/-!
Tests that `vcgen` verifies `while` loops, which are implemented by `Loop.forIn` using `repeatM`,
with a `WhileInvariant` and a termination measure. This includes loops that only terminate under
a precondition on the initial value or state, loops in `Option`, and a `StateT` loop whose state
type has no `Nonempty` instance. The verification of the same loops with the deprecated `mvcgen` is
in `tests/deprecated/elab/while_extrinsic.lean`.
-/

open Std.WP

set_option experimental.vcgen true

/-- `sqrt n` computes the integer square root of `n` using a `while` loop. -/
def sqrt (n : Nat) : Id Nat := do
  if n = 0 then
    return 0
  let mut i := 0
  while i * i ≤ n do
    i := i + 1
  return i - 1

#guard Id.run (sqrt 0) == 0
#guard Id.run (sqrt 15) == 3
#guard Id.run (sqrt 16) == 4

/-- The `sqrt` function returns the correct integer square root. -/
theorem sqrt_correct :
    ⦃ True ⦄ sqrt n ⦃ fun res => res * res ≤ n ∧ n < (res + 1) * (res + 1) ⦄ := by
  vcgen [sqrt] invariants
  | inv1 => WhileInvariant.mk fun exit i =>
      (i - 1) * (i - 1) ≤ n ∧ i ≤ n + 1 ∧ (exit = true → n < i * i)
  | inv2 => .ofMeasure fun i => n + 2 - i
  all_goals try grind
  -- Invariant preservation: `i ≤ n + 1` needs `b ≤ b * b ≤ n`, which is nonlinear.
  rename_i hb
  have := Nat.le_trans (Nat.le_mul_self _) hb
  grind

/-- `sqrtState n` is the same as `sqrt` but uses `StateT`. -/
def sqrtState (n : Nat) : StateM Nat Nat := do
  set 0
  while (← get) * (← get) ≤ n do
    modify fun i => i + 1
  return (← get) - 1

/-- The `sqrtState` function returns the correct integer square root. -/
theorem sqrtState_correct :
    ⦃ fun _ => True ⦄ sqrtState n ⦃ fun res _ => res * res ≤ n ∧ n < (res + 1) * (res + 1) ⦄ := by
  vcgen [sqrtState] invariants
  | inv1 => WhileInvariant.mk fun exit _ i =>
      (i - 1) * (i - 1) ≤ n ∧ i ≤ n + 1 ∧ (exit = true → n < i * i)
  | inv2 => .ofMeasure fun _ i => n + 2 - i
  all_goals try grind
  -- Invariant preservation: `i ≤ n + 1` needs `b ≤ b * b ≤ n`, which is nonlinear.
  rename_i hb
  have := Nat.le_trans (Nat.le_mul_self _) hb
  grind

/-- A loop that only terminates when the initial value satisfies `i ≤ x`. -/
def loopWithTerminationPrecond (x : Nat) : Id Nat := do
  let mut i := 0
  while i ≠ x do
    i := i + 1
  return i

example : ⦃ True ⦄ loopWithTerminationPrecond x ⦃ fun r => r = x ⦄ := by
  vcgen [loopWithTerminationPrecond] invariants
  | inv1 => WhileInvariant.mk fun exit i => i ≤ x ∧ (exit = true → i = x)
  | inv2 => .ofMeasure fun i => x - i
  with finish

/-- A loop that only terminates when the initial *state* satisfies some invariant. -/
def loopWithStatefulTerminationPrecond (x : Nat) : StateM Nat Nat := do
  set 0
  while (← get) ≠ x do
    modify fun i => i + 1
  get

example : ⦃ fun _ => True ⦄ loopWithStatefulTerminationPrecond x ⦃ fun r _ => r = x ⦄ := by
  vcgen [loopWithStatefulTerminationPrecond] invariants
  | inv1 => WhileInvariant.mk fun exit _ s => s ≤ x ∧ (exit = true → s = x)
  | inv2 => .ofMeasure fun _ s => x - s
  with finish

/-- A loop that does not terminate for all inputs. -/
def possiblyDivergentLoop (x : Nat) : Id Nat := do
  let mut x := x
  while x ≠ 20 do
    x := x + 1
  return x

example : ⦃ x ≤ 20 ⦄ possiblyDivergentLoop x ⦃ fun r => r = 20 ⦄ := by
  vcgen [possiblyDivergentLoop] invariants
  | inv1 => WhileInvariant.mk fun exit i => i ≤ 20 ∧ (exit = true → i = 20)
  | inv2 => .ofMeasure fun i => 20 - i
  with finish

def terminatesSometimes (n : Nat) (p : Nat → Bool) : Option Nat := do
  let mut n := n
  while !p n do
    n := n + 2
  return n

example (n m : Nat) (h : n ≤ m) (heven : n % 2 = 0) (hmeven : m % 2 = 0) (h : p m) :
    ⦃ True ⦄ terminatesSometimes n p ⦃ fun r => r % 2 = 0 ⦄ := by
  vcgen [terminatesSometimes] invariants
  | inv1 => WhileInvariant.mk fun exit i => i % 2 = 0 ∧ i ≤ m ∧ (exit = true → p i)
  | inv2 => .ofMeasure fun i => m + 1 - i
  with finish

/-!
The specification for `while` works for a `StateT` even if the state doesn't have a `Nonempty`
instance.
-/

structure State where
  n : Nat

def stateWithoutNonemptyInstance : StateM State Nat := do
  while (← get).n > 0 do
    modify fun state => { n := state.n - 1 }
  return (← get).n

example : ⦃ fun _ => True ⦄ stateWithoutNonemptyInstance ⦃ fun n _ => n = 0 ⦄ := by
  vcgen [stateWithoutNonemptyInstance] invariants
  | inv1 => WhileInvariant.mk fun exit _ (s : State) => exit = true → s.n = 0
  | inv2 => .ofMeasure fun _ (s : State) => s.n
  with finish
