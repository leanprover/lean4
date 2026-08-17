import Std.WP
import Std.Tactic.Do

/-! Tests that `vcgen` names a loop's verification-condition binders after the program's own `for`
element and mutable variable rather than after the spec lemma's binders. The names stay
inaccessible, so `case vcN x y => …` keeps renaming them positionally. -/

open Std.WP Lean.Order

set_option mvcgen.warning false
set_option warn.sorry false
set_option linter.unusedVariables false

def sumEvens (xs : List Nat) : Id Nat := do
  let mut acc := 0
  for x in xs invariant _cur _suff => acc % 2 = 0 do
    acc := acc + 2 * x
  return acc

/--
trace: case vc1
xs : List Nat
acc✝ : Nat
a✝ : acc✝ % 2 = 0
⊢ ∃ k, acc✝ = 2 * k

case vc2
xs pref✝ : List Nat
x✝ : Nat
suff✝ : List Nat
_h✝ : ForIn.toList xs = pref✝ ++ x✝ :: suff✝
acc✝¹ : Nat
a✝ : acc✝¹ % 2 = 0
acc✝ : Nat := acc✝¹ + 2 * x✝
⊢ match ForInStep.yield acc✝ with
  | ForInStep.yield acc => acc % 2 = 0
  | ForInStep.done acc => acc % 2 = 0
-/
#guard_msgs in
example (xs : List Nat) : ⦃ True ⦄ (sumEvens xs : Id Nat) ⦃ fun r => ∃ k, r = 2 * k ⦄ := by
  unfold sumEvens
  vcgen
  trace_state
  all_goals sorry

-- The binders remain inaccessible, so `case vcN x y => …` renames them positionally.
example (xs : List Nat) : ⦃ True ⦄ (sumEvens xs : Id Nat) ⦃ fun r => ∃ k, r = 2 * k ⦄ := by
  unfold sumEvens
  vcgen
  case vc1 acc h => exact ⟨acc / 2, by omega⟩
  all_goals sorry

def sumRange (n : Nat) : Id Nat := do
  let mut total := 0
  for i in [0:n] invariant _cur _suff => total % 2 = 0 do
    total := total + 2 * i
  return total

/--
trace: n total✝ : Nat
a✝ : total✝ % 2 = 0
⊢ ∃ k, total✝ = 2 * k
-/
#guard_msgs in
example (n : Nat) : ⦃ True ⦄ (sumRange n : Id Nat) ⦃ fun r => ∃ k, r = 2 * k ⦄ := by
  unfold sumRange
  vcgen
  case vc1 => trace_state; sorry
  all_goals sorry

-- A membership-proof binder (`for h : x in xs`) names its binders the same way.
def sumMemEvens (xs : List Nat) : Id Nat := do
  let mut acc := 0
  for h : x in xs invariant _cur _suff => acc % 2 = 0 do
    acc := acc + 2 * x
  return acc

/--
trace: xs pref✝ : List Nat
x✝ : Nat
suff✝ : List Nat
h✝ : ForIn.toList xs = pref✝ ++ x✝ :: suff✝
acc✝¹ : Nat
a✝ : acc✝¹ % 2 = 0
acc✝ : Nat := acc✝¹ + 2 * x✝
⊢ match ForInStep.yield acc✝ with
  | ForInStep.yield acc => acc % 2 = 0
  | ForInStep.done acc => acc % 2 = 0
-/
#guard_msgs in
example (xs : List Nat) : ⦃ True ⦄ (sumMemEvens xs : Id Nat) ⦃ fun r => ∃ k, r = 2 * k ⦄ := by
  unfold sumMemEvens
  vcgen
  case vc2 => trace_state; sorry
  all_goals sorry
