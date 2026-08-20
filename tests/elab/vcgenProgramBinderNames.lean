import Std.WP
import Std.Tactic.Do

/-! Tests that `vcgen` names a loop's verification-condition binders after the program's own `for`
element, mutable variable, and `invariant` clause binders rather than after the spec lemma's
binders. The program's variables are accessible in the verification condition; the spec lemma's
binders stay inaccessible. -/

open Std.WP Lean.Order

set_option experimental.intrinsic true
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
acc : Nat
a✝ : acc % 2 = 0
⊢ ∃ k, acc = 2 * k

case vc2
xs _cur : List Nat
x : Nat
_suff : List Nat
_h✝ : ForIn.toList xs = _cur ++ x :: _suff
acc✝ : Nat
a✝ : acc✝ % 2 = 0
acc : Nat := acc✝ + 2 * x
⊢ acc % 2 = 0
-/
#guard_msgs in
example (xs : List Nat) : ⦃ True ⦄ (sumEvens xs : Id Nat) ⦃ fun r => ∃ k, r = 2 * k ⦄ := by
  unfold sumEvens
  vcgen
  trace_state
  all_goals sorry

-- The program's variables are accessible, so the proof refers to `acc` directly.
example (xs : List Nat) : ⦃ True ⦄ (sumEvens xs : Id Nat) ⦃ fun r => ∃ k, r = 2 * k ⦄ := by
  unfold sumEvens
  vcgen
  case vc1 => exact ⟨acc / 2, by omega⟩
  all_goals sorry

def sumRange (n : Nat) : Id Nat := do
  let mut total := 0
  for i in [0:n] invariant _cur _suff => total % 2 = 0 do
    total := total + 2 * i
  return total

/--
trace: n total : Nat
a✝ : total % 2 = 0
⊢ ∃ k, total = 2 * k
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
trace: xs _cur : List Nat
x : Nat
_suff : List Nat
h✝ : ForIn.toList xs = _cur ++ x :: _suff
acc✝ : Nat
a✝ : acc✝ % 2 = 0
acc : Nat := acc✝ + 2 * x
⊢ acc % 2 = 0
-/
#guard_msgs in
example (xs : List Nat) : ⦃ True ⦄ (sumMemEvens xs : Id Nat) ⦃ fun r => ∃ k, r = 2 * k ⦄ := by
  unfold sumMemEvens
  vcgen
  case vc2 => trace_state; sorry
  all_goals sorry

/-! A clause stated as alternatives names its binders after the patterns they stand for. -/

def sumEvensAlts (xs : List Nat) : Id Nat := do
  let mut acc := 0
  for x in xs invariant | _cur, _suff => acc % 2 = 0 do
    acc := acc + 2 * x
  return acc

/--
trace: xs _cur : List Nat
x : Nat
_suff : List Nat
_h✝ : ForIn.toList xs = _cur ++ x :: _suff
acc : Nat
a✝ : acc % 2 = 0
⊢ (acc + 2 * x) % 2 = 0
-/
#guard_msgs (trace) in
example (xs : List Nat) : ⦃True⦄ sumEvensAlts xs ⦃fun r => ∃ k, r = 2 * k⦄ := by
  vcgen [sumEvensAlts]
  case vc2 => trace_state; sorry
  all_goals sorry
