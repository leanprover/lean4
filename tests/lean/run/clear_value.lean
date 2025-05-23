/-!
# Tests for `clear_value` tactic
-/

/-!
Check that `clear_value` clears the value.
-/
/--
trace: x : Nat
⊢ 0 ≤ x
-/
#guard_msgs in
example : let x := 22; 0 ≤ x := by
  intro x
  clear_value x
  trace_state
  exact Nat.zero_le _

/-!
Test `*` mode.
-/
/--
trace: x : Nat
⊢ 0 ≤ x
-/
#guard_msgs in
example : let x := 22; 0 ≤ x := by
  intro x
  clear_value *
  trace_state
  exact Nat.zero_le _

/-!
Check that `clear_value` fails if there is no value to clear.
-/
/-- error: Hypothesis `x` is not a local definition. -/
#guard_msgs in
example (x : Nat) : 0 ≤ x := by
  clear_value x

/-!
Check that `clear_value *` fails if it does nothing.
-/
/--
error: Tactic `clear_value` failed to clear any values.
x : Nat
⊢ 0 ≤ x
-/
#guard_msgs in
example (x : Nat) : 0 ≤ x := by
  clear_value *

/-!
Check for validation that hypotheses aren't mentioned multiple times.
-/
/-- error: Hypothesis `x` appears multiple times. -/
#guard_msgs in
example : let x := 22; 0 ≤ x := by
  intro x
  clear_value x x

/-!
Check that `clear_value ... with` creates an equality hypothesis.
-/
/--
trace: x : Nat
h : x = 22
⊢ 0 ≤ 22
-/
#guard_msgs in
example : let x := 22; 0 ≤ x := by
  intro x
  clear_value x with h
  rw [h]
  trace_state
  exact Nat.zero_le _

/-!
Check `clear_value ... with` with `_`.
-/
/--
trace: x : Nat
h✝ : x = 22
⊢ 0 ≤ 22
-/
#guard_msgs in
example : let x := 22; 0 ≤ x := by
  intro x
  clear_value x with _
  rw [‹x = 22›]
  trace_state
  exact Nat.zero_le _

/-!
Check `clear_value ... with` with too many `with` binders.
-/
/-- error: Too many binders provided. -/
#guard_msgs in
example : let x := 22; 0 ≤ x := by
  intro x
  clear_value x with h1 h2

/-!
Check that `clear_value` checks for type correctness.
-/
/--
error: Tactic `clear_value` could not clear value of `x`.
x : Nat := 22
y : Fin x := 0
⊢ ↑y < x
-/
#guard_msgs in
example : let x := 22; let y : Fin x := 0; y.1 < x := by
  intro x y
  clear_value x

/-!
Even though we cannot clear `x` on its own, we can clear it if we clear `y` first.
-/
/--
trace: x : Nat
y : Fin x
⊢ ↑y < x
-/
#guard_msgs in
example : let x := 22; let y : Fin x := 0; y.1 < x := by
  intro x y
  clear_value y
  clear_value x
  trace_state
  exact y.2

/-!
We can clear the values `x` and `y` in any order.
-/
/--
trace: x : Nat
y : Fin x
⊢ ↑y < x
-/
#guard_msgs in
example : let x := 22; let y : Fin x := 0; y.1 < x := by
  intro x y
  clear_value y x
  trace_state
  exact y.2
/--
trace: x : Nat
y : Fin x
⊢ ↑y < x
-/
#guard_msgs in
example : let x := 22; let y : Fin x := 0; y.1 < x := by
  intro x y
  clear_value x y
  trace_state
  exact y.2

/-!
Clearing `x` on its own and `y` on its own are OK because `y + 1` is nonzero.
-/
/--
trace: x y : Nat
z : Fin (y + 1) := 0
⊢ ↑z < y + 1
-/
#guard_msgs in
example : let x := 22; let y : Nat := x; let z : Fin (y + 1) := 0; z.1 < y + 1 := by
  intro x y z
  clear_value x
  clear_value y
  trace_state
  exact z.2

/-!
Dependence, `clear_value` fails.
-/
/--
error: Tactic `clear_value` could not clear value of `α`.
α : Type := Nat
x : α := 1
⊢ x = x
-/
#guard_msgs in
example : let α := Nat; let x : α := 1; @Eq α x x := by
  intro α x
  clear_value α

/-!
`clear_value *` manages to clear `x` but not `α`
-/
/--
trace: α : Type := Nat
x : α
⊢ x = 1
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : let α := Nat; let x : α := 1; @Eq α x 1 := by
  intro α x
  clear_value *
  trace_state
  sorry

/-!
`clear_value *` fails if `x` is already cleared
-/
/--
error: Tactic `clear_value` failed to clear any values.
α : Type := Nat
x : α
⊢ x = 1
-/
#guard_msgs in
example : let α := Nat; let x : α := 1; @Eq α x 1 := by
  intro α x
  clear_value x
  clear_value *

/-!
Can use `with` clause with `*` so long as it's paired with a local.
-/
#guard_msgs in
example : let α := Nat; let x : α := 1; @Eq α x 1 := by
  intro α x
  clear_value x * with h
  exact h

/-!
Can't use `with` with `*` directly.
-/
/-- error: When using `*`, no binder may be provided for it. -/
#guard_msgs in
example : let α := Nat; let x : α := 1; @Eq α x 1 := by
  intro α x
  clear_value * with h
  exact h
