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
Check that `clear_value` preserves the order of the local context.
-/
/--
trace: x : Nat
y : Nat := 23
⊢ True
-/
#guard_msgs in
example : let _x := 22; let _y := 23; True := by
  intro x y
  clear_value x
  trace_state
  trivial

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
Double `*` is not allowed.
-/
/-- error: Multiple `*` arguments provided. -/
#guard_msgs in
example : let x := 22; 0 ≤ x := by
  intro x
  clear_value * *

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
Check that `clear_value (h : x = _)` creates an equality hypothesis.
-/
/--
trace: x : Nat
h : x = 22
⊢ 0 ≤ x
-/
#guard_msgs in
example : let x := 22; 0 ≤ x := by
  intro x
  clear_value (h : x = _)
  trace_state
  rw [h]
  exact Nat.zero_le _

/-!
Can use any term that is definitionally equal to the term.
-/
/--
trace: x : Nat
h : x = 12 + 10
⊢ 0 ≤ x
-/
#guard_msgs in
example : let x := 22; 0 ≤ x := by
  intro x
  clear_value (h : x = 12 + 10)
  trace_state
  rw [h]
  exact Nat.zero_le _

/-!
There is no restriction on the value, except that it can't depend on the values being cleared.
-/
/--
trace: x : Nat
h : x = x
⊢ 0 ≤ x
-/
#guard_msgs in
example : let x := 22; 0 ≤ x := by
  intro x
  clear_value (h : x = x)
  trace_state
  rw [h]
  exact Nat.zero_le _

/-!
Failure because it depends on the value.
-/
/--
error: Tactic `clear_value` failed, the value of `x` cannot be cleared.
x : Nat := 22
h : x = 22 + ↑0
⊢ 0 ≤ x
-/
#guard_msgs in
example : let x := 22; 0 ≤ x := by
  intro x
  clear_value (h : x = 22 + (0 : Fin x))
  trace_state
  rw [h]
  exact Nat.zero_le _

/-!
Unifies the term.
-/
/--
trace: x : Nat
h : x = id 22
⊢ 0 ≤ x
-/
#guard_msgs in
example : let x := 22; 0 ≤ x := by
  intro x
  clear_value (h : x = id _)
  trace_state
  rw [h]
  exact Nat.zero_le _

/-!
Error if provided term is not defeq.
-/
/--
error: Provided term
  23
is not definitionally equal to
  x := 22
-/
#guard_msgs in
example : let x := 22; 0 ≤ x := by
  intro x
  clear_value (h : x = 23)

/-!
Error if unification does not solve all metavariables.
-/
/--
error: don't know how to synthesize placeholder for argument 'e'
context:
x : Nat := ⋯
⊢ Nat
---
error: unsolved goals
x : Nat := 22
⊢ 0 ≤ x
-/
#guard_msgs in
example : let x := 22; 0 ≤ x := by
  intro x
  clear_value (h : x = if True then _ else _)

/-!
Check `clear_value` with `_` for binder for equality hypothesis.
-/
/--
trace: x : Nat
h✝ : x = 22
⊢ 0 ≤ 22
-/
#guard_msgs in
example : let x := 22; 0 ≤ x := by
  intro x
  clear_value (_ : x = _)
  rw [‹x = 22›]
  trace_state
  exact Nat.zero_le _

/-!
Check that `clear_value` checks for type correctness.
-/
/--
error: Tactic `clear_value` failed, the value of `x` cannot be cleared.
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
error: Tactic `clear_value` failed, the value of `α` cannot be cleared.
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
Can use `*` along with `(h : x = _)`.
-/
#guard_msgs in
example : let α := Nat; let x : α := 1; @Eq α x 1 := by
  intro α x
  clear_value (h : x = _) *
  exact h

/-!
Minimized from https://github.com/leanprover-community/mathlib4/issues/25053
The issue is that `by exact k` under the binder creates a delayed assigned metavariable
```
?m : ℕ →
  let val := 22;
  val = 22 → ℕ → ℕ
```
that is applied to `val` and `val_def`. Note that this first `ℕ` corresponds to `val`,
so, despite the fact that the local context of the metavariable delayed assigned to `?m`
has `val` as a let binding, the value is still being passed in (the types are *not* ensuring
that `val` is defeq to the expected `val`!)

In this case, we can fix the issue by making sure to instantiate metavariables before running
`isTypeCorrect`.
-/
example : True := by
  let val := 22
  have val_def : val = 22 := rfl
  have : Nat.zero = (fun k => by exact k) Nat.zero := by
    clear_value val -- used to fail
    rfl
  trivial

/-!
Local context order preservation.
-/
/--
trace: x : Nat
y : Nat := 2
z : Nat := 3
⊢ x + y = x + z - 1
-/
#guard_msgs in
example : let x := 1; let y := 2; let z := 3; x + y = x + z - 1 := by
  intro x y z
  clear_value x
  trace_state
  rfl
