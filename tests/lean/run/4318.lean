/-!
# Better `calc` error messages

RFC https://github.com/leanprover/lean4/issues/4318
-/

axiom testSorry {α : Sort _} : α

/-!
Term-mode `calc`. Errors about LHS, RHS, and relation not matching expected type.
-/

/--
error: invalid 'calc' step, left-hand side is
  1 + n - n : Nat
but is expected to be
  0 : Nat
-/
#guard_msgs in
example (n : Nat) : 0 = 1 :=
  calc
    1 + n - n = 1 := testSorry

/--
error: invalid 'calc' step, right-hand side is
  n - n : Nat
but is expected to be
  1 : Nat
-/
#guard_msgs in
example (n : Nat) : 0 = 1 :=
  calc
    0 = n - n := testSorry

/--
error: 'calc' expression has type
  0 = 1 : Prop
but is expected to have type
  0 < 1 : Prop
-/
#guard_msgs in
example : 0 < 1 :=
  calc
    0 = 1 := testSorry

/-!
No postponement.
-/
/--
error: type mismatch
  h
has type
  0 = 1 : Prop
but is expected to have type
  0 < 1 : Prop
-/
#guard_msgs in
example : 0 < 1 :=
  have h := calc 0 = 1 := testSorry;
  h

/-!
Tactic-mode `calc`. LHS failure.
-/
/--
error: invalid 'calc' step, left-hand side is
  1 + n - n : Nat
but is expected to be
  0 : Nat
-/
#guard_msgs in
example (n : Nat) : 0 = 1 := by
  calc
    1 + n - n = 1 := testSorry

/-!
Tactic mode `calc`. RHS failure, but calc extension succeeds.
-/
example (n : Nat) : 0 ≤ 1 := by
  calc 0
    _ ≤ n - n := testSorry
  guard_target =ₛ n - n ≤ 1
  exact testSorry

/-!
Tactic mode `calc`. Calc extension fails, so report general failure.
-/
/--
error: 'calc' expression has type
  0 < n - n : Prop
but is expected to have type
  0 ≤ 1 : Prop
-/
#guard_msgs in
example (n : Nat) : 0 ≤ 1 := by
  calc
    0 < n - n := testSorry

/-!
Tactic mode `calc`. Relation failure and calc extension succeeds.
-/
#guard_msgs in
example : 0 < 1 := by
  calc 0
    _ ≤ 1 := testSorry
  guard_target =ₛ 1 < 1
  exact testSorry

/-!
Tactic mode `calc`. Calc extension fails, so report general failure.
-/
/--
error: 'calc' expression has type
  0 < 1 : Prop
but is expected to have type
  0 ≤ 1 : Prop
-/
#guard_msgs in
example : 0 ≤ 1 := by
  calc
    0 < 1 := testSorry
