/-!
# Tests of the `revert` tactic
-/

/-!
Simple revert/intro test
-/
/--
trace: x y z : Nat
h1 : y = z
h3 : x = y
⊢ x = x → x = z
-/
#guard_msgs in
theorem tst1 (x y z : Nat) : y = z → x = x → x = y → x = z := by {
  intros h1 h2 h3;
  revert h2;
  trace_state;
  intro h2;
  exact Eq.trans h3 h1
}

/-!
Revert reverts dependencies too.
-/
/--
trace: x z : Nat
h2 : x = x
⊢ ∀ (y : Nat), y = z → x = y → x = z
-/
#guard_msgs in
theorem tst2 (x y z : Nat) : y = z → x = x → x = y → x = z :=
by {
  intros h1 h2 h3;
  revert y;
  trace_state;
  intros y hb ha;
  exact Eq.trans ha hb
}

/-!
Can revert a more complex term that evaluates to a hypothesis.
-/
/--
trace: x y z : Nat
a✝¹ : y = z
a✝ : x = x
⊢ x = y → x = z
-/
#guard_msgs in
theorem tst3 (x y z : Nat) : y = z → x = x → x = y → x = z := by
  intros
  revert ‹x = y›
  trace_state
  intro ha
  exact Eq.trans ha ‹y = z›

/-!
Can revert a more complex term that doesn't evaluate to a hypothesis.
This time, `a✝` itself isn't reverted.
-/
/--
trace: x y z : Nat
a✝² : y = z
a✝¹ : x = x
a✝ : x = y
⊢ x = y → x = z
-/
#guard_msgs in
theorem tst4 (x y z : Nat) : y = z → x = x → x = y → x = z := by
  intros
  revert (id ‹x = y›)
  trace_state
  intro ha
  exact Eq.trans ha ‹y = z›

/-!
Can revert other expressions.
-/
/--
trace: x y : Nat
h : x = y
⊢ x ≤ y → x ≤ y
-/
#guard_msgs in
theorem tst5 (x y : Nat) : x = y → x ≤ y := by
  intro h
  revert (Nat.le_of_eq h)
  trace_state
  exact id

/-!
New metavariables become new goals after the main one.
-/
/--
trace: x y : Nat
h : x = y
⊢ x ≤ y → x ≤ y

case c
x y : Nat
h : x = y
⊢ x ≤ y
-/
#guard_msgs in
theorem test6 (x y : Nat) : x = y → x ≤ y := by
  intro h
  revert (?c : x ≤ y)
  trace_state
  case c => exact Nat.le_of_eq h
  exact id

/-!
Unsolved natural metavariables are not allowed.
-/
/--
error: don't know how to synthesize placeholder
context:
x y : Nat
h : x = y
⊢ x ≤ y
---
error: unsolved goals
x y : Nat
h : x = y
⊢ x ≤ y
-/
#guard_msgs in
theorem test7 (x y : Nat) : x = y → x ≤ y := by
  intro h
  revert (_ : x ≤ y)
  fail "doesn't get here"
