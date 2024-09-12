attribute [-simp] Nat.add_left_eq_self -- This was later added to the simp set and interfere with the test.

example (a : Nat) : let n := 0; n + a = a := by
  intro n
  fail_if_success simp (config := { zeta := false })
  simp (config := { zeta := false }) [n]

/--
info: a b : Nat
h : a = b
n : Nat := 0
⊢ n + a = b
---
info: a b : Nat
h : a = b
n : Nat := 0
⊢ a = b
-/
#guard_msgs in
example (a b : Nat) (h : a = b) : let n := 0; n + a = b := by
  intro n
  fail_if_success simp (config := { zeta := false })
  trace_state
  simp (config := { zeta := false }) [n]
  trace_state
  simp [h]
