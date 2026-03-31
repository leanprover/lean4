attribute [-simp] Nat.add_eq_right -- This was later added to the simp set and interfere with the test.

example (a : Nat) : let n := 0; n + a = a := by
  intro n
  fail_if_success simp (config := { zeta := false })
  simp (config := { zeta := false }) [n]

/--
trace: a b : Nat
h : a = b
n : Nat := 0
⊢ n + a = b
---
trace: a b : Nat
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
