example (a : Nat) : let n := 0; n + a = a := by
  intro n
  fail_if_success simp (config := { zeta := false })
  simp (config := { zeta := false }) [n]

example (a b : Nat) (h : a = b) : let n := 0; n + a = b := by
  intro n
  fail_if_success simp (config := { zeta := false })
  trace_state
  simp (config := { zeta := false }) [n]
  trace_state
  simp [h]
