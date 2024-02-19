def foo (_ : Nat) := 10

example : foo x = 8 + 2 := by
  simp
  trace_state
  rw [foo]

example : foo x = 5 * 2 := by
  simp
  trace_state
  rw [foo]

example : foo x = 12 - 2 := by
  simp
  trace_state
  rw [foo]

example : foo x = 20 / 2 := by
  simp
  trace_state
  rw [foo]

example : foo x = 110 % 100 := by
  simp
  trace_state
  rw [foo]

example : foo x = (3+2)*2 := by
  simp
  trace_state
  rw [foo]

example : foo x * foo x = 10 ^ 2 := by
  simp
  trace_state
  rw [foo]

example : foo x = Nat.gcd 10 20 := by
  simp
  trace_state
  rw [foo]

def boo (_ : Nat) := True

example : boo x ↔ 2 < 3 := by
  simp
  trace_state
  trivial

example : boo x ↔ 3 > 2 := by
  simp
  trace_state
  trivial

example : boo x ↔ 2 ≤ 3 := by
  simp
  trace_state
  trivial

example : boo x ↔ 3 ≥ 2 := by
  simp
  trace_state
  trivial

example : foo x = 8 + 2 := by
  fail_if_success simp only
  simp only [seval]
  trace_state
  rw [foo]

example (h : x = false) : x = (3 == 4) := by
  simp
  trace_state
  assumption

example (h : x = true) : x = (3 != 4) := by
  simp
  trace_state
  assumption

example (h : ¬x) : x = (3 = 4) := by
  simp
  trace_state
  assumption

example (h : x) : x = (3 ≠ 4) := by
  simp
  trace_state
  assumption
