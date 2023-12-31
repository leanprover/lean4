def foo (_ : Nat) : Fin 32 := 10

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

example : foo x - 3 = 17 % 10 := by
  simp
  trace_state
  simp [foo]

example : foo x = (3+2)*2 := by
  simp
  trace_state
  rw [foo]

def boo (_ : Nat) := True

example : boo x ↔ (2 : Fin 8) < 3 := by
  simp
  trace_state
  trivial

example : boo x ↔ (3 : Fin 8) > 2 := by
  simp
  trace_state
  trivial

example : boo x ↔ (2 : Fin 8) ≤ 3 := by
  simp
  trace_state
  trivial

example : boo x ↔ (3 : Fin 8) ≥ 2 := by
  simp
  trace_state
  trivial
