def foo (_ : Nat) := (10 : UInt32)

example (h : x = 8) : x = (8 : UInt32).toNat := by
  simp
  trace_state
  assumption

example (h : x = 8) : x = UInt32.ofNatLT 8 (by decide) := by
  simp
  trace_state
  assumption

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


def boo (_ : Nat) := True

example : boo x ↔ (2 : UInt32) < 3 := by
  simp
  trace_state
  trivial

example : boo x ↔ (3 : UInt32) > 2 := by
  simp
  trace_state
  trivial

example : boo x ↔ (2 : UInt32) ≤ 3 := by
  simp
  trace_state
  trivial

example : boo x ↔ (3 : UInt32) ≥ 2 := by
  simp
  trace_state
  trivial

example (h : x = false) : x = ((3 : UInt32) == 4) := by
  simp
  trace_state
  assumption

example (h : x = true) : x = ((3 : UInt32) != 4) := by
  simp
  trace_state
  assumption

example (h : ¬x) : x = ((3 : UInt32) = 4) := by
  simp
  trace_state
  assumption

example (h : x) : x = ((3 : UInt32) ≠ 4) := by
  simp
  trace_state
  assumption
