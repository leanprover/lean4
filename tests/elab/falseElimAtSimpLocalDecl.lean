def f (x : Nat) := 0

theorem ex1 (h : f x = 1) : False := by
  simp [f] at h

def g (x : Nat) := [x]

theorem ex2 (h : g x = []) : 0 = 1 := by
  simp [g] at h

theorem ex3 (x : α) (h : id x ≠ x) : 0 = 1 := by
  simp at h
