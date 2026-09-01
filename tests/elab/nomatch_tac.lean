example (h : Empty) : False := by
  nomatch h

example (x : Nat) (f : Nat → Fin n) (h : n = 0 ∧ True) : False := by
  nomatch f x, h.1
