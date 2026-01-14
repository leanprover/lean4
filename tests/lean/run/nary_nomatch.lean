example (x : Fin n) (h : n = 0) : False :=
  nomatch x, h

example (x : Nat) (f : Nat → Fin n) (h : n = 0 ∧ True) : False :=
  nomatch f x, h.1
