/-!
`grind` injection step does not fail at `clear`.
-/

example (n m : Nat) (a : Fin n) (b : Fin m) (h : ∃ h : [n] = [m], (List.cons.inj h).1 ▸ a = b) :
    (List.cons.inj h.1).1 ▸ a = b := by
  grind
