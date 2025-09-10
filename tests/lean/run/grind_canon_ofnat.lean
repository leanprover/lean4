example : (@OfNat.ofNat (Fin (1 + 1)) 0 Fin.instOfNat) = (0 : Fin 2) := by
  grind

example {C : Type} (h : Fin 2 → C) :
    h (@OfNat.ofNat (Fin (1 + 1)) 0 Fin.instOfNat) = h 0 := by
  grind -- should work too
