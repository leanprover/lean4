/-!
The `Sym.simp`-based `grind` normalizer must rewrite every `Fin` literal to the form produced by
`ToExpr (Fin n)`: `@OfNat.ofNat (Fin (1 + 1)) 0 Fin.instOfNat`, with a nested numeral as value
and a ground term as type index, becomes `(0 : Fin 2)`. `grind` assumes that distinct literal
nodes denote distinct values, so the goals below were closed with a kernel-rejected proof when
the literal was left as is (see `grind_canon_ofnat`).
-/

set_option backward.grind.normalizer false

example : (@OfNat.ofNat (Fin (1 + 1)) 0 Fin.instOfNat) = (0 : Fin 2) := by grind
example {C : Type} (h : Fin 2 → C) : h (@OfNat.ofNat (Fin (1 + 1)) 0 Fin.instOfNat) = h 0 := by grind
example {C : Type} (h : Fin 2 → C) : h (@OfNat.ofNat (Fin (1 + 1)) 3 Fin.instOfNat) = h 1 := by grind
example (h : Fin 2 → Nat) : h (@OfNat.ofNat (Fin (1 + 1)) 3 Fin.instOfNat) = h 1 := by grind
