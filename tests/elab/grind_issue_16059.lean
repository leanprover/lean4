/-!
Regression test for #16059: `mkInjEq` must hash-cons `f⁻¹ (f a)` before internalizing it,
otherwise a later case-split branch can end up with two `ENode`s for the same term and
`mkCongrDefaultProof` panics.
-/

def g (n : Nat) (f : Fin (n + 1) → Fin (n + 1)) (x : Fin n) : Nat :=
  if (f ⟨x, by omega⟩).val < n then (f ⟨x, by omega⟩).val else (f ⟨n, by omega⟩).val

example (n : Nat) (f : Fin (n + 1) → Fin (n + 1)) (h : Function.Injective f) (x y : Fin n)
    (e : g n f x = g n f y) : x = y := by
  grind [g]
