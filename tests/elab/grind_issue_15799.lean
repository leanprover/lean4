/-!
Regression test for #15799: an equivalence class merged via `HEq` (e.g., through `cast` terms)
contains terms of different types, such as `Fin n` and `Fin m`. Solvers must be notified of
equalities and disequalities using their terms of the right type: `grind` used to pass a term
of the wrong type (internal error in `mkEqProof`), or to drop the equality altogether.
-/

theorem test {n m : Nat} (c : Nat → Nat) (e : n = m) (k₁ k₂ : Fin (c n)) : e ▸ k₁ = e ▸ k₂ → k₁ = k₂ := by
  grind

theorem test2 {n m : Nat} (e : n = m) (k₁ k₂ : Fin n) : e ▸ k₁ = e ▸ k₂ → k₁ = k₂ := by
  grind

example {n m : Nat} (e : n = m) (k₁ k₂ : Fin n) : e ▸ k₁ = e ▸ k₂ → k₁ = k₂ := by
  grind only

example {n m : Nat} (e : n = m) (k₁ k₂ : BitVec n) : e ▸ k₁ = e ▸ k₂ → k₁ = k₂ := by
  grind

/-!
`b : BitVec m` is a ring term in the class of `a : BitVec n`. The ring solver must still learn
`a = c` when `c : BitVec n` joins the class. `h₀` and `h₁` are not used by the final proof,
but create this situation.
-/

example {n m : Nat} (e : n = m) (a c x y : BitVec n) (b z w : BitVec m)
    (h₀ : z + b = w) (h₁ : e ▸ a = b) (h₂ : x + a = 0) (h₃ : y + c = 0) (h₄ : a = c) : x = y := by
  grind -hom -lia -linarith -ac

example {n m : Nat} (e : n = m) (a c x y : BitVec n) (b z w : BitVec m)
    (h₀ : z + b = w) (h₁ : e ▸ a = b) (h₂ : x + a = 0) (h₃ : y + c = 0) (h₄ : a = c) : x = y := by
  grind

example {n m : Nat} (e : n = m) (a c x y : BitVec n) (b z w : BitVec m)
    (h₀ : z + b = w) (h₄ : a = c) (h₁ : e ▸ a = b) (h₂ : x + a = 0) (h₃ : y + c = 0) : x = y := by
  grind -hom -lia -linarith -ac
