-- Extracted from Mathlib.Data.UnionFind.
-- This file was failing in Mathlib during development of #3124.

section Mathlib.Data.UnionFind

structure UFNode (α : Type _) where
  parent : Nat
  value : α
  rank : Nat

structure UnionFind (α) where
  arr : Array (UFNode α)

-- The `PANIC` can be avoided by turning `simprocs` off:
-- set_option simprocs false

def rankMaxAux (self : UnionFind α) : ∀ (i : Nat),
    {k : Nat // ∀ j, j < i → ∀ h, self.arr[j].rank ≤ k}
  | 0 => ⟨0, fun j hj => nomatch hj⟩
  | i+1 => by
    let ⟨k, H⟩ := rankMaxAux self i
    refine ⟨max k (if h : _ then self.arr[i].rank else 0), fun j hj h ↦ ?_⟩
    match j, Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with
    | j, Or.inl hj => exact Nat.le_trans (H _ hj h) (Nat.le_max_left _ _)
    | _, Or.inr rfl => simp [h, Nat.le_max_right]
