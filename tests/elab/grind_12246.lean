import Std.Do

set_option sym.debug true

/-!
Regression test for #12246: an assertion violation in `grind`'s `mkEqProofImpl` on goals with
heterogeneous equalities between elements of different types (here `Fin m` and `Fin n`) attached
to the same theory solver. The goal is the loop-invariant preservation condition that `mvcgen`
generated for `altColSort_rowSorted'` in the original report.
-/

def Matrix' (α β γ : Type) : Type := α → β → γ

namespace Matrix'

variable {α : Type} {m n : Nat} {M : Matrix' (Fin m) (Fin n) α}

def shuffleRows (M : Matrix' (Fin m) (Fin n) α) (j : Fin n) :
    Matrix' (Fin m) (Fin n) α := sorry

def altColSort (M : Matrix' (Fin m) (Fin n) α) :
    Matrix' (Fin m) (Fin n) α := Id.run do
  let mut M' : Matrix' (Fin m) (Fin n) α := M
  for hj : j in [:n] do M' := M'.shuffleRows ⟨j, by sorry⟩
  return M'

variable [LE α] [Std.IsLinearOrder α]

def Monotone' {α : Type} [LE α] (f : Fin n → α) : Prop := ∀ i j, i ≤ j → f i ≤ f j

attribute [grind =] Fin.le_def Monotone'

theorem altColSort_rowSorted'_step (hM : ∀ i, Monotone' (M i)) (i : Fin m)
    (x : Matrix' (Fin m) (Fin n) α) (h : M.altColSort = x)
    (pref : List Nat) (cur : Nat) (suff : List Nat) (hl : [:n].toList = pref ++ cur :: suff)
    (b : Matrix' (Fin m) (Fin n) α)
    (ih : ∀ j : Fin n, j < (⟨pref, cur :: suff, hl.symm⟩ : List.Cursor [:n].toList).pos →
      Monotone' fun x => b x j) :
    ∀ j : Fin n, j < (⟨pref ++ [cur], suff, by simp [hl]⟩ : List.Cursor [:n].toList).pos →
      Monotone' fun x => b.shuffleRows ⟨cur, sorry⟩ x j := by
  fail_if_success grind -verbose
  sorry

end Matrix'
