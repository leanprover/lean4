/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

prelude
import Init.Data.Array.Basic

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace Array

/-! ### getLit -/

-- auxiliary declaration used in the equation compiler when pattern matching array literals.
abbrev getLit {α : Type u} {n : Nat} (xs : Array α) (i : Nat) (h₁ : xs.size = n) (h₂ : i < n) : α :=
  have := h₁.symm ▸ h₂
  xs[i]

theorem extLit {n : Nat}
    (xs ys : Array α)
    (hsz₁ : xs.size = n) (hsz₂ : ys.size = n)
    (h : (i : Nat) → (hi : i < n) → xs.getLit i hsz₁ hi = ys.getLit i hsz₂ hi) : xs = ys :=
  Array.ext (hsz₁.trans hsz₂.symm) fun i hi₁ _ => h i (hsz₁ ▸ hi₁)

def toListLitAux (xs : Array α) (n : Nat) (hsz : xs.size = n) : ∀ (i : Nat), i ≤ xs.size → List α → List α
  | 0,     _,  acc => acc
  | (i+1), hi, acc => toListLitAux xs n hsz i (Nat.le_of_succ_le hi) (xs.getLit i hsz (Nat.lt_of_lt_of_eq (Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hi) hsz) :: acc)

def toArrayLit (xs : Array α) (n : Nat) (hsz : xs.size = n) : Array α :=
  List.toArray <| toListLitAux xs n hsz n (hsz ▸ Nat.le_refl _) []

theorem toArrayLit_eq (xs : Array α) (n : Nat) (hsz : xs.size = n) : xs = toArrayLit xs n hsz := by
  apply ext'
  simp [toArrayLit, List.toList_toArray]
  have hle : n ≤ xs.size := hsz ▸ Nat.le_refl _
  have hge : xs.size ≤ n := hsz ▸ Nat.le_refl _
  have := go n hle
  rw [List.drop_eq_nil_of_le hge] at this
  rw [this]
where
  getLit_eq (xs : Array α) (i : Nat) (h₁ : xs.size = n) (h₂ : i < n) : xs.getLit i h₁ h₂ = getElem xs.toList i ((id (α := xs.toList.length = n) h₁) ▸ h₂) :=
    rfl
  go (i : Nat) (hi : i ≤ xs.size) : toListLitAux xs n hsz i hi (xs.toList.drop i) = xs.toList := by
    induction i <;> simp only [List.drop, toListLitAux, getLit_eq, List.getElem_cons_drop_succ_eq_drop, *]

end Array
