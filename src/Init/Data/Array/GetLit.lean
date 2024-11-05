/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

prelude
import Init.Data.Array.Basic

namespace Array

/-! ### getLit -/

-- auxiliary declaration used in the equation compiler when pattern matching array literals.
abbrev getLit {α : Type u} {n : Nat} (a : Array α) (i : Nat) (h₁ : a.size = n) (h₂ : i < n) : α :=
  have := h₁.symm ▸ h₂
  a[i]

theorem extLit {n : Nat}
    (a b : Array α)
    (hsz₁ : a.size = n) (hsz₂ : b.size = n)
    (h : (i : Nat) → (hi : i < n) → a.getLit i hsz₁ hi = b.getLit i hsz₂ hi) : a = b :=
  Array.ext a b (hsz₁.trans hsz₂.symm) fun i hi₁ _ => h i (hsz₁ ▸ hi₁)

def toListLitAux (a : Array α) (n : Nat) (hsz : a.size = n) : ∀ (i : Nat), i ≤ a.size → List α → List α
  | 0,     _,  acc => acc
  | (i+1), hi, acc => toListLitAux a n hsz i (Nat.le_of_succ_le hi) (a.getLit i hsz (Nat.lt_of_lt_of_eq (Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hi) hsz) :: acc)

def toArrayLit (a : Array α) (n : Nat) (hsz : a.size = n) : Array α :=
  List.toArray <| toListLitAux a n hsz n (hsz ▸ Nat.le_refl _) []

theorem toArrayLit_eq (as : Array α) (n : Nat) (hsz : as.size = n) : as = toArrayLit as n hsz := by
  apply ext'
  simp [toArrayLit, toList_toArray]
  have hle : n ≤ as.size := hsz ▸ Nat.le_refl _
  have hge : as.size ≤ n := hsz ▸ Nat.le_refl _
  have := go n hle
  rw [List.drop_eq_nil_of_le hge] at this
  rw [this]
where
  getLit_eq (as : Array α) (i : Nat) (h₁ : as.size = n) (h₂ : i < n) : as.getLit i h₁ h₂ = getElem as.toList i ((id (α := as.toList.length = n) h₁) ▸ h₂) :=
    rfl
  go (i : Nat) (hi : i ≤ as.size) : toListLitAux as n hsz i hi (as.toList.drop i) = as.toList := by
    induction i <;> simp only [List.drop, toListLitAux, getLit_eq, List.getElem_cons_drop_succ_eq_drop, *]

end Array
