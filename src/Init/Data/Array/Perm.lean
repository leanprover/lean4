/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.List.Nat.Perm
import Init.Data.Array.Lemmas

namespace Array

open List

/--
`Perm as bs` asserts that `as` and `bs` are permutations of each other.

This is a wrapper around `List.Perm`, and for now has much less API.
For more complicated verification, use `perm_iff_toList_perm` and the `List` API.
-/
def Perm (as bs : Array α) : Prop :=
  as.toList ~ bs.toList

@[inherit_doc] scoped infixl:50 " ~ " => Perm

theorem perm_iff_toList_perm {as bs : Array α} : as ~ bs ↔ as.toList ~ bs.toList := Iff.rfl

@[simp] theorem perm_toArray (as bs : List α) : as.toArray ~ bs.toArray ↔ as ~ bs := by
  simp [perm_iff_toList_perm]

@[simp, refl] protected theorem Perm.refl (l : Array α) : l ~ l := by
  cases l
  simp

protected theorem Perm.rfl {l : List α} : l ~ l := .refl _

theorem Perm.of_eq {l₁ l₂ : Array α} (h : l₁ = l₂) : l₁ ~ l₂ := h ▸ .rfl

protected theorem Perm.symm {l₁ l₂ : Array α} (h : l₁ ~ l₂) : l₂ ~ l₁ := by
  cases l₁; cases l₂
  simp only [perm_toArray] at h
  simpa using h.symm

protected theorem Perm.trans {l₁ l₂ l₃ : Array α} (h₁ : l₁ ~ l₂) (h₂ : l₂ ~ l₃) : l₁ ~ l₃ := by
  cases l₁; cases l₂; cases l₃
  simp only [perm_toArray] at h₁ h₂
  simpa using h₁.trans h₂

instance : Trans (Perm (α := α)) (Perm (α := α)) (Perm (α := α)) where
  trans h₁ h₂ := Perm.trans h₁ h₂

theorem perm_comm {l₁ l₂ : Array α} : l₁ ~ l₂ ↔ l₂ ~ l₁ := ⟨Perm.symm, Perm.symm⟩

theorem Perm.push (x y : α) {l₁ l₂ : Array α} (p : l₁ ~ l₂) :
    (l₁.push x).push y ~ (l₂.push y).push x := by
  cases l₁; cases l₂
  simp only [perm_toArray] at p
  simp only [push_toArray, List.append_assoc, singleton_append, perm_toArray]
  exact p.append (Perm.swap' _ _ Perm.nil)

theorem swap_perm {as : Array α} {i j : Nat} (h₁ : i < as.size) (h₂ : j < as.size) :
    as.swap i j ~ as := by
  simp only [swap, perm_iff_toList_perm, toList_set]
  apply set_set_perm

end Array
