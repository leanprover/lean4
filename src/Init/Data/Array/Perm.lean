/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.List.Nat.Perm
import Init.Data.Array.Lemmas

-- set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
-- set_option linter.indexVariables true -- Enforce naming conventions for index variables.

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

@[simp, refl] protected theorem Perm.refl (xs : Array α) : xs ~ xs := by
  cases xs
  simp

protected theorem Perm.rfl {xs : List α} : xs ~ xs := .refl _

theorem Perm.of_eq {xs ys : Array α} (h : xs = ys) : xs ~ ys := h ▸ .rfl

protected theorem Perm.symm {xs ys : Array α} (h : xs ~ ys) : ys ~ xs := by
  cases xs; cases ys
  simp only [perm_toArray] at h
  simpa using h.symm

protected theorem Perm.trans {xs ys zs : Array α} (h₁ : xs ~ ys) (h₂ : ys ~ zs) : xs ~ zs := by
  cases xs; cases ys; cases zs
  simp only [perm_toArray] at h₁ h₂
  simpa using h₁.trans h₂

instance : Trans (Perm (α := α)) (Perm (α := α)) (Perm (α := α)) where
  trans h₁ h₂ := Perm.trans h₁ h₂

theorem perm_comm {xs ys : Array α} : xs ~ ys ↔ ys ~ xs := ⟨Perm.symm, Perm.symm⟩

theorem Perm.push (x y : α) {xs ys : Array α} (p : xs ~ ys) :
    (xs.push x).push y ~ (ys.push y).push x := by
  cases xs; cases ys
  simp only [perm_toArray] at p
  simp only [push_toArray, List.append_assoc, singleton_append, perm_toArray]
  exact p.append (Perm.swap' _ _ Perm.nil)

theorem swap_perm {xs : Array α} {i j : Nat} (h₁ : i < xs.size) (h₂ : j < xs.size) :
    xs.swap i j ~ xs := by
  simp only [swap, perm_iff_toList_perm, toList_set]
  apply set_set_perm

end Array
