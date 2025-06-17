/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
import Init.Data.List.Nat.Perm
import all Init.Data.Array.Basic
import Init.Data.Array.Lemmas

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace Array

open List

/--
`Perm as bs` asserts that `as` and `bs` are permutations of each other.

This is a wrapper around `List.Perm`, and for now has much less API.
For more complicated verification, use `perm_iff_toList_perm` and the `List` API.
-/
structure Perm (as bs : Array α) : Prop where
  of_toList_perm ::
  toList : as.toList ~ bs.toList

@[inherit_doc] scoped infixl:50 " ~ " => Perm

theorem perm_iff_toList_perm {as bs : Array α} : as ~ bs ↔ as.toList ~ bs.toList :=
  ⟨Perm.toList, Perm.of_toList_perm⟩

end Array

namespace List

open Array

theorem perm_iff_toArray_perm {as bs : List α} : as ~ bs ↔ as.toArray ~ bs.toArray := by
  simp [perm_iff_toList_perm]

theorem Perm.of_toArray_perm {as bs : List α} : as.toArray ~ bs.toArray → as ~ bs :=
  perm_iff_toArray_perm.mpr

theorem Perm.toArray {as bs : List α} : as ~ bs → as.toArray ~ bs.toArray :=
  perm_iff_toArray_perm.mp

end List

namespace Array

open List

@[simp, refl] protected theorem Perm.refl (xs : Array α) : xs ~ xs := by
  cases xs
  simp [perm_iff_toList_perm]

protected theorem Perm.rfl {xs : Array α} : xs ~ xs := .refl _

theorem Perm.of_eq {xs ys : Array α} (h : xs = ys) : xs ~ ys := h ▸ .rfl

@[symm]
protected theorem Perm.symm {xs ys : Array α} (h : xs ~ ys) : ys ~ xs := by
  cases xs; cases ys
  simp only [perm_iff_toList_perm] at h
  simpa [perm_iff_toList_perm] using h.symm

protected theorem Perm.trans {xs ys zs : Array α} (h₁ : xs ~ ys) (h₂ : ys ~ zs) : xs ~ zs := by
  cases xs; cases ys; cases zs
  simp only [perm_iff_toList_perm] at h₁ h₂
  simpa [perm_iff_toList_perm] using h₁.trans h₂

instance : Trans (Perm (α := α)) (Perm (α := α)) (Perm (α := α)) where
  trans h₁ h₂ := Perm.trans h₁ h₂

theorem perm_comm {xs ys : Array α} : xs ~ ys ↔ ys ~ xs := ⟨Perm.symm, Perm.symm⟩

theorem Perm.size_eq {xs ys : Array α} (p : xs ~ ys) : xs.size = ys.size := by
  cases xs; cases ys
  simp only [perm_iff_toList_perm] at p
  simpa using p.length_eq

@[deprecated Perm.size_eq (since := "2025-04-17")]
abbrev Perm.length_eq := @Perm.size_eq

theorem Perm.mem_iff {a : α} {xs ys : Array α} (p : xs ~ ys) : a ∈ xs ↔ a ∈ ys := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  simp only [perm_iff_toList_perm] at p
  simpa using p.mem_iff

grind_pattern Perm.mem_iff => xs ~ ys, a ∈ xs
grind_pattern Perm.mem_iff => xs ~ ys, a ∈ ys

theorem Perm.append {xs ys as bs : Array α} (p₁ : xs ~ ys) (p₂ : as ~ bs) :
    xs ++ as ~ ys ++ bs := by
  cases xs; cases ys; cases as; cases bs
  simp only [append_toArray, perm_iff_toList_perm] at p₁ p₂ ⊢
  exact p₁.append p₂

grind_pattern Perm.append => xs ~ ys, as ~ bs, xs ++ as
grind_pattern Perm.append => xs ~ ys, as ~ bs, ys ++ bs

theorem Perm.push (x : α) {xs ys : Array α} (p : xs ~ ys) :
    xs.push x ~ ys.push x := by
  rw [push_eq_append_singleton]
  exact p.append .rfl

grind_pattern Perm.push => xs ~ ys, xs.push x
grind_pattern Perm.push => xs ~ ys, ys.push x

theorem Perm.push_comm (x y : α) {xs ys : Array α} (p : xs ~ ys) :
    (xs.push x).push y ~ (ys.push y).push x := by
  cases xs; cases ys
  simp only [perm_iff_toList_perm] at p
  simp only [push_toArray, List.append_assoc, singleton_append, perm_iff_toList_perm]
  exact p.append (Perm.swap ..)

theorem swap_perm {xs : Array α} {i j : Nat} (h₁ : i < xs.size) (h₂ : j < xs.size) :
    xs.swap i j ~ xs := by
  simp only [swap, perm_iff_toList_perm, toList_set]
  apply set_set_perm

namespace Perm

set_option linter.indexVariables false in
theorem extract {xs ys : Array α} (h : xs ~ ys) {lo hi : Nat}
    (wlo : ∀ i, i < lo → xs[i]? = ys[i]?) (whi : ∀ i, hi ≤ i → xs[i]? = ys[i]?) :
    xs.extract lo hi ~ ys.extract lo hi := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  simp_all only [perm_iff_toList_perm, List.getElem?_toArray, List.extract_toArray,
    List.extract_eq_drop_take]
  apply List.Perm.take_of_getElem? (w := fun i h => by simpa using whi (lo + i) (by omega))
  apply List.Perm.drop_of_getElem? (w := wlo)
  exact h

end Perm

end Array
