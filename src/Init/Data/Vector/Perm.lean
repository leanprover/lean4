/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.Array.Perm
import Init.Data.Vector.Lemmas

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace Vector

open List Array

/--
`Perm as bs` asserts that `as` and `bs` are permutations of each other.

This is a wrapper around `List.Perm`, and for now has much less API.
For more complicated verification, use `perm_iff_toList_perm` and the `List` API.
-/
def Perm (as bs : Vector α n) : Prop :=
  as.toArray ~ bs.toArray

@[inherit_doc] scoped infixl:50 " ~ " => Perm

theorem perm_iff_toList_perm {as bs : Vector α n} : as ~ bs ↔ as.toList ~ bs.toList := Iff.rfl
theorem perm_iff_toArray_perm {as bs : Vector α n} : as ~ bs ↔ as.toArray ~ bs.toArray := Iff.rfl

@[simp] theorem perm_mk (as bs : Array α) (ha : as.size = n) (hb : bs.size = n) :
    mk as ha ~ mk bs hb ↔ as ~ bs := by
  simp [perm_iff_toArray_perm, ha, hb]

theorem toArray_perm_iff (xs : Vector α n) (ys : Array α) : xs.toArray ~ ys ↔ ∃ h, xs ~ Vector.mk ys h := by
  constructor
  · intro h
    refine ⟨by simp [← h.length_eq], h⟩
  · intro ⟨h, p⟩
    exact p

theorem perm_toArray_iff (xs : Array α) (ys : Vector α n) : xs ~ ys.toArray ↔ ∃ h, Vector.mk xs h ~ ys := by
  constructor
  · intro h
    refine ⟨by simp [h.length_eq], h⟩
  · intro ⟨h, p⟩
    exact p

@[simp, refl] protected theorem Perm.refl (xs : Vector α n) : xs ~ xs := by
  cases xs
  simp

protected theorem Perm.rfl {xs : List α} : xs ~ xs := .refl _

theorem Perm.of_eq {xs ys : Vector α n} (h : xs = ys) : xs ~ ys := h ▸ .rfl

protected theorem Perm.symm {xs ys : Vector α n} (h : xs ~ ys) : ys ~ xs := by
  cases xs; cases ys
  simp only [perm_mk] at h
  simpa using h.symm

protected theorem Perm.trans {xs ys zs : Vector α n} (h₁ : xs ~ ys) (h₂ : ys ~ zs) : xs ~ zs := by
  cases xs; cases ys; cases zs
  simp only [perm_mk] at h₁ h₂
  simpa using h₁.trans h₂

instance : Trans (Perm (α := α) (n := n)) (Perm (α := α) (n := n)) (Perm (α := α) (n := n)) where
  trans h₁ h₂ := Perm.trans h₁ h₂

theorem perm_comm {xs ys : Vector α n} : xs ~ ys ↔ ys ~ xs := ⟨Perm.symm, Perm.symm⟩

theorem Perm.mem_iff {a : α} {xs ys : Vector α n} (p : xs ~ ys) : a ∈ xs ↔ a ∈ ys := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  simp at p
  simpa using p.mem_iff

theorem Perm.push (x y : α) {xs ys : Vector α n} (p : xs ~ ys) :
    (xs.push x).push y ~ (ys.push y).push x := by
  rcases xs with ⟨xs, rfl⟩
  rcases ys with ⟨ys, h⟩
  simp only [perm_mk] at p
  simp only [push_mk, List.append_assoc, singleton_append, perm_toArray]
  simpa using Array.Perm.push x y p

theorem swap_perm {xs : Vector α n} {i j : Nat} (h₁ : i < n) (h₂ : j < n) :
    xs.swap i j ~ xs := by
  rcases xs with ⟨xs, rfl⟩
  simp only [swap, perm_iff_toList_perm, toList_set]
  apply set_set_perm

namespace Perm

set_option linter.indexVariables false in
theorem extract {xs ys : Vector α n} (h : xs ~ ys) {lo hi : Nat}
    (wlo : ∀ i, i < lo → xs[i]? = ys[i]?) (whi : ∀ i, hi ≤ i → xs[i]? = ys[i]?) :
    (xs.extract lo hi) ~ (ys.extract lo hi) := by
  rcases xs with ⟨xs, rfl⟩
  rcases ys with ⟨ys, h⟩
  exact Array.Perm.extract h (by simpa using wlo) (by simpa using whi)

end Perm

end Vector
