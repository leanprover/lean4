/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
import all Init.Data.Array.Basic
import Init.Data.Array.Perm
import all Init.Data.Vector.Basic
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
structure Perm (as bs : Vector α n) : Prop where
  of_toArray_perm ::
  toArray : as.toArray ~ bs.toArray

@[inherit_doc] scoped infixl:50 " ~ " => Perm

theorem perm_iff_toArray_perm {as bs : Vector α n} : as ~ bs ↔ as.toArray ~ bs.toArray :=
  ⟨Perm.toArray, Perm.of_toArray_perm⟩

theorem perm_iff_toList_perm {as bs : Vector α n} : as ~ bs ↔ as.toList ~ bs.toList :=
  perm_iff_toArray_perm.trans Array.perm_iff_toList_perm

theorem Perm.of_toList_perm {as bs : Vector α n} : as.toList ~ bs.toList → as ~ bs :=
  perm_iff_toList_perm.mpr

theorem Perm.toList {as bs : Vector α n} : as ~ bs → as.toList ~ bs.toList :=
  perm_iff_toList_perm.mp

@[simp] theorem perm_mk (as bs : Array α) (ha : as.size = n) (hb : bs.size = n) :
    mk as ha ~ mk bs hb ↔ as ~ bs := by
  simp [perm_iff_toArray_perm]

theorem toArray_perm_iff (xs : Vector α n) (ys : Array α) : xs.toArray ~ ys ↔ ∃ h, xs ~ Vector.mk ys h := by
  constructor
  · intro h
    refine ⟨by simp [← h.size_eq], .of_toArray_perm h⟩
  · intro ⟨h, p⟩
    exact p.toArray

theorem perm_toArray_iff (xs : Array α) (ys : Vector α n) : xs ~ ys.toArray ↔ ∃ h, Vector.mk xs h ~ ys := by
  constructor
  · intro h
    refine ⟨by simp [h.size_eq], .of_toArray_perm h⟩
  · intro ⟨h, p⟩
    exact p.toArray

@[simp, refl] protected theorem Perm.refl (xs : Vector α n) : xs ~ xs := by
  cases xs
  simp

protected theorem Perm.rfl {xs : Vector α n} : xs ~ xs := .refl _

theorem Perm.of_eq {xs ys : Vector α n} (h : xs = ys) : xs ~ ys := h ▸ .rfl

@[symm]
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

theorem Perm.append {xs ys : Vector α m} {as bs : Vector α n}
    (p₁ : xs ~ ys) (p₂ : as ~ bs) : xs ++ as ~ ys ++ bs := by
  cases xs; cases ys; cases as; cases bs
  simp only [perm_mk, mk_append_mk] at p₁ p₂ ⊢
  exact p₁.append p₂

theorem Perm.push (x : α) {xs ys : Vector α n} (p : xs ~ ys) :
    xs.push x ~ ys.push x := by
  cases xs; cases ys
  simp only [perm_mk, push_mk] at p ⊢
  exact p.push x

theorem Perm.push_comm (x y : α) {xs ys : Vector α n} (p : xs ~ ys) :
    (xs.push x).push y ~ (ys.push y).push x := by
  rcases xs with ⟨xs, rfl⟩
  rcases ys with ⟨ys, h⟩
  simp only [perm_mk, push_mk] at p ⊢
  simpa using p.push_comm x y

theorem swap_perm {xs : Vector α n} {i j : Nat} (h₁ : i < n) (h₂ : j < n) :
    xs.swap i j ~ xs := by
  rcases xs with ⟨xs, rfl⟩
  simp only [swap, perm_iff_toList_perm]
  apply set_set_perm

namespace Perm

set_option linter.indexVariables false in
theorem extract {xs ys : Vector α n} (h : xs ~ ys) {lo hi : Nat}
    (wlo : ∀ i, i < lo → xs[i]? = ys[i]?) (whi : ∀ i, hi ≤ i → xs[i]? = ys[i]?) :
    xs.extract lo hi ~ ys.extract lo hi := by
  rcases xs with ⟨xs, rfl⟩
  rcases ys with ⟨ys, h⟩
  exact ⟨Array.Perm.extract h.toArray (by simpa using wlo) (by simpa using whi)⟩

end Perm

end Vector
