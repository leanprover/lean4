/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Paul Reichert, Robin Arnez
-/
module

prelude
public import Init.Data.Order.Ord
public import Init.Data.Vector.Basic
import Init.Data.Array.Bootstrap
import Init.Data.Vector.Lemmas

public section

/-!
# Instances for `Vector`

-/

universe u

namespace Vector

open Std

@[expose, inline]
protected def compareLex {α n} (cmp : α → α → Ordering) (a b : Vector α n) : Ordering :=
  Array.compareLex cmp a.toArray b.toArray

instance {α n} [Ord α] : Ord (Vector α n) where
  compare := Vector.compareLex compare

protected theorem compareLex_eq_compareLex_toArray {α n cmp} {a b : Vector α n} :
    Vector.compareLex cmp a b = Array.compareLex cmp a.toArray b.toArray :=
  rfl

protected theorem compareLex_eq_compareLex_toList {α n cmp} {a b : Vector α n} :
    Vector.compareLex cmp a b = List.compareLex cmp a.toList b.toList :=
  Array.compareLex_eq_compareLex_toList

protected theorem compare_eq_compare_toArray {α n} [Ord α] {a b : Vector α n} :
    compare a b = compare a.toArray b.toArray :=
  rfl

protected theorem compare_eq_compare_toList {α n} [Ord α] {a b : Vector α n} :
    compare a b = compare a.toList b.toList :=
  Array.compare_eq_compare_toList

variable {α} {cmp : α → α → Ordering}

instance [ReflCmp cmp] {n} : ReflCmp (Vector.compareLex cmp (n := n)) where
  compare_self := ReflCmp.compare_self (cmp := Array.compareLex cmp)

instance [LawfulEqCmp cmp] {n} : LawfulEqCmp (Vector.compareLex cmp (n := n)) where
  eq_of_compare := by simp [Vector.compareLex_eq_compareLex_toArray]

instance [BEq α] [LawfulBEqCmp cmp] {n} : LawfulBEqCmp (Vector.compareLex cmp (n := n)) where
  compare_eq_iff_beq := by simp [Vector.compareLex_eq_compareLex_toArray,
    LawfulBEqCmp.compare_eq_iff_beq]

instance [OrientedCmp cmp] {n} : OrientedCmp (Vector.compareLex cmp (n := n)) where
  eq_swap := OrientedCmp.eq_swap (cmp := Array.compareLex cmp)

instance [TransCmp cmp] {n} : TransCmp (Vector.compareLex cmp (n := n)) where
  isLE_trans := TransCmp.isLE_trans (cmp := Array.compareLex cmp)

instance [Ord α] [ReflOrd α] {n} : ReflOrd (Vector α n) :=
  inferInstanceAs <| ReflCmp (Vector.compareLex compare)

instance [Ord α] [LawfulEqOrd α] {n} : LawfulEqOrd (Vector α n) :=
  inferInstanceAs <| LawfulEqCmp (Vector.compareLex compare)

instance [Ord α] [BEq α] [LawfulBEqOrd α] {n} : LawfulBEqOrd (Vector α n) :=
  inferInstanceAs <| LawfulBEqCmp (Vector.compareLex compare)

instance [Ord α] [OrientedOrd α] {n} : OrientedOrd (Vector α n) :=
  inferInstanceAs <| OrientedCmp (Vector.compareLex compare)

instance [Ord α] [TransOrd α] {n} : TransOrd (Vector α n) :=
  inferInstanceAs <| TransCmp (Vector.compareLex compare)

theorem compareLex_append_append {n m} {xs₁ xs₂ : Vector α n} {ys₁ ys₂ : Vector α m} :
    (xs₁ ++ ys₁).compareLex cmp (xs₂ ++ ys₂) =
      (xs₁.compareLex cmp xs₂).then (ys₁.compareLex cmp ys₂) := by
  simp only [Vector.compareLex_eq_compareLex_toArray, toArray_append]
  exact Array.compareLex_append_append_of_size_eq (by simp)

theorem compare_append_append [Ord α] {n m} {xs₁ xs₂ : Vector α n} {ys₁ ys₂ : Vector α m} :
    compare (xs₁ ++ ys₁) (xs₂ ++ ys₂) = (compare xs₁ xs₂).then (compare ys₁ ys₂) :=
  compareLex_append_append

theorem compareLex_map_map {n β} {cmp' : β → β → Ordering} (f : α → β)
    (hf : ∀ a b, cmp' (f a) (f b) = cmp a b) {xs ys : Vector α n} :
    (xs.map f).compareLex cmp' (ys.map f) = xs.compareLex cmp ys := by
  simp only [Vector.compareLex_eq_compareLex_toArray, toArray_map]
  exact Array.compareLex_map_map f hf

theorem compare_map_map [Ord α] {n β} [Ord β] (f : α → β)
    (hf : ∀ a b, compare (f a) (f b) = compare a b) {xs ys : Vector α n} :
    compare (xs.map f) (ys.map f) = compare xs ys :=
  compareLex_map_map f hf

theorem compareLex_flatMap_flatMap {n m β} {cmp' : β → β → Ordering} [LawfulEqCmp cmp]
    [LawfulEqCmp cmp'] (f : α → Vector β m) (hf : ∀ a b, (f a).compareLex cmp' (f b) = cmp a b)
    (hm : 0 < m) {xs ys : Vector α n} :
    (xs.flatMap f).compareLex cmp' (ys.flatMap f) = xs.compareLex cmp ys := by
  have hinj : ∀ a b, f a = f b → a = b := fun a b h =>
    LawfulEqCmp.eq_of_compare ((hf a b).symm.trans (h ▸ ReflCmp.compare_self))
  show Array.compareLex cmp' (xs.toArray.flatMap fun a => (f a).toArray)
    (ys.toArray.flatMap fun a => (f a).toArray) = Array.compareLex cmp xs.toArray ys.toArray
  refine Array.compareLex_flatMap_flatMap _ hf (fun a b zs h => hinj a b ?_)
    (fun a => by simpa [← Array.size_eq_zero_iff] using Nat.ne_of_gt hm)
  have : zs = #[] := by simpa [← Array.size_eq_zero_iff] using congrArg Array.size h
  simpa [this, ← toArray_inj] using h

theorem compare_flatMap_flatMap [Ord α] [LawfulEqOrd α] {n m β} [Ord β] [LawfulEqOrd β]
    (f : α → Vector β m) (hf : ∀ a b, compare (f a) (f b) = compare a b) (hm : 0 < m)
    {xs ys : Vector α n} :
    compare (xs.flatMap f) (ys.flatMap f) = compare xs ys :=
  compareLex_flatMap_flatMap f hf hm

end Vector
