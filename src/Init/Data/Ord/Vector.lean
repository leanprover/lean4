/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Paul Reichert, Robin Arnez
-/
module

prelude
public import Init.Data.Order.Ord
public import Init.Data.Vector.Basic
import Init.Data.Vector.Lemmas

public section

/-!
# Instances for `Vector`

-/

universe u

namespace Vector

open Std

@[expose]
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

end Vector
