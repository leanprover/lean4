/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Init.Data.Array.DecidableEq
public import Init.Data.Vector.Lemmas

public section

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace Vector

theorem isEqv_iff_rel {xs ys : Vector α n} {r} :
    Vector.isEqv xs ys r ↔ ∀ (i : Nat) (h' : i < n), r xs[i] ys[i] := by
  rcases xs with ⟨xs, rfl⟩
  rcases ys with ⟨ys, h⟩
  simp [Array.isEqv_iff_rel, h]

theorem isEqv_eq_decide (xs ys : Vector α n) (r) :
    Vector.isEqv xs ys r = decide (∀ (i : Nat) (h' : i < n), r xs[i] ys[i]) := by
  rcases xs with ⟨xs, rfl⟩
  rcases ys with ⟨ys, h⟩
  simp [Array.isEqv_eq_decide, h]

@[simp] theorem isEqv_toArray [BEq α] (xs ys : Vector α n) : (xs.toArray.isEqv ys.toArray r) = (xs.isEqv ys r) := by
  simp [isEqv_eq_decide, Array.isEqv_eq_decide]

theorem eq_of_isEqv [DecidableEq α] (xs ys : Vector α n) (h : Vector.isEqv xs ys (fun x y => x = y)) : xs = ys := by
  rcases xs with ⟨xs, rfl⟩
  rcases ys with ⟨ys, h⟩
  rw [← Vector.toArray_inj]
  apply Array.eq_of_isEqv
  simp_all

theorem isEqv_self_beq [BEq α] [ReflBEq α] (xs : Vector α n) : Vector.isEqv xs xs (· == ·) = true := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.isEqv_self_beq]

theorem isEqv_self [DecidableEq α] (xs : Vector α n) : Vector.isEqv xs xs (· = ·) = true := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.isEqv_self]

theorem beq_eq_decide [BEq α] (xs ys : Vector α n) :
    (xs == ys) = decide (∀ (i : Nat) (h' : i < n), xs[i] == ys[i]) := by
  simp [BEq.beq, isEqv_eq_decide]

@[deprecated mk_beq_mk (since := "2025-05-26")]
theorem beq_mk [BEq α] (xs ys : Array α) (ha : xs.size = n) (hb : ys.size = n) :
    (mk xs ha == mk ys hb) = (xs == ys) := by
  simp

@[deprecated toArray_beq_toArray (since := "2025-05-26")]
theorem beq_toArray [BEq α] (xs ys : Vector α n) : (xs.toArray == ys.toArray) = (xs == ys) := by
  simp

@[deprecated toList_beq_toList (since := "2025-05-26")]
theorem beq_toList [BEq α] (xs ys : Vector α n) : (xs.toList == ys.toList) = (xs == ys) := by
  simp

instance [BEq α] [ReflBEq α] : ReflBEq (Vector α n) where
  rfl := by simp [BEq.beq, isEqv_self_beq]

instance [BEq α] [LawfulBEq α] : LawfulBEq (Vector α n) where
  eq_of_beq := by
    rintro ⟨xs, rfl⟩ ⟨ys, h⟩ h'
    simpa using h'

end Vector
