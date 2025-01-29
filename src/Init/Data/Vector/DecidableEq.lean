/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.Array.DecidableEq
import Init.Data.Vector.Lemmas

namespace Vector

theorem isEqv_iff_rel {a b : Vector α n} {r} :
    Vector.isEqv a b r ↔ ∀ (i : Nat) (h' : i < n), r a[i] b[i] := by
  rcases a with ⟨a, rfl⟩
  rcases b with ⟨b, h⟩
  simp [Array.isEqv_iff_rel, h]

theorem isEqv_eq_decide (a b : Vector α n) (r) :
    Vector.isEqv a b r = decide (∀ (i : Nat) (h' : i < n), r a[i] b[i]) := by
  rcases a with ⟨a, rfl⟩
  rcases b with ⟨b, h⟩
  simp [Array.isEqv_eq_decide, h]

@[simp] theorem isEqv_toArray [BEq α] (a b : Vector α n) : (a.toArray.isEqv b.toArray r) = (a.isEqv b r) := by
  simp [isEqv_eq_decide, Array.isEqv_eq_decide]

theorem eq_of_isEqv [DecidableEq α] (a b : Vector α n) (h : Vector.isEqv a b (fun x y => x = y)) : a = b := by
  rcases a with ⟨a, rfl⟩
  rcases b with ⟨b, h⟩
  rw [← Vector.toArray_inj]
  apply Array.eq_of_isEqv
  simp_all

theorem isEqv_self_beq [BEq α] [ReflBEq α] (a : Vector α n) : Vector.isEqv a a (· == ·) = true := by
  rcases a with ⟨a, rfl⟩
  simp [Array.isEqv_self_beq]

theorem isEqv_self [DecidableEq α] (a : Vector α n) : Vector.isEqv a a (· = ·) = true := by
  rcases a with ⟨a, rfl⟩
  simp [Array.isEqv_self]

instance [DecidableEq α] : DecidableEq (Vector α n) :=
  fun a b =>
    match h:isEqv a b (fun a b => a = b) with
    | true  => isTrue (eq_of_isEqv a b h)
    | false => isFalse fun h' => by subst h'; rw [isEqv_self] at h; contradiction

theorem beq_eq_decide [BEq α] (a b : Vector α n) :
    (a == b) = decide (∀ (i : Nat) (h' : i < n), a[i] == b[i]) := by
  simp [BEq.beq, isEqv_eq_decide]

@[simp] theorem beq_toArray [BEq α] (a b : Vector α n) : (a.toArray == b.toArray) = (a == b) := by
  simp [beq_eq_decide, Array.beq_eq_decide]

@[simp] theorem beq_toList [BEq α] (a b : Vector α n) : (a.toList == b.toList) = (a == b) := by
  simp [beq_eq_decide, List.beq_eq_decide]

end Vector
