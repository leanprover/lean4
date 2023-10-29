/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Joachim Breitner
-/
prelude
import Init.Data.Array.Basic
import Init.Data.Nat.Linear
import Init.Data.List.BasicAux

theorem List.sizeOf_get_lt [SizeOf α] (as : List α) (i : Fin as.length) : sizeOf (as.get i) < sizeOf as := by
  match as, i with
  | [],    i      => apply Fin.elim0 i
  | a::as, ⟨0, _⟩ => simp_arith [get]
  | a::as, ⟨i+1, h⟩ =>
    simp [get]
    have h : i < as.length := Nat.lt_of_succ_lt_succ h
    have ih := sizeOf_get_lt as ⟨i, h⟩
    exact Nat.lt_of_lt_of_le ih (Nat.le_add_left ..)

namespace Array

/-- `a ∈ as` is a predicate which asserts that `a` is in the array `a s`. -/
-- NB: This is defined as a structure rather than a plain def so that a lemma
-- like `sizeOf_lt_of_mem` will not apply with no actual arrays around.
structure Mem (a : α) (as : Array α) : Prop where
  val : a ∈ as.data

instance : Membership α (Array α) where
  mem a as := Mem a as

theorem sizeOf_get_lt [SizeOf α] (as : Array α) (i : Fin as.size) : sizeOf (as.get i) < sizeOf as := by
  cases as with | _ as =>
  exact Nat.lt_trans (List.sizeOf_get_lt as i) (by simp_arith)

theorem sizeOf_lt_of_mem [SizeOf α] {as : Array α} (h : a ∈ as) : sizeOf a < sizeOf as := by
  cases as with | _ as =>
  exact Nat.lt_trans (List.sizeOf_lt_of_mem h.val) (by simp_arith)

@[simp] theorem sizeOf_get [SizeOf α] (as : Array α) (i : Fin as.size) : sizeOf (as.get i) < sizeOf as := by
  cases as with | _ as =>
  exact Nat.lt_trans (List.sizeOf_get ..) (by simp_arith)

/-- This tactic, added to the `decreasing_trivial` toolbox, proves that
`sizeOf arr[i] < sizeOf arr`, which is useful for well founded recursions
over a nested inductive like `inductive T | mk : Array T → T`. -/
macro "array_get_dec" : tactic =>
  `(tactic| first
    | apply sizeOf_get
    | apply Nat.lt_trans (sizeOf_get ..); simp_arith)

macro_rules | `(tactic| decreasing_trivial) => `(tactic| array_get_dec)

/-- This tactic, added to the `decreasing_trivial` toolbox, proves that `sizeOf a < sizeOf arr`
provided that `a ∈ arr` which is useful for well founded recursions over a nested inductive like
`inductive T | mk : Array T → T`. -/
-- NB: This is analogue to tactic `sizeOf_list_dec`
macro "array_mem_dec" : tactic =>
  `(tactic| first
    | apply Array.sizeOf_lt_of_mem; assumption; done
    | apply Nat.lt_trans (Array.sizeOf_lt_of_mem ?h)
      case' h => assumption
      simp_arith)

macro_rules | `(tactic| decreasing_trivial) => `(tactic| array_mem_dec)

end Array
