/-
Copyright (c) 2024 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.List.Count
import Init.Data.Nat.Lemmas

namespace List

open Nat

theorem countP_set (p : α → Bool) (l : List α) (i : Nat) (a : α) (h : i < l.length) :
    (l.set i a).countP p = l.countP p - (if p l[i] then 1 else 0) + (if p a then 1 else 0) := by
  induction l generalizing i with
  | nil => simp at h
  | cons x l ih =>
    cases i with
    | zero => simp [countP_cons]
    | succ i =>
      simp [add_one_lt_add_one_iff] at h
      simp [countP_cons, ih _ h]
      have : (if p l[i] = true then 1 else 0) ≤ l.countP p := boole_getElem_le_countP p l i h
      omega

theorem count_set [BEq α] (a b : α) (l : List α) (i : Nat) (h : i < l.length) :
    (l.set i a).count b = l.count b - (if l[i] == b then 1 else 0) + (if a == b then 1 else 0) := by
  simp [count_eq_countP, countP_set, h]

end List
