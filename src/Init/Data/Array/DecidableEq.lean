/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Array.Basic
import Init.ByCases

namespace Array

theorem eq_of_isEqvAux
    [DecidableEq α] (a b : Array α) (hsz : a.size = b.size) (i : Nat) (hi : i ≤ a.size)
    (heqv : Array.isEqvAux a b hsz (fun x y => x = y) i hi)
    (j : Nat) (hj : j < i) : a[j]'(Nat.lt_of_lt_of_le hj hi) = b[j]'(Nat.lt_of_lt_of_le hj (hsz ▸ hi)) := by
  induction i with
  | zero => contradiction
  | succ i ih =>
    simp only [Array.isEqvAux, Bool.and_eq_true, decide_eq_true_eq] at heqv
    by_cases hj' : j < i
    next =>
      exact ih _ heqv.right hj'
    next =>
      replace hj' : j = i := Nat.eq_of_le_of_lt_succ (Nat.not_lt.mp hj') hj
      subst hj'
      exact heqv.left

theorem eq_of_isEqv [DecidableEq α] (a b : Array α) : Array.isEqv a b (fun x y => x = y) → a = b := by
  simp [Array.isEqv]
  split
  next hsz =>
   intro h
   have aux := eq_of_isEqvAux a b hsz a.size (Nat.le_refl ..) h
   exact ext a b hsz fun i h _ => aux i h
  next => intro; contradiction

theorem isEqvAux_self [DecidableEq α] (a : Array α) (i : Nat) (h : i ≤ a.size) :
    Array.isEqvAux a a rfl (fun x y => x = y) i h = true := by
  induction i with
  | zero => simp [Array.isEqvAux]
  | succ i ih =>
    simp_all only [isEqvAux, decide_True, Bool.and_self]

theorem isEqv_self [DecidableEq α] (a : Array α) : Array.isEqv a a (fun x y => x = y) = true := by
  simp [isEqv, isEqvAux_self]

instance [DecidableEq α] : DecidableEq (Array α) :=
  fun a b =>
    match h:isEqv a b (fun a b => a = b) with
    | true  => isTrue (eq_of_isEqv a b h)
    | false => isFalse fun h' => by subst h'; rw [isEqv_self] at h; contradiction

end Array
