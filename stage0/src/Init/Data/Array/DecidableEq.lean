/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Array.Basic
import Init.Classical

namespace Array

theorem eq_of_isEqvAux [DecidableEq α] (a b : Array α) (hsz : a.size = b.size) (i : Nat) (hi : i ≤ a.size) (heqv : Array.isEqvAux a b hsz (fun x y => x = y) i) (j : Nat) (low : i ≤ j) (high : j < a.size) : a[j] = b[j]'(hsz ▸ high) := by
  by_cases h : i < a.size
  · unfold Array.isEqvAux at heqv
    simp [h] at heqv
    have hind := eq_of_isEqvAux a b hsz (i+1) (Nat.succ_le_of_lt h) heqv.2
    by_cases heq : i = j
    · subst heq; exact heqv.1
    · exact hind j (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne low heq)) high
  · have heq : i = a.size := Nat.le_antisymm hi (Nat.ge_of_not_lt h)
    subst heq
    exact absurd (Nat.lt_of_lt_of_le high low) (Nat.lt_irrefl j)
termination_by _ => a.size - i

theorem eq_of_isEqv [DecidableEq α] (a b : Array α) : Array.isEqv a b (fun x y => x = y) → a = b := by
  simp [Array.isEqv]
  split
  case inr => intro; contradiction
  case inl hsz =>
   intro h
   have aux := eq_of_isEqvAux a b hsz 0 (Nat.zero_le ..) h
   exact ext a b hsz fun i h _ => aux i (Nat.zero_le ..) _

theorem isEqvAux_self [DecidableEq α] (a : Array α) (i : Nat) : Array.isEqvAux a a rfl (fun x y => x = y) i = true := by
  unfold Array.isEqvAux
  split
  case inl h => simp [h, isEqvAux_self a (i+1)]
  case inr h => simp [h]
termination_by _ => a.size - i

theorem isEqv_self [DecidableEq α] (a : Array α) : Array.isEqv a a (fun x y => x = y) = true := by
  simp [isEqv, isEqvAux_self]

instance [DecidableEq α] : DecidableEq (Array α) :=
  fun a b =>
    match h:isEqv a b (fun a b => a = b) with
    | true  => isTrue (eq_of_isEqv a b h)
    | false => isFalse fun h' => by subst h'; rw [isEqv_self] at h; contradiction

end Array
