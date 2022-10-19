/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
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

instance [DecidableEq α] : Membership α (Array α) where
  mem a as := as.contains a

theorem sizeOf_get_lt [SizeOf α] (as : Array α) (i : Fin as.size) : sizeOf (as.get i) < sizeOf as := by
  cases as; rename_i as
  simp [get]
  have ih := List.sizeOf_get_lt as i
  exact Nat.lt_trans ih (by simp_arith)

theorem sizeOf_lt_of_mem [DecidableEq α] [SizeOf α] {as : Array α} (h : a ∈ as) : sizeOf a < sizeOf as := by
  simp [Membership.mem, contains, any, Id.run, BEq.beq, anyM] at h
  let rec aux (j : Nat) (h : anyM.loop (m := Id) (fun b => decide (a = b)) as as.size (Nat.le_refl ..) j = true) : sizeOf a < sizeOf as := by
    unfold anyM.loop at h
    split at h
    · simp [Bind.bind, pure] at h; split at h
      next he => subst a; apply sizeOf_get_lt
      next => have ih := aux (j+1) h; assumption
    · contradiction
  apply aux 0 h
termination_by aux j _ => as.size - j

@[simp] theorem sizeOf_get [SizeOf α] (as : Array α) (i : Fin as.size) : sizeOf (as.get i) < sizeOf as := by
  cases as
  simp [get]
  apply Nat.lt_trans (List.sizeOf_get ..)
  simp_arith

/-- This tactic, added to the `decreasing_trivial` toolbox, proves that
`sizeOf arr[i] < sizeOf arr`, which is useful for well founded recursions
over a nested inductive like `inductive T | mk : Array T → T`. -/
macro "array_get_dec" : tactic =>
  `(tactic| first
    | apply sizeOf_get
    | apply Nat.lt_trans (sizeOf_get ..); simp_arith)

macro_rules | `(tactic| decreasing_trivial) => `(tactic| array_get_dec)

end Array
