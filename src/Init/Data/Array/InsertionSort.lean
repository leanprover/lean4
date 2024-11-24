/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Array.Basic

@[inline] def Array.insertionSort (a : Array α) (lt : α → α → Bool := by exact (· < ·)) : Array α :=
  traverse a 0 a.size
where
  @[specialize] traverse (a : Array α) (i : Nat) (fuel : Nat) : Array α :=
    match fuel with
    | 0      => a
    | fuel+1 =>
      if h : i < a.size then
        traverse (swapLoop a i h) (i+1) fuel
      else
        a
  @[specialize] swapLoop (a : Array α) (j : Nat) (h : j < a.size) : Array α :=
    match (generalizing := false) he:j with -- using `generalizing` because we don't want to refine the type of `h`
    | 0    => a
    | j'+1 =>
      have h' : j' < a.size := by subst j; exact Nat.lt_trans (Nat.lt_succ_self _) h
      if lt a[j] a[j'] then
        swapLoop (a.swap j j') j' (by rw [size_swap]; assumption; done)
      else
        a
