/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Array.Basic

-- set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
-- set_option linter.indexVariables true -- Enforce naming conventions for index variables.

@[inline] def Array.insertionSort (xs : Array α) (lt : α → α → Bool := by exact (· < ·)) : Array α :=
  traverse xs 0 xs.size
where
  @[specialize] traverse (xs : Array α) (i : Nat) (fuel : Nat) : Array α :=
    match fuel with
    | 0      => xs
    | fuel+1 =>
      if h : i < xs.size then
        traverse (swapLoop xs i h) (i+1) fuel
      else
        xs
  @[specialize] swapLoop (xs : Array α) (j : Nat) (h : j < xs.size) : Array α :=
    match (generalizing := false) he:j with -- using `generalizing` because we don't want to refine the type of `h`
    | 0    => xs
    | j'+1 =>
      have h' : j' < xs.size := by subst j; exact Nat.lt_trans (Nat.lt_succ_self _) h
      if lt xs[j] xs[j'] then
        swapLoop (xs.swap j j') j' (by rw [size_swap]; assumption; done)
      else
        xs
