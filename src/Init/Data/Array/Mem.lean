/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Joachim Breitner
-/
module

prelude
public import Init.Data.Array.Basic
public import Init.Data.Nat.Linear
public import Init.Data.List.BasicAux

public section

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace Array

theorem sizeOf_lt_of_mem [SizeOf α] {as : Array α} (h : a ∈ as) : sizeOf a < sizeOf as := by
  cases as with | _ as
  exact Nat.lt_trans (List.sizeOf_lt_of_mem h.val) (by simp +arith)

theorem sizeOf_get [SizeOf α] (as : Array α) (i : Nat) (h : i < as.size) : sizeOf as[i] < sizeOf as := by
  cases as with | _ as
  simpa using Nat.lt_trans (List.sizeOf_get _ ⟨i, h⟩) (by simp +arith)

@[simp] theorem sizeOf_getElem [SizeOf α] (as : Array α) (i : Nat) (h : i < as.size) :
  sizeOf (as[i]'h) < sizeOf as := sizeOf_get _ _ h

/-- This tactic, added to the `decreasing_trivial` toolbox, proves that
`sizeOf arr[i] < sizeOf arr`, which is useful for well founded recursions
over a nested inductive like `inductive T | mk : Array T → T`. -/
macro "array_get_dec" : tactic =>
  `(tactic| first
    -- subsumed by simp
    -- | with_reducible apply sizeOf_get
    -- | with_reducible apply sizeOf_getElem
    | (with_reducible apply Nat.lt_of_lt_of_le (sizeOf_get ..)); simp +arith
    | (with_reducible apply Nat.lt_of_lt_of_le (sizeOf_getElem ..)); simp +arith
    )

macro_rules | `(tactic| decreasing_trivial) => `(tactic| array_get_dec)

/-- This tactic, added to the `decreasing_trivial` toolbox, proves that `sizeOf a < sizeOf arr`
provided that `a ∈ arr` which is useful for well founded recursions over a nested inductive like
`inductive T | mk : Array T → T`. -/
-- NB: This is analogue to tactic `sizeOf_list_dec`
macro "array_mem_dec" : tactic =>
  `(tactic| first
    | with_reducible apply Array.sizeOf_lt_of_mem; assumption; done
    | with_reducible
        apply Nat.lt_of_lt_of_le (Array.sizeOf_lt_of_mem ?h)
        case' h => assumption
      simp +arith)

macro_rules | `(tactic| decreasing_trivial) => `(tactic| array_mem_dec)

end Array
