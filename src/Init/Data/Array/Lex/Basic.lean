/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kim Morrison
-/
prelude
import Init.Data.Array.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Range

namespace Array

/--
Lexicographic comparator for arrays.

`lex as bs lt` is true if
- `bs` is larger than `as` and `as` is pairwise equivalent via `==` to the initial segment of `bs`, or
- there is an index `i` such that `lt as[i] bs[i]`, and for all `j < i`, `as[j] == bs[j]`.
-/
def lex [BEq α] (as bs : Array α) (lt : α → α → Bool := by exact (· < ·)) : Bool := Id.run do
  for h : i in [0 : min as.size bs.size] do
    -- TODO: `omega` should be able to find this itself.
    have : i < min as.size bs.size := Membership.get_elem_helper h rfl
    if lt as[i] bs[i] then
      return true
    else if as[i] != bs[i] then
      return false
  return as.size < bs.size

end Array
