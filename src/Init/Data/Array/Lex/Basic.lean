/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kim Morrison
-/
module

prelude
public import Init.Data.Array.Basic
import Init.WFTactics
import Init.Omega

public section

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace Array

/--
Compares arrays lexicographically with respect to a comparison `lt` on their elements.

Specifically, `Array.lex as bs lt` is true if
* `bs` is larger than `as` and `as` is pairwise equivalent via `==` to the initial segment of `bs`,
  or
* there is an index `i` such that `lt as[i] bs[i]`, and for all `j < i`, `as[j] == bs[j]`.
-/
@[inline, expose]
def lex [BEq α] (as bs : Array α) (lt : α → α → Bool := by exact (· < ·)) : Bool :=
  go 0
where @[specialize, semireducible] go (i : Nat) : Bool :=
  if h₁ : as.size ≤ i then
    i < bs.size
  else if h₂ : bs.size ≤ i then
    false
  else if lt as[i] bs[i] then
    true
  else if as[i] == bs[i] then
    go (i + 1)
  else
    false

end Array
