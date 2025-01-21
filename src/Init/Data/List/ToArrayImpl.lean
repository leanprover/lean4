/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Init.Data.List.Basic

/--
Auxiliary definition for `List.toArray`.
`List.toArrayAux as r = r ++ as.toArray`
-/
@[inline_if_reduce]
def List.toArrayAux : List α → Array α → Array α
  | nil,       r => r
  | cons a as, r => toArrayAux as (r.push a)

/-- Convert a `List α` into an `Array α`. This is O(n) in the length of the list.  -/
-- This function is exported to C, where it is called by `Array.mk`
-- (the constructor) to implement this functionality.
@[inline, match_pattern, pp_nodot, export lean_list_to_array]
def List.toArrayImpl (as : List α) : Array α :=
  as.toArrayAux (Array.mkEmpty as.length)
