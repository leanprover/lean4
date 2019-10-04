/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.array.basic
universes u v

namespace Array
-- TODO: remove the [Inhabited α] parameters as soon as we have the tactic framework for automating proof generation and using Array.fget
-- TODO: remove `partial` using well-founded recursion

@[specialize] partial def binSearchAux {α : Type u} {β : Type v} [Inhabited α] [Inhabited β] (lt : α → α → Bool) (found : Option α → β) (as : Array α) (k : α) : Nat → Nat → β
| lo, hi =>
  if lo <= hi then
    let m := (lo + hi)/2;
    let a := as.get! m;
    if lt a k then binSearchAux (m+1) hi
    else if lt k a then
      if m == 0 then found none
      else binSearchAux lo (m-1)
    else found (some a)
  else found none

@[inline] def binSearch {α : Type} [Inhabited α] (as : Array α) (k : α) (lt : α → α → Bool) (lo := 0) (hi := as.size - 1) : Option α :=
binSearchAux lt id as k lo hi

@[inline] def binSearchContains {α : Type} [Inhabited α] (as : Array α) (k : α) (lt : α → α → Bool) (lo := 0) (hi := as.size - 1) : Bool :=
binSearchAux lt Option.isSome as k lo hi

end Array
