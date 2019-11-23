/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Array.Basic
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

@[specialize] partial def binInsertAuxAux {α : Type u} [Inhabited α]
    (lt : α → α → Bool)
    (merge : α → α)
    (add : Unit → α)
    (as : Array α)
    (k : α) : Nat → Nat → Array α
| lo, hi =>
  -- as[lo] < k < as[hi]
  let m := (lo + hi)/2;
  if lt (as.get! m) k then
    if m == lo then as.insertAt (lo+1) (add ())
    else binInsertAuxAux m hi
  else if lt k (as.get! m) then
    binInsertAuxAux lo m
  else
    as.modify m $ fun a => merge a

@[specialize] partial def binInsertAux {α : Type u} [Inhabited α]
    (lt : α → α → Bool)
    (merge : α → α)
    (add : Unit → α)
    (as : Array α)
    (k : α) : Array α :=
if as.isEmpty then as.push (add ())
else if lt k (as.get! 0) then as.insertAt 0 (add ())
else if !lt (as.get! 0) k then as.modify 0 $ fun a => merge a
else if lt as.back k then as.push (add ())
else if !lt k as.back then as.modify (as.size - 1) $ fun a => merge a
else binInsertAuxAux lt merge add as k 0 (as.size - 1)

@[inline] def binInsert {α : Type u} [Inhabited α] (lt : α → α → Bool) (as : Array α) (k : α) : Array α :=
binInsertAux lt (fun _ => k) (fun _ => k) as k

end Array
