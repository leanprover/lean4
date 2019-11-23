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

@[specialize] private partial def binInsertAux {α : Type u} {m : Type u → Type v} [Monad m] [Inhabited α]
    (lt : α → α → Bool)
    (merge : α → m α)
    (add : Unit → m α)
    (as : Array α)
    (k : α) : Nat → Nat → m (Array α)
| lo, hi =>
  -- as[lo] < k < as[hi]
  let mid    := (lo + hi)/2;
  let midVal := as.get! mid;
  if lt midVal k then
    if mid == lo then do v ← add (); pure $ as.insertAt (lo+1) v
    else binInsertAux mid hi
  else if lt k midVal then
    binInsertAux lo mid
  else do
    as.modifyM mid $ fun v => merge v

@[specialize] partial def binInsertM {α : Type u} {m : Type u → Type v} [Monad m] [Inhabited α]
    (lt : α → α → Bool)
    (merge : α → m α)
    (add : Unit → m α)
    (as : Array α)
    (k : α) : m (Array α) :=
if as.isEmpty then do v ← add (); pure $ as.push v
else if lt k (as.get! 0) then do v ← add (); pure $ as.insertAt 0 v
else if !lt (as.get! 0) k then as.modifyM 0 $ merge
else if lt as.back k then do v ← add (); pure $ as.push v
else if !lt k as.back then as.modifyM (as.size - 1) $ merge
else binInsertAux lt merge add as k 0 (as.size - 1)

@[inline] def binInsert {α : Type u} [Inhabited α] (lt : α → α → Bool) (as : Array α) (k : α) : Array α :=
Id.run $ binInsertM lt (fun _ => k) (fun _ => k) as k

end Array
