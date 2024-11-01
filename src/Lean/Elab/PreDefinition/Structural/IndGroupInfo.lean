/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
prelude
import Lean.Meta.InferType

/-!
This module contains the types
* `IndGroupInfo`, a variant of `InductiveVal` with information that
   applies to a whole group of mutual inductives and
* `IndGroupInst` which extends `IndGroupInfo` with levels and parameters
   to indicate a instantiation of the group.

One purpose of this abstraction is to make it clear when a function operates on a group as
a whole, rather than a specific inductive within the group.
-/

namespace Lean.Elab.Structural
open Lean Meta

/--
A mutually inductive group, identified by the `all` array of the `InductiveVal` of its
constituents.
-/
structure IndGroupInfo where
  all       : Array Name
  numNested : Nat
deriving BEq, Inhabited

def IndGroupInfo.ofInductiveVal (indInfo : InductiveVal) : IndGroupInfo where
  all       := indInfo.all.toArray
  numNested := indInfo.numNested

def IndGroupInfo.numMotives (group : IndGroupInfo) : Nat :=
  group.all.size + group.numNested

/-- Instantiates the right `.brecOn` or `.bInductionOn` for the given type former index,
including universe parameters and fixed prefix.  -/
partial def IndGroupInfo.brecOnName (info : IndGroupInfo) (ind : Bool) (idx : Nat) : Name :=
  if let .some n := info.all[idx]? then
      if ind then mkBInductionOnName n
      else        mkBRecOnName n
    else
      let j := idx - info.all.size + 1
      info.brecOnName ind 0 |>.appendIndexAfter j

/--
An instance of an mutually inductive group of inductives, identified by the `all` array
and the level and expressions parameters.

For example this distinguishes between `List α` and `List β` so that we will not even attempt
mutual structural recursion on such incompatible types.
-/
structure IndGroupInst extends IndGroupInfo where
  levels    : List Level
  params    : Array Expr
deriving Inhabited

def IndGroupInst.toMessageData (igi : IndGroupInst) : MessageData :=
  mkAppN (.const igi.all[0]! igi.levels) igi.params

instance : ToMessageData IndGroupInst where
  toMessageData := IndGroupInst.toMessageData

def IndGroupInst.isDefEq (igi1 igi2 : IndGroupInst) : MetaM Bool := do
  unless igi1.toIndGroupInfo == igi2.toIndGroupInfo do return false
  unless igi1.levels.length = igi2.levels.length do return false
  unless (igi1.levels.zip igi2.levels).all (fun (l₁, l₂) => Level.isEquiv l₁ l₂) do return false
  unless igi1.params.size = igi2.params.size do return false
  unless (← (igi1.params.zip igi2.params).allM (fun (e₁, e₂) => Meta.isDefEqGuarded e₁ e₂)) do return false
  return true

/-- Instantiates the right `.brecOn` or `.bInductionOn` for the given type former index,
including universe parameters and fixed prefix.  -/
def IndGroupInst.brecOn (group : IndGroupInst) (ind : Bool) (lvl : Level) (idx : Nat) : Expr :=
  let n := group.brecOnName ind idx
  let us := if ind then group.levels else lvl :: group.levels
  mkAppN (.const n us) group.params

/--
Figures out the nested type formers of an inductive group, with parameters instantiated
and indices still forall-abstracted.

For example given a nested inductive
```
inductive Tree α where | node : α → Vector (Tree α) n → Tree α
```
(where `n` is an index of `Vector`) and the instantiation `Tree Int` it will return
```
#[(n : Nat) → Vector (Tree Int) n]
```

-/
def IndGroupInst.nestedTypeFormers (igi : IndGroupInst) : MetaM (Array Expr) := do
  if igi.numNested = 0 then return #[]
  -- We extract this information from the motives of the recursor
  let recName := mkRecName igi.all[0]!
  let recInfo ← getConstInfoRec recName
  assert! recInfo.numMotives = igi.numMotives
  let aux := mkAppN (.const recName (0 :: igi.levels)) igi.params
  let motives ← inferArgumentTypesN recInfo.numMotives aux
  let auxMotives : Array Expr := motives[igi.all.size:]
  auxMotives.mapM fun motive =>
    forallTelescopeReducing motive fun xs _ => do
      assert! xs.size > 0
      mkForallFVars xs.pop (← inferType xs.back)

end Lean.Elab.Structural
