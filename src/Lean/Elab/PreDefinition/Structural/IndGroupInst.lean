/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
prelude
import Lean.Elab.PreDefinition.Structural.Basic
import Lean.Meta.InferType

namespace Lean.Elab.Structural
open Lean Meta

/--
An instance of an mutually inductive group of inductives, identified by the `all` array
and the level and expressions parameters.

For example this distinguishes between `List α` and `List β` and we will not even attempt
mutual structural recursion on such incompatible types.
-/
structure IndGroupInst where
  all       : Array Name
  levels    : List Level
  params    : Array Expr
  numNested : Nat


def IndGroupInst.ofRecArgInfo (recArgInfo : RecArgInfo) : IndGroupInst :=
  { all := recArgInfo.indAll
    levels := recArgInfo.indLevels
    params := recArgInfo.indParams
    numNested := recArgInfo.indNumNested
  }

def IndGroupInst.toMessageData (igi : IndGroupInst) : MessageData :=
  mkAppN (.const igi.all[0]! igi.levels) igi.params

instance : ToMessageData IndGroupInst where
  toMessageData := IndGroupInst.toMessageData

def IndGroupInst.numMotives (igi : IndGroupInst) : Nat :=
  igi.all.size + igi.numNested

def IndGroupInst.isDefEq (igi1 igi2 : IndGroupInst) : MetaM Bool := do
  unless igi1.all[0]! = igi2.all[0]! do return false
  unless igi1.levels.length = igi2.levels.length do return false
  unless (igi1.levels.zip igi2.levels).all (fun (l₁, l₂) => Level.isEquiv l₁ l₂) do return false
  unless igi1.params.size = igi2.params.size do return false
  unless (← (igi1.params.zip igi2.params).allM (fun (e₁, e₂) => Meta.isDefEqGuarded e₁ e₂)) do return false
  return true

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
