/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Order.Types
import Lean.Meta.Tactic.Grind.OrderInsts
import Lean.Meta.Tactic.Grind.Arith.CommRing.RingId
import Lean.Meta.Tactic.Grind.Arith.CommRing.NonCommRingM
public section
namespace Lean.Meta.Grind.Order

private def preprocess (e : Expr) : GoalM Expr := do
  shareCommon (← canon e)

private def internalizeFn (fn : Expr) : GoalM Expr := do
  preprocess fn

private def getInst? (declName : Name) (u : Level) (type : Expr) : GoalM (Option Expr) := do
  synthInstance? <| mkApp (mkConst declName [u]) type

open Arith CommRing

private def mkOrderedRingInst? (u : Level) (α : Expr) (semiringInst : Expr)
    (leInst ltInst isPreorderInst : Expr) : GoalM (Option Expr) := do
  let e := mkApp5 (mkConst ``Grind.OrderedRing [u]) α semiringInst leInst ltInst isPreorderInst
  synthInstance? e

def getStructId? (type : Expr) : GoalM (Option Nat) := do
  unless (← getConfig).order do return none
  if let some id? := (← get').typeIdOf.find? { expr := type } then
    return id?
  else
    let id? ← go?
    modify' fun s => { s with typeIdOf := s.typeIdOf.insert { expr := type } id? }
    return id?
where
  go? : GoalM (Option Nat) := do
    let some u ← getDecLevel? type | return none
    let some leInst ← getInst? ``LE u type | return none
    let some isPreorderInst ← mkIsPreorderInst? u type (some leInst) | return none
    -- **TODO** compute `isPartialInst?` and `isLinearPreInst?` on demand
    let isPartialInst? ← mkIsPartialOrderInst? u type (some leInst)
    let isLinearPreInst? ← mkIsLinearPreorderInst? u type (some leInst)
    let ltInst? ← getInst? ``LT u type
    let leFn ← internalizeFn <| mkApp2 (mkConst ``LE.le [u]) type leInst
    let (lawfulOrderLTInst?, ltFn?) ← if let some ltInst := ltInst? then
      let inst? ← mkLawfulOrderLTInst? u type ltInst? (some leInst)
      if inst?.isNone then
        pure (none, none)
      else
        let ltFn ← internalizeFn <| mkApp2 (mkConst ``LT.lt [u]) type ltInst
        pure (inst?, some ltFn)
    else
      pure (none, none)
    let (ringId?, ringInst?, orderedRingInst?, isCommRing) ← if lawfulOrderLTInst?.isNone then
      pure (none, none, none, false)
    else if let some ringId ← getCommRingId? type then
      let ringInst ← RingM.run ringId do return (← getRing).ringInst
      let semiringInst ← RingM.run ringId do return (← getRing).semiringInst
      let some ordRingInst ← mkOrderedRingInst? u type semiringInst leInst ltInst?.get! isPreorderInst
        | pure (none, none, none, true)
      pure (some ringId, some ringInst, some ordRingInst, true)
    else if let some ringId ← getNonCommRingId? type then
      let semiringInst ← NonCommRingM.run ringId do return (← getRing).semiringInst
      let ringInst ← NonCommRingM.run ringId do return (← getRing).ringInst
      let some ordRingInst ← mkOrderedRingInst? u type semiringInst leInst ltInst?.get! isPreorderInst
        | pure (none, none, none, true)
      pure (some ringId, some ringInst, some ordRingInst, false)
    else
      pure (none, none, none, false)
    let id := (← get').structs.size
    let struct := {
      id,  type, u, leInst, isPreorderInst, ltInst?, leFn, isPartialInst?, ringInst?, orderedRingInst?
      isLinearPreInst?, ltFn?, lawfulOrderLTInst?, ringId?, isCommRing
     }
    modify' fun s => { s with structs := s.structs.push struct }
    return some id

end Lean.Meta.Grind.Order
