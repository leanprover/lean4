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
public section
namespace Lean.Meta.Grind.Order

private def preprocess (e : Expr) : GoalM Expr := do
  shareCommon (← canon e)

private def internalizeFn (fn : Expr) : GoalM Expr := do
  preprocess fn

private def getInst? (declName : Name) (u : Level) (type : Expr) : GoalM (Option Expr) := do
  synthInstance? <| mkApp (mkConst declName [u]) type

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
    let u ← getDecLevel type
    let some leInst ← getInst? ``LE u type | return none
    let some isPreorderInst ← mkIsPreorderInst? u type (some leInst) | return none
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
    let (ringId?, isCommRing) ← if let some ringId ← Arith.CommRing.getCommRingId? type then
      pure (some ringId, true)
    else if let some ringId ← Arith.CommRing.getNonCommRingId? type then
      pure (some ringId, false)
    else
      pure (none, false)
    let id := (← get').structs.size
    let struct := {
      id,  type, u, leInst, isPreorderInst, ltInst?, leFn, isPartialInst?
      isLinearPreInst?, ltFn?, lawfulOrderLTInst?, ringId?, isCommRing
     }
    modify' fun s => { s with structs := s.structs.push struct }
    return some id

end Lean.Meta.Grind.Order
