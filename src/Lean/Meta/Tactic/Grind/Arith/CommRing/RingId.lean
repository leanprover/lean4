/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingM
import Lean.Meta.Tactic.Grind.Arith.Insts
import Lean.Meta.Sym.Arith.Classify
public section
namespace Lean.Meta.Grind.Arith.CommRing
open Sym Arith
/--
Returns the ring id for the given type if there is a `CommRing` instance for it.

This function will also perform sanity-checks
(e.g., the `Add` instance for `type` must be definitionally equal to the `CommRing.toAdd` one.)

It also caches the functions representing `+`, `*`, `-`, `^`, and `intCast`.
-/
def getCommRingId? (type : Expr) : GoalM (Option Nat) := do
  if let some result := (← get').typeClassify.find? { expr := type } then
    let .commRing id := result | return none
    return some id
  else
    let result ← go?
    modify' fun s => { s with typeClassify := s.typeClassify.insert { expr := type } result }
    return result.toOption
where
  go? : GoalM ClassifyResult := do
    let .commRing symId ← classify? type | return .none
    let id := (← get').rings.size
    modify' fun s => { s with rings := s.rings.push { symId, id } }
    return .commRing id

/--
Returns the ring id for the given type if there is a `Ring` instance for it.
This function is invoked only when `getCommRingId?` returns `none`.
-/
def getNonCommRingId? (type : Expr) : GoalM (Option Nat) := do
  if let some result := (← get').typeClassify.find? { expr := type } then
    let .nonCommRing id := result | return none
    return some id
  else
    let result ← go?
    modify' fun s => { s with typeClassify := s.typeClassify.insert { expr := type } result }
    return result.toOption
where
  go? : GoalM ClassifyResult := do
    let .nonCommRing symId ← classify? type | return .none
    let id := (← get').ncRings.size
    modify' fun s => { s with ncRings := s.ncRings.push { symId, id } }
    return .nonCommRing id

private def setCommSemiringId (ringId : Nat) (semiringId : Nat) : GoalM Unit := do
  RingM.run ringId do modifyCommRing fun s => { s with semiringId? := some semiringId }

def getCommSemiringId? (type : Expr) : GoalM (Option Nat) := do
  if let some result := (← get').typeClassify.find? { expr := type } then
    let .commSemiring id := result | return .none
    return some id
  else
    let result ← go?
    modify' fun s => { s with typeClassify := s.typeClassify.insert { expr := type } result }
    return result.toOption
where
  go? : GoalM ClassifyResult := do
    let .commSemiring symId ← classify? type | return .none
    let s ← getCommSemiringOfId symId
    let r ← getCommRingOfId s.ringId
    let some ringId ← getCommRingId? r.type
      | throwError "`grind` unexpected failure, failure to initialize ring{indentExpr r.type}"
    let id := (← get').semirings.size
    modify' fun s => { s with semirings := s.semirings.push { symId, id, ringId } }
    setCommSemiringId ringId id
    return .commSemiring id

def getNonCommSemiringId? (type : Expr) : GoalM (Option Nat) := do
  if let some result := (← get').typeClassify.find? { expr := type } then
    let .nonCommSemiring id := result | return .none
    return some id
  else
    let result ← go?
    modify' fun s => { s with typeClassify := s.typeClassify.insert { expr := type } result }
    return result.toOption
where
  go? : GoalM ClassifyResult := do
    let .nonCommSemiring symId ← classify? type | return .none
    let id := (← get').ncSemirings.size
    modify' fun s => { s with ncSemirings := s.ncSemirings.push { symId, id } }
    return .nonCommSemiring id

end Lean.Meta.Grind.Arith.CommRing
