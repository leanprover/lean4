/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingM
import Init.Grind.Ring.Field
import Init.Grind.Ring.Envelope
import Lean.Meta.Tactic.Grind.Simp
import Lean.Meta.Tactic.Grind.Arith.Insts
public section
namespace Lean.Meta.Grind.Arith.CommRing

/--
Returns the ring id for the given type if there is a `CommRing` instance for it.

This function will also perform sanity-checks
(e.g., the `Add` instance for `type` must be definitionally equal to the `CommRing.toAdd` one.)

It also caches the functions representing `+`, `*`, `-`, `^`, and `intCast`.
-/
def getCommRingId? (type : Expr) : GoalM (Option Nat) := do
  if let some id? := (← get').typeIdOf.find? { expr := type } then
    return id?
  else
    let id? ← go?
    modify' fun s => { s with typeIdOf := s.typeIdOf.insert { expr := type } id? }
    return id?
where
  go? : GoalM (Option Nat) := do
    let u ← getDecLevel type
    let commRing := mkApp (mkConst ``Grind.CommRing [u]) type
    let some commRingInst ← synthInstance? commRing | return none
    let ringInst := mkApp2 (mkConst ``Grind.CommRing.toRing [u]) type commRingInst
    let semiringInst := mkApp2 (mkConst ``Grind.Ring.toSemiring [u]) type ringInst
    let commSemiringInst := mkApp2 (mkConst ``Grind.CommRing.toCommSemiring [u]) type semiringInst
    trace_goal[grind.ring] "new ring: {type}"
    let charInst? ← getIsCharInst? u type semiringInst
    let noZeroDivInst? ← getNoZeroDivInst? u type
    trace_goal[grind.ring] "NoNatZeroDivisors available: {noZeroDivInst?.isSome}"
    let fieldInst? ← synthInstance? <| mkApp (mkConst ``Grind.Field [u]) type
    let semiringId? := none
    let id := (← get').rings.size
    let ring : CommRing := {
      id, semiringId?, type, u, semiringInst, ringInst, commSemiringInst,
      commRingInst, charInst?, noZeroDivInst?, fieldInst?,
    }
    modify' fun s => { s with rings := s.rings.push ring }
    return some id

/--
Returns the ring id for the given type if there is a `Ring` instance for it.
This function is invoked only when `getCommRingId?` returns `none`.
-/
def getNonCommRingId? (type : Expr) : GoalM (Option Nat) := do
  if let some id? := (← get').nctypeIdOf.find? { expr := type } then
    return id?
  else
    let id? ← go?
    modify' fun s => { s with nctypeIdOf := s.nctypeIdOf.insert { expr := type } id? }
    return id?
where
  go? : GoalM (Option Nat) := do
    let u ← getDecLevel type
    let ring := mkApp (mkConst ``Grind.Ring [u]) type
    let some ringInst ← synthInstance? ring | return none
    let semiringInst := mkApp2 (mkConst ``Grind.Ring.toSemiring [u]) type ringInst
    trace_goal[grind.ring] "new ring: {type}"
    let charInst? ← getIsCharInst? u type semiringInst
    let id := (← get').ncRings.size
    let ring : Ring := {
      id, type, u, semiringInst, ringInst, charInst?
    }
    modify' fun s => { s with ncRings := s.ncRings.push ring }
    return some id

private def setCommSemiringId (ringId : Nat) (semiringId : Nat) : GoalM Unit := do
  RingM.run ringId do modifyCommRing fun s => { s with semiringId? := some semiringId }

def getCommSemiringId? (type : Expr) : GoalM (Option Nat) := do
  if let some id? := (← get').stypeIdOf.find? { expr := type } then
    return id?
  else
    let id? ← go?
    modify' fun s => { s with stypeIdOf := s.stypeIdOf.insert { expr := type } id? }
    return id?
where
  go? : GoalM (Option Nat) := do
    let u ← getDecLevel type
    let commSemiring := mkApp (mkConst ``Grind.CommSemiring [u]) type
    let some commSemiringInst ← synthInstance? commSemiring | return none
    let semiringInst := mkApp2 (mkConst ``Grind.CommSemiring.toSemiring [u]) type commSemiringInst
    let q ← shareCommon (← canon (mkApp2 (mkConst ``Grind.Ring.OfSemiring.Q [u]) type semiringInst))
    let some ringId ← getCommRingId? q
      | throwError "`grind` unexpected failure, failure to initialize ring{indentExpr q}"
    let id := (← get').semirings.size
    let semiring : CommSemiring := {
      id, type, ringId, u, semiringInst, commSemiringInst
    }
    modify' fun s => { s with semirings := s.semirings.push semiring }
    setCommSemiringId ringId id
    return some id

def getNonCommSemiringId? (type : Expr) : GoalM (Option Nat) := do
  if let some id? := (← get').ncstypeIdOf.find? { expr := type } then
    return id?
  else
    let id? ← go?
    modify' fun s => { s with ncstypeIdOf := s.ncstypeIdOf.insert { expr := type } id? }
    return id?
where
  go? : GoalM (Option Nat) := do
    let u ← getDecLevel type
    let semiring := mkApp (mkConst ``Grind.Semiring [u]) type
    let some semiringInst ← synthInstance? semiring | return none
    let id := (← get').ncSemirings.size
    let semiring : Semiring := { id, type, u, semiringInst }
    modify' fun s => { s with ncSemirings := s.ncSemirings.push semiring }
    return some id

end Lean.Meta.Grind.Arith.CommRing
