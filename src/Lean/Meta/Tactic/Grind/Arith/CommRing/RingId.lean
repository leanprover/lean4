/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingM
import Lean.Meta.Tactic.Grind.Arith.Insts
import Lean.Meta.Sym.Arith.Ring.Detect
public section
namespace Lean.Meta.Grind.Arith.CommRing

open Sym.Arith.Ring (detectCommRing?)

/--
Returns the ring id for the given type if there is a `CommRing` instance for it.
Uses the shared detection cache in `SymM` so that ring detection results and
lazily-computed operations (e.g., `addFn?`) are shared between the arithmetic
normalizer and grind's ring solver.
-/
def getCommRingId? (type : Expr) : GoalM (Option Nat) := do
  if let some id? := (← get').typeIdOf.find? { expr := type } then
    return id?
  let some tmpl ← detectCommRing? type | do
    modify' fun s => { s with typeIdOf := s.typeIdOf.insert { expr := type } none }
    return none
  trace_goal[grind.ring] "new ring: {type}"
  trace_goal[grind.ring] "NoNatZeroDivisors available: {tmpl.noZeroDivInst?.isSome}"
  let id := (← get').rings.size
  -- Copy from shared cache (includes pre-computed lazy fields from ArithNorm),
  -- reset per-context state (vars, varMap, denote)
  let ring : CommRing := { tmpl with
    toRing.id := id
    toRing.vars := {}
    toRing.varMap := {}
    toRing.denote := {}
    denoteEntries := {}
  }
  modify' fun s => { s with
    rings := s.rings.push ring
    typeIdOf := s.typeIdOf.insert { expr := type } (some id)
  }
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
