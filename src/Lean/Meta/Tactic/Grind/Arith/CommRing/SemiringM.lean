/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Grind.Ring.OfSemiring
public import Lean.Meta.Tactic.Grind.Types
public import Lean.Meta.Tactic.Grind.SynthInstance
public import Lean.Meta.Tactic.Grind.Arith.CommRing.MonadRing
public import Lean.Meta.Tactic.Grind.Arith.CommRing.GetSet
public import Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr
import Lean.Meta.Tactic.Grind.Arith.CommRing.Functions
public section
namespace Lean.Meta.Grind.Arith.CommRing

structure SemiringM.Context where
  semiringId : Nat

abbrev SemiringM := ReaderT SemiringM.Context GoalM

abbrev SemiringM.run (semiringId : Nat) (x : SemiringM α) : GoalM α :=
  x { semiringId }

abbrev getSemiringId : SemiringM Nat :=
  return (← read).semiringId

def getSemiring : SemiringM Semiring := do
  let s ← get'
  let semiringId ← getSemiringId
  if h : semiringId < s.semirings.size then
    return s.semirings[semiringId]
  else
    throwError "`grind` internal error, invalid semiringId"

protected def SemiringM.getRing : SemiringM Ring := do
  let s ← get'
  let ringId := (← getSemiring).ringId
  if h : ringId < s.rings.size then
    return s.rings[ringId]
  else
    throwError "`grind` internal error, invalid ringId"

instance : MonadRing SemiringM where
  getRing := SemiringM.getRing
  modifyRing f := do
    let ringId := (← getSemiring).ringId
    modify' fun s => { s with rings := s.rings.modify ringId f }
  canonExpr e := do shareCommon (← canon e)
  synthInstance? e := Grind.synthInstance? e

@[inline] def modifySemiring (f : Semiring → Semiring) : SemiringM Unit := do
  let semiringId ← getSemiringId
  modify' fun s => { s with semirings := s.semirings.modify semiringId f }

def getAddFn' : SemiringM Expr := do
  let s ← getSemiring
  if let some addFn := s.addFn? then return addFn
  let addFn ← mkBinHomoFn s.type s.u ``HAdd ``HAdd.hAdd
  modifySemiring fun s => { s with addFn? := some addFn }
  return addFn

def getMulFn' : SemiringM Expr := do
  let s ← getSemiring
  if let some mulFn := s.mulFn? then return mulFn
  let mulFn ← mkBinHomoFn s.type s.u ``HMul ``HMul.hMul
  modifySemiring fun s => { s with mulFn? := some mulFn }
  return mulFn

def getPowFn' : SemiringM Expr := do
  let s ← getSemiring
  if let some powFn := s.powFn? then return powFn
  let powFn ← mkPowFn s.u s.type s.semiringInst
  modifySemiring fun s => { s with powFn? := some powFn }
  return powFn

def getNatCastFn' : SemiringM Expr := do
  let s ← getSemiring
  if let some natCastFn := s.natCastFn? then return natCastFn
  let natCastFn ← mkNatCastFn s.u s.type s.semiringInst
  modifySemiring fun s => { s with natCastFn? := some natCastFn }
  return natCastFn

def getToQFn : SemiringM Expr := do
  let s ← getSemiring
  if let some toQFn := s.toQFn? then return toQFn
  let toQFn ← canonExpr <| mkApp2 (mkConst ``Grind.Ring.OfSemiring.toQ [s.u]) s.type s.semiringInst
  modifySemiring fun s => { s with toQFn? := some toQFn }
  return toQFn

private def mkAddRightCancelInst? (u : Level) (type : Expr) : GoalM (Option Expr) := do
  let add := mkApp (mkConst ``Add [u]) type
  let some addInst ← synthInstance? add | return none
  let addRightCancel := mkApp2 (mkConst ``Grind.AddRightCancel [u]) type addInst
  synthInstance? addRightCancel

def getAddRightCancelInst? : SemiringM (Option Expr) := do
  let s ← getSemiring
  if let some r := s.addRightCancelInst? then return r
  let addRightCancelInst? ← mkAddRightCancelInst? s.u s.type
  modifySemiring fun s => { s with addRightCancelInst? := some addRightCancelInst? }
  return addRightCancelInst?

def getTermSemiringId? (e : Expr) : GoalM (Option Nat) := do
  return (← get').exprToSemiringId.find? { expr := e }

def setTermSemiringId (e : Expr) : SemiringM Unit := do
  let semiringId ← getSemiringId
  if let some semiringId' ← getTermSemiringId? e then
    unless semiringId' == semiringId do
      reportIssue! "expression in two different semirings{indentExpr e}"
    return ()
  modify' fun s => { s with exprToSemiringId := s.exprToSemiringId.insert { expr := e } semiringId }

/-- Similar to `mkVar` but for `Semiring`s -/
def mkSVar (e : Expr) : SemiringM Var := do
  let s ← getSemiring
  if let some var := s.varMap.find? { expr := e } then
    return var
  let var : Var := s.vars.size
  modifySemiring fun s => { s with
    vars       := s.vars.push e
    varMap     := s.varMap.insert { expr := e } var
  }
  setTermSemiringId e
  markAsCommRingTerm e
  return var

def _root_.Lean.Grind.Ring.OfSemiring.Expr.denoteAsRingExpr (e : SemiringExpr) : SemiringM Expr := do
  shareCommon (← go e)
where
  go : SemiringExpr → SemiringM Expr
  | .num k => denoteNum k
  | .var x => return mkApp (← getToQFn) (← getSemiring).vars[x]!
  | .add a b => return mkApp2 (← getAddFn) (← go a) (← go b)
  | .mul a b => return mkApp2 (← getMulFn) (← go a) (← go b)
  | .pow a k => return mkApp2 (← getPowFn) (← go a) (toExpr k)

end Lean.Meta.Grind.Arith.CommRing
