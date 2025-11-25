/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingM
public import Lean.Meta.Tactic.Grind.Arith.CommRing.MonadSemiring
import Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr
public import Lean.Meta.Tactic.Grind.Arith.CommRing.Functions
public section
namespace Lean.Meta.Grind.Arith.CommRing

structure SemiringM.Context where
  semiringId : Nat

abbrev SemiringM := ReaderT SemiringM.Context GoalM

abbrev SemiringM.run (semiringId : Nat) (x : SemiringM α) : GoalM α :=
  x { semiringId }

abbrev getSemiringId : SemiringM Nat :=
  return (← read).semiringId

instance : MonadCanon SemiringM where
  canonExpr e := do shareCommon (← canon e)
  synthInstance? e := Grind.synthInstance? e

protected def SemiringM.getCommSemiring : SemiringM CommSemiring := do
  let s ← get'
  let semiringId ← getSemiringId
  if h : semiringId < s.semirings.size then
    return s.semirings[semiringId]
  else
    throwError "`grind` internal error, invalid semiringId"

@[inline] protected def SemiringM.modifyCommSemiring (f : CommSemiring → CommSemiring) : SemiringM Unit := do
  let semiringId ← getSemiringId
  modify' fun s => { s with semirings := s.semirings.modify semiringId f }

instance : MonadCommSemiring SemiringM where
  getCommSemiring := SemiringM.getCommSemiring
  modifyCommSemiring := SemiringM.modifyCommSemiring

protected def SemiringM.getCommRing : SemiringM CommRing := do
  let s ← get'
  let ringId := (← getCommSemiring).ringId
  if h : ringId < s.rings.size then
    return s.rings[ringId]
  else
    throwError "`grind` internal error, invalid ringId"

protected def SemiringM.modifyCommRing (f : CommRing → CommRing) : SemiringM Unit := do
  let ringId := (← getCommSemiring).ringId
  modify' fun s => { s with rings := s.rings.modify ringId f }

instance : MonadCommRing SemiringM where
 getCommRing := SemiringM.getCommRing
 modifyCommRing := SemiringM.modifyCommRing

def getToQFn : SemiringM Expr := do
  let s ← getCommSemiring
  if let some toQFn := s.toQFn? then return toQFn
  let toQFn ← canonExpr <| mkApp2 (mkConst ``Grind.Ring.OfSemiring.toQ [s.u]) s.type s.semiringInst
  modifyCommSemiring fun s => { s with toQFn? := some toQFn }
  return toQFn

private def mkAddRightCancelInst? (u : Level) (type : Expr) : GoalM (Option Expr) := do
  let add := mkApp (mkConst ``Add [u]) type
  let some addInst ← synthInstance? add | return none
  let addRightCancel := mkApp2 (mkConst ``Grind.AddRightCancel [u]) type addInst
  synthInstance? addRightCancel

def getAddRightCancelInst? : SemiringM (Option Expr) := do
  let s ← getCommSemiring
  if let some r := s.addRightCancelInst? then return r
  let addRightCancelInst? ← mkAddRightCancelInst? s.u s.type
  modifyCommSemiring fun s => { s with addRightCancelInst? := some addRightCancelInst? }
  return addRightCancelInst?

section
variable [MonadLiftT MetaM m] [MonadError m] [Monad m] [MonadCanon m] [MonadSemiring m]

def getAddFn' : m Expr := do
  let s ← getSemiring
  if let some addFn := s.addFn? then return addFn
  let expectedInst := mkApp2 (mkConst ``instHAdd [s.u]) s.type <| mkApp2 (mkConst ``Grind.Semiring.toAdd [s.u]) s.type s.semiringInst
  let addFn ← mkBinHomoFn s.type s.u ``HAdd ``HAdd.hAdd expectedInst
  modifySemiring fun s => { s with addFn? := some addFn }
  return addFn

def getMulFn' : m Expr := do
  let s ← getSemiring
  if let some mulFn := s.mulFn? then return mulFn
  let expectedInst := mkApp2 (mkConst ``instHMul [s.u]) s.type <| mkApp2 (mkConst ``Grind.Semiring.toMul [s.u]) s.type s.semiringInst
  let mulFn ← mkBinHomoFn s.type s.u ``HMul ``HMul.hMul expectedInst
  modifySemiring fun s => { s with mulFn? := some mulFn }
  return mulFn

def getPowFn' : m Expr := do
  let s ← getSemiring
  if let some powFn := s.powFn? then return powFn
  let powFn ← mkPowFn s.u s.type s.semiringInst
  modifySemiring fun s => { s with powFn? := some powFn }
  return powFn

def getNatCastFn' : m Expr := do
  let s ← getSemiring
  if let some natCastFn := s.natCastFn? then return natCastFn
  let natCastFn ← mkNatCastFn s.u s.type s.semiringInst
  modifySemiring fun s => { s with natCastFn? := some natCastFn }
  return natCastFn

end

def getTermSemiringId? (e : Expr) : GoalM (Option Nat) := do
  return (← get').exprToSemiringId.find? { expr := e }

def setTermSemiringId (e : Expr) : SemiringM Unit := do
  let semiringId ← getSemiringId
  if let some semiringId' ← getTermSemiringId? e then
    unless semiringId' == semiringId do
      reportIssue! "expression in two different semirings{indentExpr e}"
    return ()
  modify' fun s => { s with exprToSemiringId := s.exprToSemiringId.insert { expr := e } semiringId }

instance : MonadSetTermId SemiringM where
  setTermId e := setTermSemiringId e

/-- Similar to `mkVarCore` but for `Semiring`s -/
def mkSVarCore [MonadLiftT GoalM m] [Monad m] [MonadSemiring m] [MonadSetTermId m] (e : Expr) : m Var := do
  let s ← getSemiring
  if let some var := s.varMap.find? { expr := e } then
    return var
  let var : Var := s.vars.size
  modifySemiring fun s => { s with
    vars       := s.vars.push e
    varMap     := s.varMap.insert { expr := e } var
  }
  MonadSetTermId.setTermId e
  ringExt.markTerm e
  return var

def mkSVar (e : Expr) : SemiringM Var := do
  mkSVarCore e

def _root_.Lean.Grind.CommRing.Expr.denoteAsRingExpr (e : SemiringExpr) : SemiringM Expr := do
  shareCommon (← go e)
where
  go : SemiringExpr → SemiringM Expr
  | .num k     => denoteNum k
  | .natCast k => denoteNum k
  | .var x   => return mkApp (← getToQFn) (← getSemiring).vars[x]!
  | .add a b => return mkApp2 (← getAddFn) (← go a) (← go b)
  | .mul a b => return mkApp2 (← getMulFn) (← go a) (← go b)
  | .pow a k => return mkApp2 (← getPowFn) (← go a) (toExpr k)
  | .neg .. | .sub .. | .intCast .. => unreachable!

end Lean.Meta.Grind.Arith.CommRing
