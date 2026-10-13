/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingM
import Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr
public section
namespace Lean.Meta.Grind.Arith.CommRing
open Sym.Arith

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

/-- The `Sym.Arith` classification record of the current semiring. -/
protected def SemiringM.getCommSemiring : SemiringM Sym.Arith.CommSemiring := do
  let s ← getArithState
  let semiringId ← getSemiringId
  if h : semiringId < s.semirings.size then
    return s.semirings[semiringId]
  else
    throwError "`grind` internal error, invalid semiringId"

@[inline] protected def SemiringM.modifyCommSemiring (f : Sym.Arith.CommSemiring → Sym.Arith.CommSemiring) : SemiringM Unit := do
  let semiringId ← getSemiringId
  modifyArithState fun s => { s with semirings := s.semirings.modify semiringId f }

instance : MonadCommSemiring SemiringM where
  getCommSemiring := SemiringM.getCommSemiring
  modifyCommSemiring := SemiringM.modifyCommSemiring

/-- The `Sym.Arith` record of the envelope ring `OfSemiring.Q` of the current semiring. -/
protected def SemiringM.getCommRing : SemiringM Sym.Arith.CommRing := do
  let s ← getArithState
  let ringId := (← getCommSemiring).ringId
  if h : ringId < s.rings.size then
    return s.rings[ringId]
  else
    throwError "`grind` internal error, invalid ringId"

protected def SemiringM.modifyCommRing (f : Sym.Arith.CommRing → Sym.Arith.CommRing) : SemiringM Unit := do
  let ringId := (← getCommSemiring).ringId
  modifyArithState fun s => { s with rings := s.rings.modify ringId f }

instance : MonadCommRing SemiringM where
 getCommRing := SemiringM.getCommRing
 modifyCommRing := SemiringM.modifyCommRing

/-- The per-goal solver state of the current semiring. -/
protected def SemiringM.getSemiringState : SemiringM SemiringState := do
  return (← get').getSemiring (← getSemiringId)

protected def SemiringM.modifySemiringState (f : SemiringState → SemiringState) : SemiringM Unit := do
  let semiringId ← getSemiringId
  modify' fun s => s.modifySemiring semiringId f

instance : MonadSemiringState SemiringM where
  getSemiringState := SemiringM.getSemiringState
  modifySemiringState := SemiringM.modifySemiringState

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
def mkSVarCore [MonadLiftT GoalM m] [Monad m] [MonadSemiringState m] [MonadSetTermId m] (e : Expr) : m Var := do
  let s ← getSemiringState
  if let some var := s.varMap.find? { expr := e } then
    return var
  let var : Var := s.vars.size
  modifySemiringState fun s => { s with
    vars       := s.vars.push e
    varMap     := s.varMap.insert { expr := e } var
  }
  MonadSetTermId.setTermId e
  ringExt.markTerm e
  return var

/--
Semiring terms are reified only by the `internalize` hook, after the core has created the
`ENode`s of the term and of all its subterms. So every variable created here is already
internalized, and there is no generation to assign.
-/
instance : MonadMkVar SemiringM where
  mkVar e := do
    unless (← alreadyInternalized e) do
      throwError "`grind` internal error, semiring term has not been internalized{indentExpr e}"
    mkSVarCore e

def _root_.Lean.Grind.CommRing.Expr.denoteAsRingExpr (e : SemiringExpr) : SemiringM Expr := do
  shareCommon (← go e)
where
  go : SemiringExpr → SemiringM Expr
  | .num k     => denoteNum k
  | .natCast k => denoteNum k
  | .var x   => return mkApp (← getToQFn) (← getSemiringState).vars[x]!
  | .add a b => return mkApp2 (← getAddFn) (← go a) (← go b)
  | .mul a b => return mkApp2 (← getMulFn) (← go a) (← go b)
  | .pow a k => return mkApp2 (← getPowFn) (← go a) (toExpr k)
  | .neg .. | .sub .. | .intCast .. => unreachable!

end Lean.Meta.Grind.Arith.CommRing
