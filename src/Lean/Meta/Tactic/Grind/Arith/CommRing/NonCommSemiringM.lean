/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.CommRing.SemiringM
public section
namespace Lean.Meta.Grind.Arith.CommRing

structure NonCommSemiringM.Context where
  semiringId : Nat

abbrev NonCommSemiringM := ReaderT NonCommSemiringM.Context GoalM

abbrev NonCommSemiringM.run (semiringId : Nat) (x : NonCommSemiringM α) : GoalM α :=
  x { semiringId }

instance : MonadCanon NonCommSemiringM where
  canonExpr e := do shareCommon (← canon e)
  synthInstance? e := Grind.synthInstance? e

protected def NonCommSemiringM.getSemiring : NonCommSemiringM Semiring := do
  let s ← get'
  let semiringId := (← read).semiringId
  if h : semiringId < s.ncSemirings.size then
    return s.ncSemirings[semiringId]
  else
    throwError "`grind` internal error, invalid semiringId"

protected def NonCommSemiringM.modifySemiring (f : Semiring → Semiring) : NonCommSemiringM Unit := do
  let semiringId := (← read).semiringId
  modify' fun s => { s with ncSemirings := s.ncSemirings.modify semiringId f }

instance : MonadSemiring NonCommSemiringM where
  getSemiring := NonCommSemiringM.getSemiring
  modifySemiring := NonCommSemiringM.modifySemiring

def getTermNonCommSemiringId? (e : Expr) : GoalM (Option Nat) := do
    return (← get').exprToNCSemiringId.find? { expr := e }

def setTermNonCommSemiringId (e : Expr) : NonCommSemiringM Unit := do
  let semiringId := (← read).semiringId
  if let some semiringId' ← getTermNonCommSemiringId? e then
    unless semiringId' == semiringId do
      reportIssue! "expression in two different semirings{indentExpr e}"
    return ()
  modify' fun s => { s with exprToNCSemiringId := s.exprToNCSemiringId.insert { expr := e } semiringId }

instance : MonadSetTermId NonCommSemiringM where
  setTermId e := setTermNonCommSemiringId e

end Lean.Meta.Grind.Arith.CommRing
