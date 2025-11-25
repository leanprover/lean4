/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingM
public section
namespace Lean.Meta.Grind.Arith.CommRing

structure NonCommRingM.Context where
  ringId : Nat

/-- We don't want to keep carrying the `RingId` around. -/
abbrev NonCommRingM := ReaderT NonCommRingM.Context GoalM

abbrev NonCommRingM.run (ringId : Nat) (x : NonCommRingM α) : GoalM α :=
  x { ringId }

instance : MonadCanon NonCommRingM where
  canonExpr e := do shareCommon (← canon e)
  synthInstance? e := Grind.synthInstance? e

protected def NonCommRingM.getRing : NonCommRingM Ring := do
  let s ← get'
  let ringId := (← read).ringId
  if h : ringId < s.ncRings.size then
    return s.ncRings[ringId]
  else
    throwError "`grind` internal error, invalid ringId"

protected def NonCommRingM.modifyRing (f : Ring → Ring) : NonCommRingM Unit := do
  let ringId := (← read).ringId
  modify' fun s => { s with ncRings := s.ncRings.modify ringId f }

instance : MonadRing NonCommRingM where
  getRing := NonCommRingM.getRing
  modifyRing := NonCommRingM.modifyRing

def getTermNonCommRingId? (e : Expr) : GoalM (Option Nat) := do
    return (← get').exprToNCRingId.find? { expr := e }

def setTermNonCommRingId (e : Expr) : NonCommRingM Unit := do
  let ringId := (← read).ringId
  if let some ringId' ← getTermNonCommRingId? e then
    unless ringId' == ringId do
      reportIssue! "expression in two different rings{indentExpr e}"
    return ()
  modify' fun s => { s with exprToNCRingId := s.exprToNCRingId.insert { expr := e } ringId }

instance : MonadSetTermId NonCommRingM where
  setTermId e := setTermNonCommRingId e

end Lean.Meta.Grind.Arith.CommRing
