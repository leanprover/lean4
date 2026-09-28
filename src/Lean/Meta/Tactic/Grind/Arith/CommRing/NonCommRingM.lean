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
open Sym.Arith

structure NonCommRingM.Context where
  ringId : Nat
  /-- Generation assigned to terms internalized while reifying (see `ncreify?`). -/
  gen : Nat := 0

/-- We don't want to keep carrying the `RingId` around. -/
abbrev NonCommRingM := ReaderT NonCommRingM.Context GoalM

abbrev NonCommRingM.run (ringId : Nat) (x : NonCommRingM α) : GoalM α :=
  x { ringId }

instance : MonadCanon NonCommRingM where
  canonExpr e := do shareCommon (← canon e)
  synthInstance? e := Grind.synthInstance? e

/-- The `Sym.Arith` classification record of the current non-commutative ring. -/
protected def NonCommRingM.getRing : NonCommRingM Sym.Arith.Ring := do
  let s ← getArithState
  let ringId := (← read).ringId
  if h : ringId < s.ncRings.size then
    return s.ncRings[ringId]
  else
    throwError "`grind` internal error, invalid ringId"

protected def NonCommRingM.modifyRing (f : Sym.Arith.Ring → Sym.Arith.Ring) : NonCommRingM Unit := do
  let ringId := (← read).ringId
  modifyArithState fun s => { s with ncRings := s.ncRings.modify ringId f }

instance : MonadRing NonCommRingM where
  getRing := NonCommRingM.getRing
  modifyRing := NonCommRingM.modifyRing

/-- The per-goal solver state of the current non-commutative ring. -/
protected def NonCommRingM.getRingState : NonCommRingM RingState := do
  return (← get').getNCRing (← read).ringId

protected def NonCommRingM.modifyRingState (f : RingState → RingState) : NonCommRingM Unit := do
  let ringId := (← read).ringId
  modify' fun s => s.modifyNCRing ringId f

instance : MonadRingState NonCommRingM where
  getRingState := NonCommRingM.getRingState
  modifyRingState := NonCommRingM.modifyRingState

instance : MonadGetVar NonCommRingM where
  getVar x := return (← getRingState).vars[x]!

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

instance : MonadMkVar NonCommRingM where
  mkVar e := do
    unless (← alreadyInternalized e) do
      internalize e (← read).gen
    mkVarCore e

end Lean.Meta.Grind.Arith.CommRing
