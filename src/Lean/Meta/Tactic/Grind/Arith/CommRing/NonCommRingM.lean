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
  symRingId : Nat

/-- We don't want to keep carrying the `RingId` around. -/
abbrev NonCommRingM := ReaderT NonCommRingM.Context GoalM

abbrev NonCommRingM.run (ringId : Nat) (x : NonCommRingM α) : GoalM α := do
  let s ← get'
  let symRingId := s.ncRings[ringId]!.symId
  x { ringId, symRingId }

protected def NonCommRingM.getRing : NonCommRingM Ring := do
  let s ← getArithState
  let ringId := (← read).symRingId
  if h : ringId < s.ncRings.size then
    return s.ncRings[ringId]
  else
    throwError "`grind` internal error, invalid ringId"

protected def NonCommRingM.modifyRing (f : Ring → Ring) : NonCommRingM Unit := do
  let ringId := (← read).symRingId
  modifyArithState fun s => { s with ncRings := s.ncRings.modify ringId f }

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

def getRingEntry : NonCommRingM RingEntry := do
  let s ← get'
  let ringId := (← read).ringId
  if h : ringId < s.ncRings.size then
    return s.ncRings[ringId]
  else
    throwError "`grind` internal error, invalid ringId"

def modifyRingEntry (f : RingEntry → RingEntry) : NonCommRingM Unit := do
  let ringId := (← read).ringId
  modify' fun s => { s with ncRings := s.ncRings.modify ringId f }

def mkNonCommVar (e : Expr) (gen : Nat) : NonCommRingM Var := do
  unless (← alreadyInternalized e) do
    internalize e gen
  let s ← getRingEntry
  if let some var := s.varMap.find? { expr := e } then
    return var
  let var : Var := s.vars.size
  modifyRingEntry fun s => { s with
    vars       := s.vars.push e
    varMap     := s.varMap.insert { expr := e } var
  }
  setTermNonCommRingId e
  ringExt.markTerm e
  return var

instance : MonadMkVar NonCommRingM where
  mkVar := mkNonCommVar

instance : MonadGetVar NonCommRingM where
  getVar x := return (← getRingEntry).vars[x]!

end Lean.Meta.Grind.Arith.CommRing
