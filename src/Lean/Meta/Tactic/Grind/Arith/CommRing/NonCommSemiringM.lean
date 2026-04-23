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
open Sym.Arith

structure NonCommSemiringM.Context where
  semiringId : Nat
  symSemiringId : Nat

abbrev NonCommSemiringM := ReaderT NonCommSemiringM.Context GoalM

abbrev NonCommSemiringM.run (semiringId : Nat) (x : NonCommSemiringM α) : GoalM α := do
  let s ← get'
  let symSemiringId := s.ncSemirings[semiringId]!.symId
  x { semiringId, symSemiringId }

protected def NonCommSemiringM.getSemiring : NonCommSemiringM Semiring := do
  let s ← getArithState
  let semiringId := (← read).symSemiringId
  if h : semiringId < s.ncSemirings.size then
    return s.ncSemirings[semiringId]
  else
    throwError "`grind` internal error, invalid semiringId"

protected def NonCommSemiringM.modifySemiring (f : Semiring → Semiring) : NonCommSemiringM Unit := do
  let semiringId := (← read).symSemiringId
  modifyArithState fun s => { s with ncSemirings := s.ncSemirings.modify semiringId f }

instance : MonadSemiring NonCommSemiringM where
  getSemiring := NonCommSemiringM.getSemiring
  modifySemiring := NonCommSemiringM.modifySemiring

def getSemiringEntry : NonCommSemiringM SemiringEntry := do
  let s ← get'
  let semiringId := (← read).semiringId
  if h : semiringId < s.ncSemirings.size then
    return s.ncSemirings[semiringId]
  else
    throwError "`grind` internal error, invalid semiringId"

def modifySemiringEntry (f : SemiringEntry → SemiringEntry) : NonCommSemiringM Unit := do
  let semiringId := (← read).semiringId
  modify' fun s => { s with ncSemirings := s.ncSemirings.modify semiringId f }

def getTermNonCommSemiringId? (e : Expr) : GoalM (Option Nat) := do
    return (← get').exprToNCSemiringId.find? { expr := e }

def setTermNonCommSemiringId (e : Expr) : NonCommSemiringM Unit := do
  let semiringId := (← read).semiringId
  if let some semiringId' ← getTermNonCommSemiringId? e then
    unless semiringId' == semiringId do
      reportIssue! "expression in two different semirings{indentExpr e}"
    return ()
  modify' fun s => { s with exprToNCSemiringId := s.exprToNCSemiringId.insert { expr := e } semiringId }

def mkNonCommSVar (e : Expr) (gen : Nat) : NonCommSemiringM Var := do
  unless (← alreadyInternalized e) do
    internalize e gen
  let s ← getSemiringEntry
  if let some var := s.varMap.find? { expr := e } then
    return var
  let var : Var := s.vars.size
  modifySemiringEntry fun s => { s with
    vars       := s.vars.push e
    varMap     := s.varMap.insert { expr := e } var
  }
  setTermNonCommSemiringId e
  ringExt.markTerm e
  return var

instance : MonadMkVar NonCommSemiringM where
  mkVar := mkNonCommSVar

instance : MonadGetVar NonCommSemiringM where
  getVar x := return (← getSemiringEntry).vars[x]!

end Lean.Meta.Grind.Arith.CommRing
