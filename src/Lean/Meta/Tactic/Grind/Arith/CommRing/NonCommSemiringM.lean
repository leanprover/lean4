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

abbrev NonCommSemiringM := ReaderT NonCommSemiringM.Context GoalM

abbrev NonCommSemiringM.run (semiringId : Nat) (x : NonCommSemiringM α) : GoalM α :=
  x { semiringId }

instance : MonadCanon NonCommSemiringM where
  canonExpr e := do shareCommon (← canon e)
  synthInstance? e := Grind.synthInstance? e

/-- The `Sym.Arith` classification record of the current non-commutative semiring. -/
protected def NonCommSemiringM.getSemiring : NonCommSemiringM Sym.Arith.Semiring := do
  let s ← getArithState
  let semiringId := (← read).semiringId
  if h : semiringId < s.ncSemirings.size then
    return s.ncSemirings[semiringId]
  else
    throwError "`grind` internal error, invalid semiringId"

protected def NonCommSemiringM.modifySemiring (f : Sym.Arith.Semiring → Sym.Arith.Semiring) : NonCommSemiringM Unit := do
  let semiringId := (← read).semiringId
  modifyArithState fun s => { s with ncSemirings := s.ncSemirings.modify semiringId f }

instance : MonadSemiring NonCommSemiringM where
  getSemiring := NonCommSemiringM.getSemiring
  modifySemiring := NonCommSemiringM.modifySemiring

/-- The per-goal solver state of the current non-commutative semiring. -/
protected def NonCommSemiringM.getSemiringState : NonCommSemiringM SemiringState := do
  return (← get').getNCSemiring (← read).semiringId

protected def NonCommSemiringM.modifySemiringState (f : SemiringState → SemiringState) : NonCommSemiringM Unit := do
  let semiringId := (← read).semiringId
  modify' fun s => s.modifyNCSemiring semiringId f

instance : MonadSemiringState NonCommSemiringM where
  getSemiringState := NonCommSemiringM.getSemiringState
  modifySemiringState := NonCommSemiringM.modifySemiringState

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

/--
Semiring terms are reified only by the `internalize` hook, after the core has created the
`ENode`s of the term and of all its subterms. So every variable created here is already
internalized, and there is no generation to assign.
-/
instance : MonadMkVar NonCommSemiringM where
  mkVar e := do
    unless (← alreadyInternalized e) do
      throwError "`grind` internal error, semiring term has not been internalized{indentExpr e}"
    mkSVarCore e

end Lean.Meta.Grind.Arith.CommRing
