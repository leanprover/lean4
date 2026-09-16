/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module
prelude
public import Lean.Meta.Tactic.BVDecide.Prover.Basic
public import Lean.Meta.Tactic.BVDecide.TacticContext
public import Lean.Cadical.Basic

/-!
This module provides the basic infrastructure for the CEGAR (Counter Example Guided Abstraction Refinement)
solver.
-/

namespace Lean.Meta.Tactic.BVDecide

open Std.Tactic.BVDecide

namespace CegarM

public structure Context where
  goal : MVarId
  unusedHypotheses : Std.HashSet Normalize.Hyp
  atomsAssignment : Std.HashMap Nat (Nat × Expr × Bool)
  tacticContext : TacticContext

public structure FunState where
  congrCache : Std.HashMap Sym.ExprPtr Expr := {}

public structure BitVecState where
  aig : Std.Sat.AIG BVBit := .empty
  blastCache : BVExpr.Cache aig := .empty
  cnfCache : Std.Sat.AIG.toCNF.State aig := .empty aig

public structure TheoryState where
  funState : FunState := {}
  bitvecState : BitVecState := {}
  satSolver : Cadical.Solver

def TheoryState.new : BaseIO TheoryState := do
  return { satSolver := ← Cadical.Solver.new }

public structure State where
  satExpr : SatAtBVLogical
  newHypotheses : Std.HashSet Normalize.Hyp := {}
  hypQueue : Array Normalize.Hyp := #[]
  didChange : Bool := true
  theoryState : TheoryState

end CegarM

public abbrev CegarM (α : Type) := ReaderT CegarM.Context StateRefT CegarM.State LemmaM α

namespace CegarM

public def getReflectionResult : CegarM ReflectionResult := do
  return {
    satExpr := (← get).satExpr
    unusedHypotheses := (← read).unusedHypotheses
  }

@[inline]
public def getDidChange : CegarM Bool := return (← get).didChange

@[inline]
public def setDidChange (v : Bool) : CegarM Unit := modify fun s => { s with didChange := v }

@[inline]
public def getTheoryState : CegarM TheoryState := return (← get).theoryState

@[inline]
public def modifyTheoryState (f : TheoryState → TheoryState) : CegarM Unit :=
  modify fun s => { s with theoryState := f s.theoryState }

@[inline]
public def pushNewHyp (hyp : Normalize.Hyp) : CegarM Unit :=
  modify fun s => { s with hypQueue := s.hypQueue.push hyp }

@[inline]
public def drainNewHyps : CegarM (Array Normalize.Hyp) :=
  modifyGet fun s => (s.hypQueue, { s with hypQueue := #[] })

@[inline]
public def getTacticContext : CegarM TacticContext := return (← read).tacticContext

@[inline]
public def hasRefinementProcedures : CegarM Bool := do
  let cfg := (← getTacticContext).config
  return cfg.uf

@[inline]
public def run (ctx : TacticContext) (x : CegarM (Except CounterExample α)) : UnsatProver α :=
  fun goal reflectionResult atomsAssignment => do
    let ctx := {
      goal := goal
      unusedHypotheses := reflectionResult.unusedHypotheses
      atomsAssignment := atomsAssignment
      tacticContext := ctx
    }
    let state := {
      satExpr := reflectionResult.satExpr
      theoryState := ← TheoryState.new
    }
    StateRefT'.run' (ReaderT.run x ctx) state

public def getSatSolver : CegarM Cadical.Solver := return (← get).theoryState.satSolver

public structure CounterExample where
  exprCex : Std.HashMap Expr BVExpr.PackedBitVec
  atomCex : Std.HashMap Nat BVExpr.PackedBitVec

public def CounterExample.ofArray (arr : Array (Expr × BVExpr.PackedBitVec)) : ReifyM CounterExample := do
  let exprCex := Std.HashMap.ofArray arr
  let mut atomCex := Std.HashMap.emptyWithCapacity arr.size
  for (expr, val) in arr do
    let some atom ← ReifyM.getAtomNumber expr | unreachable!
    atomCex := atomCex.insert atom val
  return { exprCex, atomCex }

end CegarM

end Lean.Meta.Tactic.BVDecide
