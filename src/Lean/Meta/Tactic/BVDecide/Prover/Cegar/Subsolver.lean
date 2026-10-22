/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module
prelude
public import Lean.Meta.Tactic.BVDecide.Prover.Cegar.Basic
public import Lean.Meta.Tactic.BVDecide.Prover.Cegar.BitVec
public import Lean.Meta.Tactic.BVDecide.Normalize
import Lean.Meta.Tactic.BVDecide.External

/-!
This file implements a subsolver that is capable of incrementally processing QF_BV queries with
pre-processing and incremental bitblasting. The solver is explicitly itself not a CEGAR loop with
support for other theories but instead supposed to be used as a building block for other theories.
-/

namespace Lean.Meta.Tactic.BVDecide

open Std.Tactic.BVDecide

namespace Cegar

/--
An incremental bitvector subsolver with a classic SMT push/pop/solve API. Supports incremental
pre-processing and bitblasting but no theories beyond bitvectors.
-/
public structure Subsolver where
  /--
  Incremental reification state.
  -/
  reifyState : BVDecide.State
  /--
  Incremental caches for the rewrites in the pre-processor.
  -/
  preProcessState : Grind.BVDecide.Caches
  /--
  Incremental BitVEc solver state, this tracks the assumption levels.
  -/
  bvSolver : BitVecSolverState
  /--
  The goal we are operating in.
  -/
  mvar : MVarId
  /--
  General bv_decide configuration.
  -/
  ctx : TacticContext

public abbrev SubsolverT {σ : Type} (m : Type → Type) [STWorld σ m] (α : Type) := StateRefT Subsolver m α

/--
Create a subsolver for hypotheses in the local context of `mvar`. It performs neither theory
refinement nor the preprocessing passes that are disabled for CEGAR lemmas.
-/
public def Subsolver.new (ctx : TacticContext) (mvar : MVarId) : Sym.SymM Subsolver := do
  let ctx := { ctx with
    config := { ctx.config with
      enums := false
      structures := false
      fixedInt := false
      shortCircuit := false
      uf := false
      epr := false
    }
  }
  let satSolver ← Cadical.Solver.new
  let opts := External.SatOptions.ofMode ctx.config.solverMode |>.addIncremental
  opts.configureSolver satSolver
  return {
    reifyState := {}
    preProcessState := {}
    bvSolver := {
      bitvecState := {}
      satSolver
      solverTimeBudgetMs := ctx.config.timeout * 1000
      assumptions := #[]
    }
    mvar
    ctx
  }

namespace SubsolverT

variable {σ : Type} {m : Type → Type}
variable [STWorld σ m] [Monad m] [MonadLiftT Sym.SymM m] [MonadLiftT Grind.GrindM m] [MonadLiftT (ST σ) m]

def liftBvSolverM (x : BvSolverM α) : SubsolverT m α := do
  let ctx := (← get).ctx
  let bvSolver ← modifyGet fun s => (s.bvSolver, { s with bvSolver.bitvecState := {} })
  let (a, bvSolver) ← BvSolverM.run ctx bvSolver x
  modify fun s => { s with bvSolver }
  return a

def liftReifyM (x : ReifyM α) : SubsolverT m α := do
  let config := (← get).ctx.config
  let reifyState ← modifyGet fun s => (s.reifyState, { s with reifyState := {} })
  let (a, reifyState) ← liftM (m := Grind.GrindM) <|
    StateRefT'.run (ReaderT.run x { hypotheses := #[], config }) reifyState
  modify fun s => { s with reifyState }
  return a

def liftPreProcessM (x : Normalize.PreProcessM α) : SubsolverT m α := do
  let ctx := (← get).ctx.preProcessContext
  let ctx := .new ctx.mode ctx.config true
  let mvar := (← get).mvar
  let caches ← modifyGet fun s => (s.preProcessState, { s with preProcessState := {} })
  let (a, state) ← liftM (m := Grind.GrindM) do
    let target ← mvar.withContext <| mkFreshExprMVar (mkConst ``False)
    Normalize.PreProcessM.run ctx (.mvarIdTarget target.mvarId!) do
      Normalize.PreProcessM.setCaches caches
      x
  modify fun s => { s with preProcessState := state.caches }
  return a

/--
Push a new level of hypotheses `hyps` onto the solver stack. This already triggers pre-processing.
-/
public def push (hyps : Array Normalize.Hyp) : SubsolverT m Unit := do
  let preprocessResult ← liftPreProcessM do
      if ← Normalize.bvNormalize hyps then
        return none
      else
        return some (← Normalize.PreProcessM.getHyps)

  match preprocessResult with
  | some hyps =>
    let bvExprs ← liftReifyM do
      let (sats, lemmas) ← LemmaM.run do
        -- TODO: share with lemma file?
        hyps.filterMapM fun hyp => do
          checkSystem "bv_decide"
          if hyp.type.isConstOf ``True then return none
          let some reflected ← SatAtBVLogical.of hyp
            | throwError m!"Failed to reify subsolver hypothesis {hyp.type}"
          return some reflected
      return (lemmas ++ sats).map (·.bvExpr)
    liftBvSolverM <| BvSolverM.push bvExprs
  | none => liftBvSolverM <| BvSolverM.push #[.const false]

/--
Pop the most recent level of hypotheses from the solver stack.
-/
public def pop : SubsolverT m Unit := do
  liftBvSolverM BvSolverM.pop

/--
Check whether the currently pushed assumptions are UNSAT (`.ok ()`) or SAT (`.error model`)
incrementally.
-/
public def check : SubsolverT m (Except CegarM.CounterExample Unit) := do
  let res ← liftBvSolverM do BvSolverM.solve
  match res with
  | .ok _ => return .ok ()
  | .error assignment =>
    let atomsAssignment ← liftReifyM <| ReifyM.atomsAssignmentMap
    let aig := (← get).bvSolver.bitvecState.aig
    let cex := reconstructCounterExample aig assignment atomsAssignment
    let cex ← liftReifyM <| CegarM.CounterExample.ofArray cex
    return .error cex

public def run (ctx : TacticContext) (mvar : MVarId) (x : SubsolverT m α) : m α := do
  let solver ← Subsolver.new ctx mvar
  StateRefT'.run' x solver

end SubsolverT

end Cegar

end Lean.Meta.Tactic.BVDecide
