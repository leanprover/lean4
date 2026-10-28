/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module
prelude
public import Lean.Meta.Tactic.BVDecide.Prover.Cegar.Basic
public import Lean.Cadical.Internal -- TODO: temporary fix
import Lean.Meta.Sym.InferType
import Lean.Meta.Tactic.BVDecide.Prover.Bitblast
import Lean.Meta.Tactic.BVDecide.External

/-!
This module contains the incremental BitVec theory solver for the CEGAR loop. It implements
incremental bitblasting, CNF generation and SAT solving. Once it determines UNSAT it will construct
a proof for the goal and close it by contradiction.
-/

namespace Lean.Meta.Tactic.BVDecide

open Std.Sat
open Std.Tactic.BVDecide
open Std.Tactic.BVDecide.Reflect

/--
A general purpose incremental bitblaster with a classic SMT style push/pop/solve interface
-/
public structure BitVecSolverState where
  /--
  The bitblasting state.
  -/
  bitvecState : CegarM.BitVecState
  /--
  The incremental SAT solver.
  -/
  satSolver : Cadical.Solver
  /--
  Remaining time budget of this solver in milliseconds.
  -/
  solverTimeBudgetMs : Nat
  /--
  The assumption stack.
  -/
  assumptions : Array (Array (Nat × Bool))

public abbrev BvSolverM := ReaderT TacticContext StateRefT BitVecSolverState Sym.SymM

namespace BvSolverM

public def run (ctx : TacticContext) (state : BitVecSolverState) (x : BvSolverM α) :
    Sym.SymM (α × BitVecSolverState) := do
  StateRefT'.run (ReaderT.run x ctx) state

@[inline]
def takeBVState : BvSolverM CegarM.BitVecState := do
  modifyGet fun s => (s.bitvecState, { s with bitvecState := {} })

@[inline]
def setBVState (bitvecState : CegarM.BitVecState) : BvSolverM Unit :=
  modify fun s => { s with bitvecState }

@[inline]
def getSolverTime : BvSolverM Nat := do
  return (← get).solverTimeBudgetMs

@[inline]
def consumeSolverTime (ms : Nat) : BvSolverM Unit := do
  modify fun s => { s with solverTimeBudgetMs := s.solverTimeBudgetMs - ms }

def pushNewCnf (prevCnfSize : Nat) (current : CNF Nat) : BvSolverM Unit := do
  let satSolver := (← get).satSolver
  for clause in current.clauses[prevCnfSize...*] do
    satSolver.clause clause

def getAssignment : BvSolverM (Array (Bool × Nat)) := do
  let satSolver := (← get).satSolver
  let aigSize := (← get).bitvecState.aig.decls.size
  let mut model := Array.emptyWithCapacity aigSize
  for idx in 0...aigSize do
    let value ← satSolver.val idx
    model := model.push (value, idx)
  return model

def runSatSolver : BvSolverM Cadical.Status := do
  let solver := (← get).satSolver
  let solveTask ← BaseIO.asTask solver.solve .dedicated
  let mut sleepMs := 1
  let maxSleepMs := 64
  while (← IO.getTaskState solveTask) != .finished do
    if (← getSolverTime) == 0 then
      solver.terminate
      break
    if let some tk := (← readThe Core.Context).cancelTk? then
      if ← tk.isSet then
        solver.terminate
        throwInterruptException
    IO.sleep sleepMs.toUInt32
    consumeSolverTime sleepMs
    sleepMs := if sleepMs ≥ maxSleepMs then sleepMs else sleepMs * 2
  return solveTask.get

public def push (bvExprs : Array BVLogicalExpr) : BvSolverM Unit := do
  let level ← bvExprs.mapM addExpr
  modify fun s => { s with assumptions := s.assumptions.push level }
where
  addExpr (bvExpr : BVLogicalExpr) : BvSolverM (Nat × Bool) := do
    let ⟨aig, bbCache, cnfCache⟩ ← takeBVState
    let prevAigSize := aig.decls.size
    let blastResult : { ret : Return aig // AIG.IsPrefix aig.decls ret.result.1.aig.decls } ←
      withTraceNode `Meta.Tactic.bv (fun _ => return "Bitblasting BVLogicalExpr to AIG") do
        -- lazyPure to prevent compiler lifting
        IO.lazyPure (fun _ =>
          let res := bvExpr.bitblastWithCache aig bbCache
          ⟨res, BVLogicalExpr.bitblastWithCache_isPrefix_aig⟩
        )
    let ret := blastResult.1
    let bbCache := ret.cache
    let entry := ret.result.1
    let aig := entry.aig
    let aigSize := aig.decls.size
    trace[Meta.Tactic.bv] s!"AIG has {aigSize} nodes, added {aigSize - prevAigSize} nodes this round"

    if (← read).config.graphviz then
      IO.FS.writeFile ("." / "aig.gv") <| AIG.toGraphviz entry


    let prevCnfSize := cnfCache.cnf.clauses.size
    let cnfCache := cnfCache.cast blastResult.2
    let cnfCache ←
      withTraceNode `Meta.Tactic.sat (fun _ => return "Converting AIG to CNF") do
        -- lazyPure to prevent compiler lifting
        IO.lazyPure (fun _ => AIG.toCNF' entry cnfCache)
    let cnfSize := cnfCache.cnf.clauses.size
    trace[Meta.Tactic.bv] s!"CNF has {cnfSize} clauses, added {cnfSize - prevCnfSize} clauses this round"

    setBVState ⟨entry.aig, bbCache, cnfCache⟩

    pushNewCnf prevCnfSize cnfCache.cnf
    return (entry.ref.gate, !entry.ref.invert)

public def pop : BvSolverM Unit := do
  modify fun s => { s with assumptions := s.assumptions.pop }

public def solve : BvSolverM (Except (Array (Bool × Nat)) Unit) := do
  let solver := (← get).satSolver
  (← get).assumptions.forM fun level => level.forM fun (lit, pol) => solver.assume lit pol
  let status ← withTraceNode `Meta.Tactic.sat (fun _ => return m!"Running incremental SAT solver") do
    runSatSolver
  match status with
  | .satisfiable => return .error (← getAssignment)
  | .unsatisfiable => return .ok ()
  | .unknown => External.throwSatTimeout

end BvSolverM

def liftBvSolverM (x : BvSolverM α) : CegarM α := do
  let ctx ← CegarM.getTacticContext
  let state ← modifyGet fun s =>
    let state := {
      bitvecState := s.theoryState.bitvecState
      satSolver := s.theoryState.satSolver
      solverTimeBudgetMs := s.solverTimeBudgetMs
      assumptions := #[]
    }
    (state, { s with theoryState.bitvecState := {} })
  let (x, state) ← BvSolverM.run ctx state x
  modify fun s =>
    { s with
        theoryState.bitvecState := state.bitvecState
        solverTimeBudgetMs := state.solverTimeBudgetMs
    }
  return x

public def Cegar.checkBitVec :
    CegarM (Except (Array (Expr × Bool × BVExpr.PackedBitVec)) LratCert) := do
  withTraceNode `Meta.Tactic.bv (fun _ => return m!"Checking BitVec abstraction") do
    let bvExpr := (← get).satExpr.bvExpr
    let res ← liftBvSolverM do
      BvSolverM.push #[bvExpr]
      BvSolverM.solve
    match res with
    | .ok .. =>
      /-
      At this point we drop the theory related caches as the `lratBitblaster` will rebuild them from
      scratch and we would just waste memory still keeping them around.
      -/
      CegarM.clearCaches
      let res ← lratBitblaster (← CegarM.getTacticContext) (← read).goal (← CegarM.getReflectionResult)
      match res with
      | .ok cert => return .ok cert
      | .error _ => throwError m!"Error during proof recovery"
    | .error assignment =>
      let atomsAssignment ← ReifyM.atomsAssignmentMap
      let aig := (← CegarM.getTheoryState).bitvecState.aig
      let equations := reconstructCounterExample aig assignment atomsAssignment
      return .error equations

end Lean.Meta.Tactic.BVDecide
