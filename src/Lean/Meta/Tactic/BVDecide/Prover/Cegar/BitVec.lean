/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module
prelude
public import Lean.Meta.Tactic.BVDecide.Prover.Cegar.Basic
import Lean.Meta.Sym.InferType
import Lean.Meta.Tactic.BVDecide.Prover.Bitblast

/-!
TODO
-/

namespace Lean.Meta.Tactic.BVDecide

open Std.Sat
open Std.Tactic.BVDecide
open Std.Tactic.BVDecide.Reflect

@[inline]
def takeBVState : CegarM CegarM.BitVecState := do
  let state := (← CegarM.getTheoryState).bitvecState
  CegarM.modifyTheoryState fun ts => { ts with bitvecState := {} }
  return state

@[inline]
def setBVState (s : CegarM.BitVecState) : CegarM Unit :=
  CegarM.modifyTheoryState fun ts => { ts with bitvecState := s }

def pushNewCnf (prevCnfSize : Nat) (current : CNF Nat) : CegarM Unit := do
  let satSolver ← CegarM.getSatSolver
  for clause in current.clauses[prevCnfSize...*] do
    satSolver.clause clause

def getAssignment (aigSize : Nat) : CegarM (Array (Bool × Nat)) := do
  let satSolver ← CegarM.getSatSolver
  let mut model := Array.emptyWithCapacity aigSize
  for idx in 0...aigSize do
    let value ← satSolver.val idx
    model := model.push (value, idx)
  return model

public def Cegar.checkBitVec :
    CegarM (Except (Array (Expr × BVExpr.PackedBitVec)) LratCert) := do
  let ctx ← CegarM.getTacticContext
  let bvExpr := (← get).satExpr.bvExpr
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

  if ctx.config.graphviz then
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
  let satSolver ← CegarM.getSatSolver
  satSolver.assume entry.ref.gate !entry.ref.invert
  -- TODO: this needs to be made interruptible
  let status ← satSolver.solve

  match status with
  | .satisfiable =>
    trace[Meta.Tactic.sat] "SAT solver found a counter example."
    let assignment ← getAssignment aigSize
    let equations := reconstructCounterExample entry.aig assignment (← read).atomsAssignment
    return .error equations
  | .unsatisfiable =>
    let res ← lratBitblaster ctx (← read).goal (← CegarM.getReflectionResult) (← read).atomsAssignment
    match res with
    | .ok cert => return .ok cert
    | .error _ => throwError m!"Error during proof recovery"
    throwError m!"SAT solver reports UNSAT"
  | .unknown => throwError m!"SAT solver timed out"

end Lean.Meta.Tactic.BVDecide
