/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Std.Sat.AIG.CNF
import Std.Sat.AIG.RelabelNat
import Std.Tactic.BVDecide.Bitblast
import Std.Tactic.BVDecide.Syntax
import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide.SatAtBVLogical
import Lean.Elab.Tactic.BVDecide.Frontend.Normalize
import Lean.Elab.Tactic.BVDecide.Frontend.LRAT

/-!
This module provides the implementation of the `bv_decide` frontend itself.
-/

namespace Lean.Elab.Tactic.BVDecide
namespace Frontend

open Std.Sat
open Std.Tactic.BVDecide
open Std.Tactic.BVDecide.Reflect
open Lean.Meta

/--
Given:
- `var2Cnf`: The mapping from AIG to CNF variables.
- `assignments`: A model for the CNF as provided by a SAT solver.
- `aigSize`: The amount of nodes in the AIG that was used to produce the CNF.
- `atomsAssignment`: The mapping of the reflection monad from atom indices to `Expr`.

Reconstruct bit by bit which value expression must have had which `BitVec` value and return all
expression - pair values.
-/
def reconstructCounterExample (var2Cnf : Std.HashMap BVBit Nat) (assignment : Array (Bool × Nat))
    (aigSize : Nat) (atomsAssignment : Std.HashMap Nat Expr) :
    Array (Expr × BVExpr.PackedBitVec) := Id.run do
  let mut sparseMap : Std.HashMap Nat (RBMap Nat Bool Ord.compare) := {}
  for (bitVar, cnfVar) in var2Cnf.toArray do
    /-
    The setup of the variables in CNF is as follows:
    1. One auxiliary variable for each node in the AIG
    2. The actual BitVec bitwise variables
    Hence we access the assignment array offset by the AIG size to obtain the value for a BitVec bit.
    We assume that a variable can be found at its index as CaDiCal prints them in order.
    -/
    let (varSet, _) := assignment[cnfVar + aigSize]!
    let mut bitMap := sparseMap.getD bitVar.var {}
    bitMap := bitMap.insert bitVar.idx varSet
    sparseMap := sparseMap.insert bitVar.var bitMap

  let mut finalMap := #[]
  for (bitVecVar, bitMap) in sparseMap.toArray do
    let mut value : Nat := 0
    let mut currentBit := 0
    for (bitIdx, bitValue) in bitMap.toList do
      assert! bitIdx == currentBit
      if bitValue then
        value := value ||| (1 <<< currentBit)
      currentBit := currentBit + 1
    let atomExpr := atomsAssignment.get! bitVecVar
    finalMap := finalMap.push (atomExpr, ⟨BitVec.ofNat currentBit value⟩)
  return finalMap

structure UnsatProver.Result where
  proof : Expr
  lratCert : LratCert

abbrev UnsatProver := BVLogicalExpr → Std.HashMap Nat Expr → MetaM UnsatProver.Result

def lratBitblaster (cfg : TacticContext) (bv : BVLogicalExpr)
    (atomsAssignment : Std.HashMap Nat Expr) :
    MetaM UnsatProver.Result := do
  let entry ←
    withTraceNode `bv (fun _ => return "Bitblasting BVLogicalExpr to AIG") do
      -- lazyPure to prevent compiler lifting
      IO.lazyPure (fun _ => bv.bitblast)
  let aigSize := entry.aig.decls.size
  trace[Meta.Tactic.bv] s!"AIG has {aigSize} nodes."

  if cfg.graphviz then
    IO.FS.writeFile ("." / "aig.gv") <| AIG.toGraphviz entry

  let (cnf, map) ←
    withTraceNode `sat (fun _ => return "Converting AIG to CNF") do
      -- lazyPure to prevent compiler lifting
      IO.lazyPure (fun _ =>
        let (entry, map) := entry.relabelNat'
        let cnf := AIG.toCNF entry
        (cnf, map)
      )

  let res ←
    withTraceNode `sat (fun _ => return "Obtaining external proof certificate") do
      runExternal cnf cfg.solver cfg.lratPath cfg.trimProofs cfg.timeout cfg.binaryProofs

  match res with
  | .ok cert =>
    let proof ← cert.toReflectionProof cfg bv ``verifyBVExpr ``unsat_of_verifyBVExpr_eq_true
    return ⟨proof, cert⟩
  | .error assignment =>
    let reconstructed := reconstructCounterExample map assignment aigSize atomsAssignment
    let mut error := m!"The prover found a potential counterexample, consider the following assignment:\n"
    for (var, value) in reconstructed do
      error := error ++ m!"{var} = {value.bv}\n"
    throwError error

def reflectBV (g : MVarId) : M (BVLogicalExpr × (Expr → M Expr)) := g.withContext do
  let hyps ← getLocalHyps
  let sats ← hyps.filterMapM SatAtBVLogical.of
  if sats.size = 0 then
    let mut error := "None of the hypotheses are in the supported BitVec fragment.\n"
    error := error ++ "There are two potential fixes for this:\n"
    error := error ++ "1. If you are using custom BitVec constructs simplify them to built-in ones.\n"
    error := error ++ "2. If your problem is using only built-in ones it might currently be out of reach.\n"
    error := error ++ "   Consider expressing it in terms of different operations that are better supported."
    throwError error
  let sat := sats.foldl (init := SatAtBVLogical.trivial) SatAtBVLogical.and
  return (sat.bvExpr, sat.proveFalse)

def closeWithBVReflection (g : MVarId) (unsatProver : UnsatProver) :
    MetaM LratCert := M.run do
  g.withContext do
    let (bvLogicalExpr, f) ←
      withTraceNode `bv (fun _ => return "Reflecting goal into BVLogicalExpr") do
        reflectBV g
    trace[Meta.Tactic.bv] "Reflected bv logical expression: {bvLogicalExpr}"

    let atomsPairs := (← getThe State).atoms.toList.map (fun (expr, _, ident) => (ident, expr))
    let atomsAssignment := Std.HashMap.ofList atomsPairs
    let ⟨bvExprUnsat, cert⟩ ← unsatProver bvLogicalExpr atomsAssignment
    let proveFalse ← f bvExprUnsat
    g.assign proveFalse
    return cert

def bvUnsat (g : MVarId) (cfg : TacticContext) : MetaM LratCert := M.run do
  let unsatProver : UnsatProver := fun bvExpr atomsAssignment => do
    withTraceNode `bv (fun _ => return "Preparing LRAT reflection term") do
      lratBitblaster cfg bvExpr atomsAssignment
  closeWithBVReflection g unsatProver

structure Result where
  simpTrace : Simp.Stats
  lratCert : Option LratCert

def bvDecide (g : MVarId) (cfg : TacticContext) : MetaM Result := do
  let ⟨g?, simpTrace⟩ ← Normalize.bvNormalize g
  let some g := g? | return ⟨simpTrace, none⟩
  let lratCert ← bvUnsat g cfg
  return ⟨simpTrace, some lratCert⟩

@[builtin_tactic Lean.Parser.Tactic.bvDecide]
def evalBvTrace : Tactic := fun
  | `(tactic| bv_decide) => do
    IO.FS.withTempFile fun _ lratFile => do
      let cfg ← BVDecide.Frontend.TacticContext.new lratFile
      liftMetaFinishingTactic fun g => do
        discard <| bvDecide g cfg
  | _ => throwUnsupportedSyntax

end Frontend
end Lean.Elab.Tactic.BVDecide

