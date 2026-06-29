/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module
prelude

public import Lean.Meta.Tactic.BVDecide.Prover.Basic
public import Lean.Meta.Tactic.BVDecide.TacticContext
import Lean.Meta.Native


/-!
This module provides the implementation of the `bv_decide` frontend itself.
-/
namespace Lean.Meta.Tactic.BVDecide

open Std.Sat
open Std.Tactic.BVDecide
open Std.Tactic.BVDecide.Reflect

/--
Turn an `LratCert` into a proof that some `reflectedExpr` is UNSAT.
-/
def LratCert.toReflectionProof (cert : LratCert) (ctx : TacticContext)
    (reflectionResult : ReflectionResult) : MetaM Expr := do
  withTraceNode `Meta.Tactic.sat (fun _ => return "Compiling expr term") do
    mkAuxDecl ctx.exprDef reflectionResult.expr (mkConst ``BVLogicalExpr)

  withTraceNode `Meta.Tactic.sat (fun _ => return "Compiling proof certificate term") do
    mkAuxDecl ctx.certDef (toExpr cert) (mkConst ``String)

  let reflectedExpr := mkConst ctx.exprDef
  let certExpr := mkConst ctx.certDef
  let reflectionTerm := mkApp2 (mkConst ``verifyBVExpr) reflectedExpr certExpr

  withTraceNode `Meta.Tactic.sat (fun _ => return "Compiling and evaluating reflection proof term") do
    match (← nativeEqTrue `bv_decide reflectionTerm (axiomDeclRange? := (← getRef))) with
    | .notTrue =>
      throwError m!"Tactic `bv_decide` failed: The LRAT certificate could not be verified; \
        evaluating the following term returned `false`:{indentExpr reflectionTerm}"
    | .success auxProof =>
      return mkApp3 (mkConst ``unsat_of_verifyBVExpr_eq_true) reflectedExpr certExpr auxProof
where
  /--
  Add an auxiliary declaration. Only used to create constants that appear in our reflection proof.
  -/
  mkAuxDecl (name : Name) (value type : Expr) : CoreM Unit :=
    withOptions (fun opt => opt.set `compiler.extract_closed false) do
      addAndCompile <| .defnDecl {
        name := name,
        levelParams := [],
        type := type,
        value := value,
        hints := .abbrev,
        safety := .safe
      }

/--
Run a SAT solver to obtain an LRAT certificate and use it to produce a proof of UNSAT.
-/
public def lratBitblaster (ctx : TacticContext) : UnsatProver LratCert :=
  fun (goal : MVarId) (reflectionResult : ReflectionResult) (atomsAssignment : Std.HashMap Nat (Nat × Expr × Bool)) => do
  withTraceNode `Meta.Tactic.bv (fun _ => return "Preparing LRAT reflection term") do
    let bvExpr := reflectionResult.bvExpr
    let entry ←
      withTraceNode `Meta.Tactic.bv (fun _ => return "Bitblasting BVLogicalExpr to AIG") do
        -- lazyPure to prevent compiler lifting
        IO.lazyPure (fun _ => bvExpr.bitblast)
    let aigSize := entry.aig.decls.size
    trace[Meta.Tactic.bv] s!"AIG has {aigSize} nodes."

    if ctx.config.graphviz then
      IO.FS.writeFile ("." / "aig.gv") <| AIG.toGraphviz entry

    let (cnf, map) ←
      withTraceNode `Meta.Tactic.sat (fun _ => return "Converting AIG to CNF") do
        -- lazyPure to prevent compiler lifting
        IO.lazyPure (fun _ =>
          let (entry, map) := entry.relabelNat'
          let cnf := AIG.toCNF entry
          (cnf, map)
        )

    let res ←
      withTraceNode `Meta.Tactic.sat (fun _ => return "Obtaining external proof certificate") do
        runExternal
          cnf
          ctx.solver
          ctx.lratPath
          ctx.config.trimProofs
          ctx.config.timeout
          ctx.config.binaryProofs
          ctx.config.solverMode

    match res with
    | .ok cert =>
      trace[Meta.Tactic.sat] "SAT solver found a proof."
      let proof ← cert.toReflectionProof ctx reflectionResult
      return .ok ⟨proof, cert⟩
    | .error assignment =>
      trace[Meta.Tactic.sat] "SAT solver found a counter example."
      let equations := reconstructCounterExample map assignment aigSize atomsAssignment
      return .error { goal, unusedHypotheses := reflectionResult.unusedHypotheses, equations }


/--
Given a pre-existing LRAT certificate in `ctx.lratPath` use it to produce a proof of UNSAT.
-/
public def lratChecker (ctx : TacticContext) : UnsatProver Unit :=
  fun _ (reflectionResult : ReflectionResult) _ => do
  withTraceNode `Meta.Tactic.sat (fun _ => return "Preparing LRAT reflection term") do
    let cert ← LratCert.ofFile ctx.lratPath ctx.config.trimProofs
    let proof ← cert.toReflectionProof ctx reflectionResult
    return .ok ⟨proof, ()⟩

end Lean.Meta.Tactic.BVDecide
