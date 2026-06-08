/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module
prelude

public import Lean.Meta.Tactic.BVDecide.Reflect
public import Lean.Meta.Tactic.BVDecide.Counterexample
public import Lean.Meta.Tactic.BVDecide.LRAT.Cert


/-!
This module provides the implementation of the `bv_decide` frontend itself.
-/
namespace Lean.Meta.Tactic.BVDecide

open Std.Sat
open Std.Tactic.BVDecide
open Std.Tactic.BVDecide.Reflect

public structure UnsatProver.Result (α : Type) where
  /--
  A proof that the input `BVLogicalExpr` of the `UnsatProver` is `Unsat`
  -/
  proof : Expr
  /--
  Potential meta data that can aid in squeezing the proof.
  Used by `bv_decide?` to exfiltrate the LRAT certificate to avoid calling the SAT solver again.
  -/
  cert : α

public structure ReflectionResult where
  /--
  The reflected expression.
  -/
  bvExpr : BVLogicalExpr
  /--
  Function to prove `False` given an unsatisfiability proof of `bvExpr`
  -/
  proveFalse : Expr → M Expr
  /--
  Set of unused hypotheses for diagnostic purposes.
  -/
  unusedHypotheses : Std.HashSet FVarId
  /--
  A cache for `toExpr bvExpr`.
  -/
  expr : Expr

public abbrev UnsatProver (α : Type) := MVarId → ReflectionResult → Std.HashMap Nat (Nat × Expr × Bool) →
    MetaM (Except CounterExample (UnsatProver.Result α))

public def reflectBV (g : MVarId) : M ReflectionResult := g.withContext do
  let hyps ← getPropHyps
  let mut sats := #[]
  let mut unusedHypotheses := {}
  for hyp in hyps do
    checkSystem "bv_decide"
    if let (some reflected, lemmas) ← (SatAtBVLogical.of (mkFVar hyp)).run then
      sats := (sats ++ lemmas).push reflected
    else
      unusedHypotheses := unusedHypotheses.insert hyp
  if h : sats.size = 0 then
    let mut error := "None of the hypotheses are in the supported BitVec fragment after applying preprocessing.\n"
    error := error ++ "There are three potential reasons for this:\n"
    error := error ++ "1. If you are using custom BitVec constructs simplify them to built-in ones.\n"
    error := error ++ "2. If your problem is using only built-in ones it might currently be out of reach.\n"
    error := error ++ "   Consider expressing it in terms of different operations that are better supported.\n"
    error := error ++ "3. The original goal was reduced to False and is thus invalid."
    throwError error
  else
    let sat := sats[1...*].foldl (init := sats[0]) SatAtBVLogical.and
    return {
      bvExpr := ShareCommon.shareCommon sat.bvExpr,
      proveFalse := sat.proveFalse,
      unusedHypotheses := unusedHypotheses,
      expr := sat.expr
    }

public def closeWithBVReflection (g : MVarId) (unsatProver : UnsatProver α) :
    MetaM (Except CounterExample α) := M.run do
  g.withContext do
    let reflectionResult ←
      withTraceNode `Meta.Tactic.bv (fun _ => return "Reflecting goal into BVLogicalExpr") do
        reflectBV g
    trace[Meta.Tactic.bv] "Reflected bv logical expression: {reflectionResult.bvExpr}"

    let atomsPairs := (← getThe State).atoms.toList.map fun (expr, {width, atomNumber, synthetic}) =>
      (atomNumber, (width, expr, synthetic))
    let atomsAssignment := Std.HashMap.ofList atomsPairs
    match ← unsatProver g reflectionResult atomsAssignment with
    | .ok ⟨bvExprUnsat, cert⟩ =>
      let proveFalse ← reflectionResult.proveFalse bvExprUnsat
      g.assign proveFalse
      return .ok cert
    | .error counterExample => return .error counterExample

end Lean.Meta.Tactic.BVDecide
