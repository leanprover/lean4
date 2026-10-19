/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module
prelude
public import Lean.Meta.Tactic.BVDecide.Prover.Cegar.Basic
public import Lean.Meta.Tactic.BVDecide.Prover.Cegar.BitVec
public import Lean.Meta.Tactic.BVDecide.Prover.Cegar.Function
public import Lean.Meta.Tactic.BVDecide.Prover.Cegar.Epr
public import Lean.Meta.Tactic.BVDecide.Prover.Cegar.Lemmas
public import Lean.Meta.Tactic.BVDecide.Prover.Cegar.Subsolver
import Lean.Meta.Tactic.BVDecide.Prover.Bitblast
import Lean.Meta.Tactic.BVDecide.External

/-!
This module contains the implementation of the lemmas on demand solver used by bv_decide.
-/

namespace Lean.Meta.Tactic.BVDecide

open Cegar in
public def cegarBlaster (ctx : TacticContext) : UnsatProver CegarCert :=
  if ctx.config.needsIncremental then
    cegarLoop
  else
    (lratBitblaster ctx).map CegarCert.ofLratCert
where
  checkTermination : CegarM Unit := do
    checkSystem "bv_decide"
    if (← CegarM.getRounds) == 0 then
      throwError m!"bv_decide reached its round limit, consider increasing it via the `cegarRounds` config option"
    CegarM.consumeRound

  cegarStep (lastCex : Array (Expr × Bool × Std.Tactic.BVDecide.BVExpr.PackedBitVec)) :
      CegarM (Except (Array (Expr × Bool × Std.Tactic.BVDecide.BVExpr.PackedBitVec)) CegarCert) :=
    withTraceNode `Meta.Tactic.bv (fun _ => return "CEGAR step") do
      checkTermination
      match ← checkBitVec with
      | .ok cert =>
        return .ok (← CegarM.createCert cert)
      | .error cex =>
        if lastCex == cex then
          throwError m!"Model did not change, TODO"
        let nextCex := cex
        traceModel nextCex
        let processedCex ← CegarM.CounterExample.ofArray nextCex
        checkTheories processedCex
        return .error nextCex

  cegarLoop : UnsatProver CegarCert := CegarM.run ctx do
    let mut lastCex := #[]
    CegarM.setDidChange true
    configureSolver
    while ← CegarM.getDidChange do
      match ← cegarStep lastCex with
      | .ok cert => return .ok cert
      | .error cex =>
        lastCex := cex

      match ← processNewHyps with
      | .solved => return .ok (← CegarM.createCert none)
      | .newHyps => CegarM.setDidChange true
      | .none => CegarM.setDidChange false

    let equations ← mkEquations lastCex

    let funState := (← getThe BVDecide.State).theoryState.funState
    return .error {
      goal := (← read).goal,
      unusedHypotheses := (← read).unusedHypotheses,
      equations := equations
      functionAtoms := funState.atoms.map (·.funExpr)
    }

  traceModel (cex : Array (Expr × Bool × Std.Tactic.BVDecide.BVExpr.PackedBitVec)) : CegarM Unit := do
    withTraceNode `Meta.Tactic.bv (fun _ => return m!"Model found") do
      for (lhs, rhs) in ← mkEquations cex do
        trace[Meta.Tactic.bv] m!"{lhs} = {rhs.bv}"

  mkEquations (cex : Array (Expr × Bool × Std.Tactic.BVDecide.BVExpr.PackedBitVec)) :
      CegarM (Array (Expr × Std.Tactic.BVDecide.BVExpr.PackedBitVec)) := do
    return cex.filterMap fun (lhs, synth, rhs) =>
      if synth then none else some (lhs, rhs)

  checkTheories (cex : CegarM.CounterExample) : CegarM Unit := do
    if ← checkUf cex then return ()
    if ← checkEpr cex then return ()

  configureSolver : CegarM Unit := do
    let solver ← CegarM.getSatSolver
    let opts := External.SatOptions.ofMode (← CegarM.getTacticContext).config.solverMode
    let opts := opts.addIncremental
    opts.configureSolver solver

end Lean.Meta.Tactic.BVDecide
