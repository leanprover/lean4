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
public import Lean.Meta.Tactic.BVDecide.Prover.Cegar.Lemmas
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

  cegarLoop : UnsatProver CegarCert := CegarM.run ctx do
    let mut lastCex := #[]
    CegarM.setDidChange true
    configureSolver
    while ← CegarM.getDidChange do
      checkTermination
      match ← checkBitVec with
      | .ok cert =>
        return .ok (← CegarM.createCert cert)
      | .error cex =>
        lastCex := cex
        let cex ← CegarM.CounterExample.ofArray cex
        discard <| checkUf cex

      match ← processNewHyps with
      | .solved => return .ok (← CegarM.createCert none)
      | .newHyps => CegarM.setDidChange true
      | .none => CegarM.setDidChange false

    let equations := lastCex.filterMap fun (lhs, synth, rhs) =>
      if synth then none else some (lhs, rhs)

    let funState := (← getThe BVDecide.State).theoryState.funState
    return .error {
      goal := (← read).goal,
      unusedHypotheses := (← read).unusedHypotheses,
      equations := equations
      functionAtoms := funState.atoms.map (·.funExpr)
    }

  configureSolver : CegarM Unit := do
    let solver ← CegarM.getSatSolver
    let opts := External.SatOptions.ofMode (← CegarM.getTacticContext).config.solverMode
    let opts := opts.addIncremental
    opts.configureSolver solver

end Lean.Meta.Tactic.BVDecide
