/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module
prelude
public import Lean.Meta.Tactic.BVDecide.Prover.Cegar.Basic
import Lean.Meta.Tactic.BVDecide.Normalize
import Lean.Meta.Tactic.Grind.Main

/-!
This module is responsible for draining the queue of new lemmas, pre-processing it and updating the
BitVec abstraction accordingly.
-/

namespace Lean.Meta.Tactic.BVDecide

public inductive ProcessHypResult where
  | solved
  | newHyps
  | none

public def Cegar.processNewHyps : CegarM ProcessHypResult := do
  withTraceNode `Meta.Tactic.bv (fun _ => return m!"Processing new lemmas") do
    let hypQueue ← CegarM.drainNewHyps
    if hypQueue.isEmpty then return .none
    let target := .mvarIdTarget (← read).goal
    let ctx := (← CegarM.getTacticContext).preProcessContext
    let ctx :=
      .new
        ctx.mode
        { ctx.config with
            enums := false,
            structures := false,
            fixedInt := false,
            shortCircuit := false
        }
        true
    let caches ← CegarM.takePreProcessCaches
    let (solved, state) ←
      Normalize.PreProcessM.run ctx target do
        Normalize.PreProcessM.setCaches caches
        Normalize.bvNormalize <| hypQueue.map (·.hyp)
    if solved then return .solved
    CegarM.setPreProcessCaches state.caches
    let hypQueue := state.hypotheses

    let mut sats := #[]
    for hyp in hypQueue do
      checkSystem "bv_decide"

      if hyp.type.isConstOf ``True then
        continue

      LemmaM.resetLemmas
      if let some reflected ← SatAtBVLogical.of hyp then
        let lemmas ← LemmaM.getLemmas
        sats := sats ++ lemmas |>.push reflected
      else
        throwError m!"Failed to reify CEGAR lemma {hyp}"

    if sats.isEmpty then
      return .none

    let sat ← sats.foldlM (init := (← get).satExpr) (SatAtBVLogical.and · ·)
    modify fun s => { s with satExpr := sat }
    return .newHyps

end Lean.Meta.Tactic.BVDecide

