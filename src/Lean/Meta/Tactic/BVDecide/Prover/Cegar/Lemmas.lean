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
TODO
-/

namespace Lean.Meta.Tactic.BVDecide

public inductive ProcessHypResult where
  | solved
  | newHyps
  | none

public def Cegar.processNewHyps : CegarM ProcessHypResult := do
  let hypQueue ← CegarM.drainNewHyps
  if hypQueue.isEmpty then return .none
  let params ← Grind.mkDefaultParams {}
  -- TODO: think about carrying over caches
  let target := .mvarIdTarget (← read).goal
  let ctx := (← CegarM.getTacticContext).preProcessContext
  let (solved, state) ← Grind.GrindM.run (params := params) <| Normalize.PreProcessM.run ctx target do
    Normalize.bvNormalize hypQueue
  if solved then return .solved
  let hypQueue := state.hypotheses

  let mut sats := #[]
  for hyp in hypQueue do
    checkSystem "bv_decide"
    -- TODO: think about repeated lemmas
    if let (some reflected, lemmas) ← (SatAtBVLogical.of hyp).run then
      sats := (sats ++ lemmas).push reflected
    else
      throwError m!"Failed to reify CEGAR lemma {hyp}"

  let sat ← sats.foldlM (init := (← get).satExpr) (SatAtBVLogical.and · ·)
  modify fun s => { s with satExpr := sat, newHypotheses := s.newHypotheses.insertMany hypQueue }
  return .newHyps

end Lean.Meta.Tactic.BVDecide

