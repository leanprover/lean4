/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Lean.Elab.Tactic.Location
import Lean.Meta.Tactic.Replace
import Lean.Meta.Tactic.Rewrites

/-!
# The `rewrites` tactic.

`rw?` tries to find a lemma which can rewrite the goal.

`rw?` should not be left in proofs; it is a search tool, like `apply?`.

Suggestions are printed as `rw [h]` or `rw [← h]`.

-/
namespace Lean.Elab.Rewrites

open Lean Meta Rewrites
open Lean.Parser.Tactic

open Lean Elab Tactic

@[builtin_tactic Lean.Parser.Tactic.rewrites?]
def evalExact : Tactic := fun stx => do
  let `(tactic| rw?%$tk $[$loc]? $[[ $[-$forbidden],* ]]?) := stx
        | throwUnsupportedSyntax
  let moduleRef ← createModuleTreeRef
  let forbidden : NameSet :=
    ((forbidden.getD #[]).map Syntax.getId).foldl (init := ∅) fun s n => s.insert n
  reportOutOfHeartbeats `findRewrites tk
  let goal ← getMainGoal
  withLocation (expandOptLocation (Lean.mkOptionalNode loc))
    fun f => do
      let some a ← f.findDecl? | return
      if a.isImplementationDetail then return
      let target ← instantiateMVars (← f.getType)
      let hyps ← localHypotheses (except := [f])
      let results ← findRewrites hyps moduleRef goal target (stopAtRfl := false) forbidden
      reportOutOfHeartbeats `rewrites tk
      if results.isEmpty then
        throwError "Could not find any lemmas which can rewrite the hypothesis {← f.getUserName}"
      for r in results do withMCtx r.mctx do
        Tactic.TryThis.addRewriteSuggestion tk [(r.expr, r.symm)]
          r.result.eNew (loc? := .some (.fvar f)) (origSpan? := ← getRef)
      if let some r := results[0]? then
        setMCtx r.mctx
        let replaceResult ← goal.replaceLocalDecl f r.result.eNew r.result.eqProof
        replaceMainGoal (replaceResult.mvarId :: r.result.mvarIds)
    do
      let target ← instantiateMVars (← goal.getType)
      let hyps ← localHypotheses
      let results ← findRewrites hyps moduleRef goal target (stopAtRfl := true) forbidden
      reportOutOfHeartbeats `rewrites tk
      if results.isEmpty then
        throwError "Could not find any lemmas which can rewrite the goal"
      results.forM (·.addSuggestion tk)
      if let some r := results[0]? then
        setMCtx r.mctx
        replaceMainGoal
          ((← goal.replaceTargetEq r.result.eNew r.result.eqProof) :: r.result.mvarIds)
        evalTactic (← `(tactic| try rfl))
    (fun _ => throwError "Failed to find a rewrite for some location")

end Lean.Elab.Rewrites
