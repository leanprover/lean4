/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Tactic.Rewrite
public import Lean.Meta.Tactic.Replace
public import Lean.Elab.Tactic.Location
import Lean.Meta.Eqns

public section

namespace Lean.Elab.Tactic
open Meta

/--
Runs `Lean.MVarId.rewrite`, and also handles filtering out the old metavariables in the rewrite result.
This should be used from within `withSynthesize`.
Use `finishElabRewrite` once elaboration is complete to make final updates to `RewriteResult`.
-/
def elabRewrite (mvarId : MVarId) (e : Expr) (stx : Syntax)
    (symm : Bool := false) (config := { : Rewrite.Config }) : TacticM RewriteResult := do
  let mvarCounterSaved := (← getMCtx).mvarCounter
  let thm ← elabTerm stx none true
  if thm.hasSyntheticSorry then
    throwAbortTactic
  unless ← occursCheck mvarId thm do
    throwErrorAt stx "Occurs check failed: Expression{indentExpr thm}\ncontains the goal {Expr.mvar mvarId}"
  let r ← mvarId.rewrite e thm symm (config := config)
  let mctx ← getMCtx
  let mvarIds := r.mvarIds.filter fun mvarId => (mctx.getDecl mvarId |>.index) >= mvarCounterSaved

  return { r with mvarIds }

/--
Makes new goals be synthetic opaque, to be done once elaboration of the rewrite theorem is complete.

Workaround note: we are only doing this for proof goals, not data goals,
since there are many downstream cases of tactic proofs that later assign data goals by unification.
-/
def finishElabRewrite (r : RewriteResult) : MetaM RewriteResult := do
  let mvarIds ← r.mvarIds.filterM (not <$> ·.isAssigned)
  mvarIds.forM fun newMVarId => newMVarId.withContext do
    if ← Meta.isProp (← newMVarId.getType) then
      newMVarId.setKind .syntheticOpaque
  return { r with mvarIds }

def rewriteTarget (stx : Syntax) (symm : Bool) (config : Rewrite.Config := {}) : TacticM Unit := do
  let r ← Term.withSynthesize <| withMainContext do
    elabRewrite (← getMainGoal) (← getMainTarget) stx symm (config := config)
  let r ← finishElabRewrite r
  let mvarId' ← (← getMainGoal).replaceTargetEq r.eNew r.eqProof
  replaceMainGoal (mvarId' :: r.mvarIds)

def rewriteLocalDecl (stx : Syntax) (symm : Bool) (fvarId : FVarId) (config : Rewrite.Config := {}) :
    TacticM Unit := withMainContext do
  -- Note: we cannot execute `replaceLocalDecl` inside `Term.withSynthesize`.
  -- See issues #2711 and #2727.
  let rwResult ← Term.withSynthesize <| withMainContext do
    let localDecl ← fvarId.getDecl
    elabRewrite (← getMainGoal) localDecl.type stx symm (config := config)
  let rwResult ← finishElabRewrite rwResult
  let replaceResult ← (← getMainGoal).replaceLocalDecl fvarId rwResult.eNew rwResult.eqProof
  replaceMainGoal (replaceResult.mvarId :: rwResult.mvarIds)

def withRWRulesSeq (token : Syntax) (rwRulesSeqStx : Syntax) (x : (symm : Bool) → (term : Syntax) → TacticM Unit) : TacticM Unit := do
  let lbrak := rwRulesSeqStx[0]
  let rules := rwRulesSeqStx[1].getArgs
  -- show initial state up to (incl.) `[`
  withTacticInfoContext (mkNullNode #[token, lbrak]) (pure ())
  let numRules := (rules.size + 1) / 2
  for i in *...numRules do
    let rule := rules[i * 2]!
    let sep  := rules.getD (i * 2 + 1) Syntax.missing
    -- show rule state up to (incl.) next `,`
    withTacticInfoContext (mkNullNode #[rule, sep]) do
      -- show errors on rule
      withRef rule do
        let symm := !rule[0].isNone
        let term := rule[1]
        let processId (id : Syntax) : TacticM Unit := do
          -- See if we can interpret `id` as a hypothesis first.
          if (← withMainContext <| Term.isLocalIdent? id).isSome then
            x symm term
          else
            -- Try to get equation theorems for `id`.
            let declName ← try realizeGlobalConstNoOverload id catch _ => return (← x symm term)
            let some eqThms ← getEqnsFor? declName | x symm term
            let hint := if eqThms.size = 1 then m!"" else
              .hint' m!"Try rewriting with `{Name.str declName unfoldThmSuffix}`"
            let rec go : List Name →  TacticM Unit
              | [] => throwError m!"Failed to rewrite using equation theorems for `{.ofConstName declName}`" ++ hint
              | eqThm::eqThms => (x symm (mkCIdentFrom id eqThm)) <|> go eqThms
            discard <| Term.addTermInfo id (← mkConstWithFreshMVarLevels declName) (lctx? := ← getLCtx)
            go eqThms.toList
        match term with
        | `($id:ident)  => processId id
        | `(@$id:ident) => processId id
        | _ => x symm term


declare_config_elab elabRewriteConfig Rewrite.Config

@[builtin_tactic Lean.Parser.Tactic.rewriteSeq] def evalRewriteSeq : Tactic := fun stx => do
  let cfg ← elabRewriteConfig stx[1]
  let loc   := expandOptLocation stx[3]
  withRWRulesSeq stx[0] stx[2] fun symm term => do
    withLocation loc
      (rewriteLocalDecl term symm · cfg)
      (rewriteTarget term symm cfg)
      (throwTacticEx `rewrite · "Did not find an occurrence of the pattern in the current goal")

end Lean.Elab.Tactic
