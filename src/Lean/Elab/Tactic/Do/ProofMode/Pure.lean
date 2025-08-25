/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Sebastian Graf
-/
module

prelude
public import Std.Tactic.Do.Syntax
public import Lean.Elab.Tactic.Do.ProofMode.MGoal
public import Lean.Elab.Tactic.Do.ProofMode.Focus
public import Lean.Elab.Tactic.Meta

public section

namespace Lean.Elab.Tactic.Do.ProofMode
open Std.Do SPred.Tactic
open Lean Elab Tactic Meta

-- NB: We do not use MVarId.intro because that would mean we require all callers to supply an MVarId.
-- This function only knows about the hypothesis H=⌜φ⌝ to destruct.
-- It will provide a proof for Q ∧ H ⊢ₛ T
-- if `k` produces a proof for Q ⊢ₛ T that may range over a pure proof h : φ.
-- It calls `k` with the φ in H = ⌜φ⌝ and a proof `h : φ` thereof.
def mPureCore (σs : Expr) (hyp : Expr) (name : TSyntax ``binderIdent)
  (k : Expr /-φ:Prop-/ → Expr /-h:φ-/ → MetaM (α × MGoal × Expr)) : MetaM (α × MGoal × Expr) := do
  let u ← mkFreshLevelMVar
  let φ ← mkFreshExprMVar (mkSort .zero)
  let inst ← synthInstance (mkApp3 (mkConst ``IsPure [u]) σs hyp φ)
  let (name, ref) ← getFreshHypName name
  withLocalDeclD name φ fun h => do
    addLocalVarInfo ref (← getLCtx) h φ
    let (a, goal, prf /- : goal.toExpr -/) ← k φ h
    let prf ← mkLambdaFVars #[h] prf
    let prf := mkApp7 (mkConst ``Pure.thm [u]) σs goal.hyps hyp goal.target φ inst prf
    let goal := { goal with hyps := SPred.mkAnd! u σs goal.hyps hyp }
    return (a, goal, prf)

@[builtin_tactic Lean.Parser.Tactic.mpure]
def elabMPure : Tactic
  | `(tactic| mpure $hyp) => do
    let mvar ← getMainGoal
    mvar.withContext do
    let g ← instantiateMVars <| ← mvar.getType
    let some goal := parseMGoal? g | throwError "not in proof mode"
    let res ← goal.focusHypWithInfo hyp
    let (m, _new_goal, prf) ← mPureCore goal.σs res.focusHyp (← `(binderIdent| $hyp:ident)) fun _ _ => do
      let goal := res.restGoal goal
      let m ← mkFreshExprSyntheticOpaqueMVar goal.toExpr
      return (m, goal, m)
    let prf := res.rewriteHyps goal prf
    mvar.assign prf
    replaceMainGoal [m.mvarId!]
  | _ => throwUnsupportedSyntax

def MGoal.triviallyPure (goal : MGoal) : OptionT MetaM Expr := do
  let mv ← mkFreshExprMVar goal.toExpr
  let ([], _) ← try runTactic mv.mvarId! (← `(tactic| apply $(mkIdent ``Std.Do.SPred.Tactic.Pure.intro); trivial)) catch _ => failure
    | failure
  return mv
