/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Sebastian Graf
-/
module

prelude
public import Lean.Elab.Tactic.Do.ProofMode.MGoal

public section

namespace Lean.Elab.Tactic.Do.ProofMode
open Std.Do SPred.Tactic ProofMode
open Lean Elab.Tactic Meta

/-- The result of focusing the context of a goal `goal : MGoal` on a particular hypothesis.
The focused hypothesis is returned as `focusHyp : Expr`, along with the
residual `restHyps : Expr` and a `proof : Expr` for the property
`goal.hyps ⊣⊢ₛ restHyps ∧ focusHyp`. -/
structure FocusResult where
  focusHyp : Expr
  restHyps : Expr
  proof : Expr
  deriving Inhabited

partial def focusHyp (u : Level) (σs : Expr) (e : Expr) (name : Name) : Option FocusResult := do
  if let some hyp := parseHyp? e then
    if hyp.name = name then
      return ⟨e, emptyHyp u σs, mkApp2 (mkConst ``Focus.this [u]) σs e⟩
    else
      none
  else if let some (u, σs, lhs, rhs) := parseAnd? e then
    try
      -- NB: Need to prefer rhs over lhs, like the goal view (Lean.Elab.Tactic.Do.ProofMode.Delab).
      let ⟨focus, rhs', h₁⟩ ← focusHyp u σs rhs name
      let ⟨C, h₂⟩ := SPred.mkAnd u σs lhs rhs'
      return ⟨focus, C, mkApp8 (mkConst ``Focus.right [u]) σs lhs rhs rhs' C focus h₁ h₂⟩
    catch _ =>
      let ⟨focus, lhs', h₁⟩ ← focusHyp u σs lhs name
      let ⟨C, h₂⟩ := SPred.mkAnd u σs lhs' rhs
      return ⟨focus, C, mkApp8 (mkConst ``Focus.left [u]) σs lhs lhs' rhs C focus h₁ h₂⟩
  else if let some _ := parseEmptyHyp? e then
    none
  else
    panic! s!"focusHyp: hypothesis without proper metadata: {e}"

def MGoal.focusHyp (goal : MGoal) (name : Name) : Option FocusResult :=
  Lean.Elab.Tactic.Do.ProofMode.focusHyp goal.u goal.σs goal.hyps name

def FocusResult.refl (u : Level) (σs : Expr) (restHyps : Expr) (focusHyp : Expr) : FocusResult :=
  let proof := mkApp2 (mkConst ``SPred.bientails.refl [u]) σs (SPred.mkAnd! u σs restHyps focusHyp)
  { restHyps, focusHyp, proof }

def FocusResult.restGoal (res : FocusResult) (goal : MGoal) : MGoal :=
  { goal with hyps := res.restHyps }

def FocusResult.recombineGoal (res : FocusResult) (goal : MGoal) : MGoal :=
  { goal with hyps := SPred.mkAnd! goal.u goal.σs res.restHyps res.focusHyp }

/-- Turn a proof for `(res.recombineGoal goal).toExpr` into one for `goal.toExpr`. -/
def FocusResult.rewriteHyps (res : FocusResult) (goal : MGoal) : Expr → Expr :=
  mkApp6 (mkConst ``Focus.rewrite_hyps [goal.u]) goal.σs goal.hyps (SPred.mkAnd! goal.u goal.σs res.restHyps res.focusHyp) goal.target res.proof

def MGoal.focusHypWithInfo (goal : MGoal) (name : Ident) : MetaM FocusResult := do
  let some res := goal.focusHyp name.getId | throwError "unknown hypothesis `{name}`"
  let some hyp := parseHyp? res.focusHyp | throwError "impossible; res.focusHyp not a hypothesis"
  addHypInfo name goal.σs hyp
  pure res
