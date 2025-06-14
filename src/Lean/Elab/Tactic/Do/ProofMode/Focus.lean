/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Sebastian Graf
-/
prelude
import Lean.Elab.Tactic.Do.ProofMode.MGoal
import Lean.Meta

namespace Lean.Elab.Tactic.Do.ProofMode
open Std.Do ProofMode
open Lean Elab.Tactic Meta

/-- The result of focussing the context of a goal `goal : MGoal` on a particular hypothesis.
The focussed hypothesis is returned as `focusHyp : Expr`, along with the
residual `restHyps : Expr` and a `proof : Expr` for the property
`goal.hyps ⊣⊢ₛ restHyps ∧ focusHyp`. -/
structure FocusResult where
  focusHyp : Expr
  restHyps : Expr
  proof : Expr
  deriving Inhabited

theorem focus_this {σs : List Type} {P : SPred σs} : P ⊣⊢ₛ ⌜True⌝ ∧ P :=
  SPred.true_and.symm

theorem focus_l {σs : List Type} {P P' Q C R : SPred σs} (h₁ : P ⊣⊢ₛ P' ∧ R) (h₂ : P' ∧ Q ⊣⊢ₛ C) :
    P ∧ Q ⊣⊢ₛ C ∧ R :=
  (SPred.and_congr_l h₁).trans (SPred.and_right_comm.trans (SPred.and_congr_l h₂))

theorem focus_r {σs : List Type} {P Q Q' C R : SPred σs} (h₁ : Q ⊣⊢ₛ Q' ∧ R) (h₂ : P ∧ Q' ⊣⊢ₛ C) :
    P ∧ Q ⊣⊢ₛ C ∧ R :=
  (SPred.and_congr_r h₁).trans (SPred.and_assoc.symm.trans (SPred.and_congr_l h₂))

partial def focusHyp (σs : Expr) (e : Expr) (name : Name) : Option FocusResult := do
  if let some hyp := parseHyp? e then
    if hyp.name = name then
      return ⟨e, emptyHyp σs, mkApp2 (mkConst ``focus_this) σs e⟩
    else
      none
  else if let some (σs, lhs, rhs) := parseAnd? e then
    try
      -- NB: Need to prefer rhs over lhs, like the goal view (Lean.Elab.Tactic.Do.ProofMode.Display).
      let ⟨focus, rhs', h₁⟩ ← focusHyp σs rhs name
      let ⟨C, h₂⟩ := mkAnd σs lhs rhs'
      return ⟨focus, C, mkApp8 (mkConst ``focus_r) σs lhs rhs rhs' C focus h₁ h₂⟩
    catch _ =>
      let ⟨focus, lhs', h₁⟩ ← focusHyp σs lhs name
      let ⟨C, h₂⟩ := mkAnd σs lhs' rhs
      return ⟨focus, C, mkApp8 (mkConst ``focus_l) σs lhs lhs' rhs C focus h₁ h₂⟩
  else if let some _ := parseEmptyHyp? e then
    none
  else
    panic! s!"focusHyp: hypothesis without proper metadata: {e}"

def MGoal.focusHyp (goal : MGoal) (name : Name) : Option FocusResult :=
  Lean.Elab.Tactic.Do.ProofMode.focusHyp goal.σs goal.hyps name

def FocusResult.refl (σs : Expr) (restHyps : Expr) (focusHyp : Expr) : FocusResult :=
  let proof := mkApp2 (mkConst ``SPred.bientails.refl) σs (mkAnd! σs restHyps focusHyp)
  { restHyps, focusHyp, proof }

def FocusResult.restGoal (res : FocusResult) (goal : MGoal) : MGoal :=
  { goal with hyps := res.restHyps }

def FocusResult.recombineGoal (res : FocusResult) (goal : MGoal) : MGoal :=
  { goal with hyps := mkAnd! goal.σs res.restHyps res.focusHyp }

theorem FocusResult.rewrite_hyps {σs} {P Q R : SPred σs} (hrw : P ⊣⊢ₛ Q) (hgoal : Q ⊢ₛ R) : P ⊢ₛ R :=
  hrw.mp.trans hgoal

/-- Turn a proof for `(res.recombineGoal goal).toExpr` into one for `goal.toExpr`. -/
def FocusResult.rewriteHyps (res : FocusResult) (goal : MGoal) : Expr → Expr :=
  mkApp6 (mkConst ``rewrite_hyps) goal.σs goal.hyps (mkAnd! goal.σs res.restHyps res.focusHyp) goal.target res.proof

def MGoal.focusHypWithInfo (goal : MGoal) (name : Ident) : MetaM FocusResult := do
  let some res := goal.focusHyp name.getId | throwError "unknown hypothesis '{name}'"
  let some hyp := parseHyp? res.focusHyp | throwError "impossible; res.focusHyp not a hypothesis"
  addHypInfo name goal.σs hyp
  pure res
