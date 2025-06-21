/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Sebastian Graf
-/
prelude
import Std.Tactic.Do.Syntax
import Lean.Elab.Tactic.Do.ProofMode.MGoal
import Lean.Elab.Tactic.Do.ProofMode.Focus

namespace Lean.Elab.Tactic.Do.ProofMode
open Std.Do
open Lean Elab Tactic Meta

class IsPure {σs : List Type} (P : SPred σs) (φ : outParam Prop) where to_pure : P ⊣⊢ₛ ⌜φ⌝
instance (σs) : IsPure (σs:=σs) ⌜φ⌝ φ where to_pure := .rfl
instance (σs) : IsPure (σs:=σs) spred(⌜φ⌝ → ⌜ψ⌝) (φ → ψ) where to_pure := SPred.pure_imp
instance (σs) : IsPure (σs:=σs) spred(⌜φ⌝ ∧ ⌜ψ⌝) (φ ∧ ψ) where to_pure := SPred.pure_and
instance (σs) : IsPure (σs:=σs) spred(⌜φ⌝ ∨ ⌜ψ⌝) (φ ∨ ψ) where to_pure := SPred.pure_or
instance (σs) (P : α → Prop) : IsPure (σs:=σs) spred(∃ x, ⌜P x⌝) (∃ x, P x) where to_pure := SPred.pure_exists
instance (σs) (P : α → Prop) : IsPure (σs:=σs) spred(∀ x, ⌜P x⌝) (∀ x, P x) where to_pure := SPred.pure_forall
instance (σs) (P : SPred (σ::σs)) [inst : IsPure P φ] : IsPure (σs:=σs) spred(P s) φ where to_pure := (iff_of_eq SPred.bientails_cons).mp inst.to_pure s
instance (P : Prop) : IsPure (σs:=[]) P P where to_pure := Iff.rfl

theorem Pure.thm {σs : List Type} {P Q T : SPred σs} {φ : Prop} [IsPure Q φ]
  (h : φ → P ⊢ₛ T) : P ∧ Q ⊢ₛ T := by
    apply SPred.pure_elim
    · exact SPred.and_elim_r.trans IsPure.to_pure.mp
    · intro hp
      exact SPred.and_elim_l.trans (h hp)

-- NB: We do not use MVarId.intro because that would mean we require all callers to supply an MVarId.
-- This function only knows about the hypothesis H=⌜φ⌝ to destruct.
-- It will provide a proof for Q ∧ H ⊢ₛ T
-- if `k` produces a proof for Q ⊢ₛ T that may range over a pure proof h : φ.
-- It calls `k` with the φ in H = ⌜φ⌝ and a proof `h : φ` thereof.
def mPureCore (σs : Expr) (hyp : Expr) (name : TSyntax ``binderIdent)
  (k : Expr /-φ:Prop-/ → Expr /-h:φ-/ → MetaM (α × MGoal × Expr)) : MetaM (α × MGoal × Expr) := do
  let φ ← mkFreshExprMVar (mkSort .zero)
  let inst ← synthInstance (mkApp3 (mkConst ``IsPure) σs hyp φ)
  let (name, ref) ← getFreshHypName name
  withLocalDeclD name φ fun h => do
    addLocalVarInfo ref (← getLCtx) h φ
    let (a, goal, prf /- : goal.toExpr -/) ← k φ h
    let prf ← mkLambdaFVars #[h] prf
    let prf := mkApp7 (mkConst ``Pure.thm) σs goal.hyps hyp goal.target φ inst prf
    let goal := { goal with hyps := mkAnd! σs goal.hyps hyp }
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

/-- A generalization of `SPred.pure_intro` exploiting `IsPure`. -/
private theorem Pure.intro {σs : List Type} {P Q : SPred σs} {φ : Prop} [IsPure Q φ] (hp : φ) : P ⊢ₛ Q :=
  (SPred.pure_intro hp).trans IsPure.to_pure.mpr

macro "mpure_intro" : tactic => `(tactic| apply Pure.intro)
