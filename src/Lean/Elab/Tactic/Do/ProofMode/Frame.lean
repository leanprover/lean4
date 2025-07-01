/-
Copyright (c) 2025 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
prelude
import Std.Tactic.Do.Syntax
import Lean.Elab.Tactic.Do.ProofMode.MGoal
import Lean.Elab.Tactic.Do.ProofMode.Focus

namespace Lean.Elab.Tactic.Do.ProofMode
open Std.Do SPred.Tactic
open Lean Elab Tactic Meta

-- #synth ∀ {w x P Q y z}, HasFrame spred(⌜w = 2⌝ ∧ ⌜x = 3⌝ ∧ P ∧ ⌜y = 4⌝ ∧ Q ∧ ⌜z=6⌝) _ _

/-- If `P'` is a conjunction of unnamed hypotheses that are a subset of the named hypotheses of `P`,
transfer the names of the hypotheses of `P` to the hypotheses of `P'`. -/
partial def transferHypNames (P P' : Expr) : MetaM Expr := (·.snd) <$> label (collectHyps P) P'
  where
    collectHyps (P : Expr) (acc : List Hyp := []) : List Hyp :=
      if let some hyp := parseHyp? P then
        hyp :: acc
      else if let some (_, L, R) := parseAnd? P then
        collectHyps L (collectHyps R acc)
      else
        acc

    label (Ps : List Hyp) (P' : Expr) : MetaM (List Hyp × Expr) := do
      let P' ← instantiateMVarsIfMVarApp P'
      if let some _ := parseEmptyHyp? P' then
        return (Ps, P')
      if let some (σs, L, R) := parseAnd? P' then
        let (Ps, L') ← label Ps L
        let (Ps, R') ← label Ps R
        return (Ps, mkAnd! σs L' R')
      else
        let mut Ps' := Ps
        repeat
          -- If we cannot find the hyp, it might be in a nested conjunction.
          -- Just pick a default name for it.
          let uniq ← mkFreshId
          let P :: Ps'' := Ps' | return (Ps, { name := `h, uniq, p := P' : Hyp }.toExpr)
          Ps' := Ps''
          if ← isDefEq P.p P' then
            return (Ps, { P with p := P' }.toExpr)
        unreachable!

def mFrameCore [Monad m] [MonadControlT MetaM m] [MonadLiftT MetaM m]
  (goal : MGoal) (kFail : m (α × Expr)) (kSuccess : Expr /-φ:Prop-/ → Expr /-h:φ-/ → MGoal → m (α × Expr)) : m (α × Expr) := do
  let P := goal.hyps
  let φ ← mkFreshExprMVar (mkSort .zero)
  let P' ← mkFreshExprMVar (mkApp (mkConst ``SPred) goal.σs)
  if let some inst ← synthInstance? (mkApp4 (mkConst ``HasFrame) goal.σs P P' φ) then
    if ← isDefEq (mkConst ``True) φ then return (← kFail)
    -- copy the name of P to P' if it is a named hypothesis
    let P' ← transferHypNames P P'
    let goal := { goal with hyps := P' }
    withLocalDeclD `h φ fun hφ => do
      let (a, prf) ← kSuccess φ hφ goal
      let prf ← mkLambdaFVars #[hφ] prf
      let prf := mkApp7 (mkConst ``Frame.frame) goal.σs P P' goal.target φ inst prf
      return (a, prf)
  else
    kFail

def mTryFrame [Monad m] [MonadControlT MetaM m] [MonadLiftT MetaM m]
  (goal : MGoal) (k : MGoal → m (α × Expr)) : m (α × Expr) :=
  mFrameCore goal (k goal) (fun _ _ goal => k goal)

@[builtin_tactic Lean.Parser.Tactic.mframe]
def elabMFrame : Tactic | _ => do
  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some goal := parseMGoal? g | throwError "not in proof mode"
  let (m, prf) ← mFrameCore goal (fun _ => throwError "Could not infer frame") fun _ _ goal => do
    let m ← mkFreshExprSyntheticOpaqueMVar goal.toExpr
    return (m, m)
  mvar.assign prf
  replaceMainGoal [m.mvarId!]
