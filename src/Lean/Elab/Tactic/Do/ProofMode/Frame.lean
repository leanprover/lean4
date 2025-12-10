/-
Copyright (c) 2025 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Tactic.Do.Syntax
public import Lean.Elab.Tactic.Do.ProofMode.Focus

public section

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
      else if let some (_, _, L, R) := parseAnd? P then
        collectHyps L (collectHyps R acc)
      else
        acc

    label (Ps : List Hyp) (P' : Expr) : MetaM (List Hyp × Expr) := do
      let P' ← instantiateMVarsIfMVarApp P'
      if let some _ := parseEmptyHyp? P' then
        return (Ps, P')
      if let some (u, σs, L, R) := parseAnd? P' then
        let (Ps, L') ← label Ps L
        let (Ps, R') ← label Ps R
        return (Ps, SPred.mkAnd! u σs L' R')
      else
        let mut Ps' := Ps
        repeat
          -- If we cannot find the hyp, it might be in a nested conjunction.
          -- Just pick a default name for it.
          let name ← mkFreshUserName `h
          let uniq ← mkFreshId
          let P :: Ps'' := Ps' | return (Ps, { name, uniq, p := P' : Hyp }.toExpr)
          Ps' := Ps''
          if ← isDefEq P.p P' then
            return (Ps, { P with p := P' }.toExpr)
        unreachable!

def mFrameCore [Monad m] [MonadControlT MetaM m] [MonadLiftT MetaM m]
  (goal : MGoal) (kFail : m Expr) (kSuccess : Expr /-φ:Prop-/ → Expr /-h:φ-/ → MGoal → m Expr) : m Expr := do
  let P := goal.hyps
  let φ ← mkFreshExprMVar (mkSort .zero) .synthetic
  let P' ← mkFreshExprMVar (mkApp (mkConst ``SPred [goal.u]) goal.σs) .synthetic
  let synthGoal := mkApp4 (mkConst ``HasFrame [goal.u]) goal.σs P P' φ
  let inst ←
    match ← trySynthInstance synthGoal with
    | .some inst => pure inst
    | .undef     =>
      -- We give the `instHasFramePureTrueDown` instance extra support here so that it applies even
      -- when the type class synthesis problem is stuck. This ensures we are able to frame
      -- `?inv1 a b c : SPred []` before the user has instantiated `?inv1`.
      if ← isDefEqGuarded (TypeList.mkNil goal.u) goal.σs then
        liftMetaM <| φ.mvarId!.assign (mkApp2 (mkConst ``ULift.down [goal.u, 0]) (mkSort .zero) P)
        liftMetaM <| P'.mvarId!.assign (mkApp2 (mkConst ``SPred.pure [goal.u]) goal.σs (mkConst ``True))
        pure <| mkApp (mkConst ``instHasFramePureTrueDown [goal.u]) P
      else return ← kFail
    | _          => return ← kFail
  if ← withDefault <| isDefEqGuarded (mkConst ``True) φ then return (← kFail)
  -- copy the name of P to P' if it is a named hypothesis
  let P' ← transferHypNames P P'
  let goal := { goal with hyps := P' }
  withLocalDeclD (← liftMetaM <| mkFreshUserName `h) φ fun hφ => do
    let prf ← kSuccess φ hφ goal
    let prf ← mkLambdaFVars #[hφ] prf
    let prf := mkApp7 (mkConst ``Frame.frame [goal.u]) goal.σs P P' goal.target φ inst prf
    return prf

def mTryFrame [Monad m] [MonadControlT MetaM m] [MonadLiftT MetaM m]
  (goal : MGoal) (k : MGoal → m Expr) : m Expr :=
  mFrameCore goal (k goal) (fun _ _ goal => k goal)

@[builtin_tactic Lean.Parser.Tactic.mframe]
def elabMFrame : Tactic | _ => do
  let mvar ← getMainGoal
  mvar.withContext do
  let g ← instantiateMVars <| ← mvar.getType
  let some goal := parseMGoal? g | throwError "not in proof mode"
  let prf ← mFrameCore goal (fun _ => throwError "Could not infer frame") fun _ _ goal => do
    let m ← mkFreshExprSyntheticOpaqueMVar goal.toExpr
    replaceMainGoal [m.mvarId!]
    return m
  mvar.assign prf
