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
open Std.Do
open Lean Elab Tactic Meta

class SimpAnd {σs : List Type} (P Q : SPred σs) (PQ : outParam (SPred σs)) : Prop where
  simp_and : P ∧ Q ⊣⊢ₛ PQ

instance (σs) (P Q : SPred σs) : SimpAnd P Q (spred(P ∧ Q)) where simp_and := .rfl
instance (σs) (P : SPred σs) : SimpAnd P ⌜True⌝ P where simp_and := SPred.and_true
instance (σs) (P : SPred σs) : SimpAnd ⌜True⌝ P P where simp_and := SPred.true_and

class HasFrame {σs : List Type} (P : SPred σs) (P' : outParam (SPred σs)) (φ : outParam Prop) : Prop where
  reassoc : P ⊣⊢ₛ P' ∧ ⌜φ⌝
instance (σs) : HasFrame (σs:=σs) ⌜φ⌝ ⌜True⌝ φ where reassoc := SPred.true_and.symm
instance (σs) (P P' Q QP : SPred σs) [HasFrame P Q φ] [SimpAnd Q P' QP]: HasFrame (σs:=σs) spred(P ∧ P') QP φ where
  reassoc := ((SPred.and_congr_l HasFrame.reassoc).trans SPred.and_right_comm).trans (SPred.and_congr_l SimpAnd.simp_and)
instance (σs) (P P' Q' PQ : SPred σs) [HasFrame P' Q' φ] [SimpAnd P Q' PQ]: HasFrame (σs:=σs) spred(P ∧ P') PQ φ where
  reassoc := ((SPred.and_congr_r HasFrame.reassoc).trans SPred.and_assoc.symm).trans (SPred.and_congr_l SimpAnd.simp_and)
instance (σs) (P : SPred σs) : HasFrame (σs:=σs) spred(⌜φ⌝ ∧ P) P φ where reassoc := SPred.and_comm
instance (σs) (P : SPred σs) : HasFrame (σs:=σs) spred(P ∧ ⌜φ⌝) P φ where reassoc := .rfl
instance (σs) (P P' Q Q' QQ : SPred σs) [HasFrame P Q φ] [HasFrame P' Q' ψ] [SimpAnd Q Q' QQ]: HasFrame (σs:=σs) spred(P ∧ P') QQ (φ ∧ ψ) where
  reassoc := (SPred.and_congr HasFrame.reassoc HasFrame.reassoc).trans
             <| SPred.and_assoc.trans
             <| (SPred.and_congr_r
                  <| SPred.and_assoc.symm.trans
                  <| (SPred.and_congr_l SPred.and_comm).trans
                  <| SPred.and_assoc.trans
                  <| SPred.and_congr_r SPred.pure_and).trans
             <| SPred.and_assoc.symm.trans
             <| SPred.and_congr_l SimpAnd.simp_and
instance (σs) (P Q : SPred σs) [HasFrame P Q ψ] : HasFrame (σs:=σs) spred(⌜φ⌝ ∧ P) Q (φ ∧ ψ) where
  reassoc := SPred.and_comm.trans
             <| (SPred.and_congr_l HasFrame.reassoc).trans
             <| SPred.and_right_comm.trans
             <| SPred.and_assoc.trans
             <| SPred.and_congr_r SPred.pure_and
instance (σs) (P Q : SPred σs) [HasFrame P Q ψ] : HasFrame (σs:=σs) spred(P ∧ ⌜φ⌝) Q (ψ ∧ φ) where
  reassoc := (SPred.and_congr_l HasFrame.reassoc).trans
             <| SPred.and_right_comm.trans
             <| SPred.and_assoc.trans
             <| SPred.and_congr_r (SPred.and_comm.trans SPred.pure_and)
-- The following instance comes last so that it gets the highest priority.
-- It's the most efficient and best solution if valid
instance {P : Prop} : HasFrame (σs:=[]) P ⌜True⌝ P where reassoc := SPred.true_and.symm

-- #synth ∀ {w x P Q y z}, HasFrame spred(⌜w = 2⌝ ∧ ⌜x = 3⌝ ∧ P ∧ ⌜y = 4⌝ ∧ Q ∧ ⌜z=6⌝) _ _

theorem Frame.frame {σs : List Type} {P Q T : SPred σs} {φ : Prop} [HasFrame P Q φ]
  (h : φ → Q ⊢ₛ T) : P ⊢ₛ T := by
    apply SPred.pure_elim
    · exact HasFrame.reassoc.mp.trans SPred.and_elim_r
    · intro hp
      exact HasFrame.reassoc.mp.trans (SPred.and_elim_l' (h hp))

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
