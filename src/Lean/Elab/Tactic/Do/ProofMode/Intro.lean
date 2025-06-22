/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Sebastian Graf
-/
prelude
import Std.Tactic.Do.Syntax
import Lean.Elab.Tactic.Do.ProofMode.Basic
import Lean.Elab.Tactic.Do.ProofMode.Display

namespace Lean.Elab.Tactic.Do.ProofMode
open Std.Do
open Lean Elab Tactic Meta

theorem Intro.intro {σs : List Type} {P Q H T : SPred σs} (hand : Q ∧ H ⊣⊢ₛ P) (h : P ⊢ₛ T) : Q ⊢ₛ H → T :=
  SPred.imp_intro (hand.mp.trans h)

partial def mIntro [Monad m] [MonadControlT MetaM m] (goal : MGoal) (ident : TSyntax ``binderIdent) (k : MGoal → m (α × Expr)) : m (α × Expr) :=
  controlAt MetaM fun map => do
  let some (σs, H, T) := goal.target.app3? ``SPred.imp | throwError "Target not an implication {goal.target}"
  let (name, ref) ← getFreshHypName ident
  let uniq ← mkFreshId
  let hyp := Hyp.mk name uniq H
  addHypInfo ref σs hyp (isBinder := true)
  let Q := goal.hyps
  let H := hyp.toExpr
  let (P, hand) := mkAnd goal.σs goal.hyps H
  map do
    let (a, prf) ← k { goal with hyps := P, target := T }
    let prf := mkApp7 (mkConst ``Intro.intro) σs P Q H T hand prf
    return (a, prf)

-- This is regular MVar.intro, but it takes care not to leave the proof mode by preserving metadata
partial def mIntroForall [Monad m] [MonadControlT MetaM m] [MonadLiftT MetaM m] (goal : MGoal) (ident : TSyntax ``binderIdent) (k : MGoal → m (α × Expr)) : m (α × Expr) :=
  controlAt MetaM fun map => do
  let some (_type, σ, σs') := (← whnf goal.σs).app3? ``List.cons | liftMetaM <| throwError "Ambient state list not a cons {goal.σs}"
  let name ← match ident with
  | `(binderIdent| $name:ident) => pure name.getId
  | `(binderIdent| $_) => liftMetaM <| mkFreshUserName `s
  withLocalDeclD name σ fun s => do
    addLocalVarInfo ident (← getLCtx) s σ (isBinder := true)
    let H := betaRevPreservingHypNames σs' goal.hyps #[s]
    let T := goal.target.betaRev #[s]
    map do
      let (a, prf) ← k { σs:=σs', hyps:=H, target:=T }
      let prf ← mkLambdaFVars #[s] prf
      return (a, mkApp5 (mkConst ``SPred.entails_cons_intro) σ σs' goal.hyps goal.target prf)

def mIntroForallN [Monad m] [MonadControlT MetaM m] [MonadLiftT MetaM m] (goal : MGoal) (n : Nat) (k : MGoal → m (α × Expr)) : m (α × Expr) :=
  match n with
  | 0 => k goal
  | n+1 => do mIntroForall goal (← liftM (m := MetaM) `(binderIdent| _)) fun g =>
              mIntroForallN g n k

macro_rules
  | `(tactic| mintro $pat₁ $pat₂ $pats:mintroPat*) => `(tactic| mintro $pat₁; mintro $pat₂ $pats*)
  | `(tactic| mintro $pat:mintroPat) => do
    match pat with
    | `(mintroPat| $_:binderIdent) => Macro.throwUnsupported -- handled by an elaborator below
    | `(mintroPat| ∀$_:binderIdent) => Macro.throwUnsupported -- handled by an elaborator below
    | `(mintroPat| $pat:mcasesPat) => `(tactic| mintro h; mcases h with $pat)
    | _ => Macro.throwUnsupported -- presently unreachable

@[builtin_tactic Lean.Parser.Tactic.mintro]
def elabMIntro : Tactic
  | `(tactic| mintro $ident:binderIdent) => do

  let (mvar, goal) ← mStartMVar (← getMainGoal)
  mvar.withContext do

  let goals ← IO.mkRef []
  mvar.assign (← Prod.snd <$> mIntro goal ident fun newGoal => do
    let m ← mkFreshExprSyntheticOpaqueMVar newGoal.toExpr
    goals.modify (m.mvarId! :: ·)
    return ((), m))
  replaceMainGoal (← goals.get)

  | `(tactic| mintro ∀$ident:binderIdent) => do

  let (mvar, goal) ← mStartMVar (← getMainGoal)
  mvar.withContext do

  let goals ← IO.mkRef []
  mvar.assign (← Prod.snd <$> mIntroForall goal ident fun newGoal => do
    let m ← mkFreshExprSyntheticOpaqueMVar newGoal.toExpr
    goals.modify (m.mvarId! :: ·)
    return ((), m))
  replaceMainGoal (← goals.get)

  | _ => throwUnsupportedSyntax
