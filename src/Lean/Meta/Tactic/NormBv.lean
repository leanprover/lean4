/-
Copyright (c) 2024 Alex Keizer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Keizer
-/
-- prelude
-- TODO: minimize imports
import Lean.Meta.Tactic.Util
import Lean.Elab.Tactic
import Lean.Elab.Tactic.Basic
import Lean.Meta.Tactic.Apply
import Init.Data.BitVec

namespace Lean.Meta

open Lean.Elab.Tactic
open Std BitVec

@[elab_as_elim]
theorem BitVec.concatCases
    {motive : {w : Nat} → BitVec w → Sort u}
    (nil    : motive BitVec.nil)
    (concat : ∀ {w : Nat} (x : BitVec w) (b : Bool), motive (concat x b) ) :
    ∀ {w} (x : BitVec w), motive x :=
  sorry

-- TODO: this is copied from `evalCases`, surely there's a better way to do this
-- It's just doing the equivalent of `cases $target using BitVec.concatCases`
def casesBitVec (target : Expr) : TacticM Unit := do
  let elimInfo ← withMainContext <| getElimInfo ``BitVec.concatCases
  let mvarId ← getMainGoal
  -- save initial info before main goal is reassigned
  let initInfo ← mkTacticInfo (← getMCtx) (← getUnsolvedGoals) (← getRef)
  let tag ← mvarId.getTag
  mvarId.withContext do
    let targets ← addImplicitTargets elimInfo #[target]
    let result ← ElimApp.mkElimApp elimInfo targets tag
    let elimArgs := result.elimApp.getAppArgs
    let targets ← elimInfo.targetsPos.mapM fun i => instantiateMVars elimArgs[i]!
    let motiveType ← inferType elimArgs[elimInfo.motivePos]!
    let mvarId ← generalizeTargetsEq mvarId motiveType targets
    let (targetsNew, mvarId) ← mvarId.introN targets.size
    mvarId.withContext do
      ElimApp.setMotiveArg mvarId elimArgs[elimInfo.motivePos]!.mvarId! targetsNew
      mvarId.assign result.elimApp
      ElimApp.evalAlts elimInfo result.alts .missing #[] initInfo
          (numEqs := targets.size) (toClear := targetsNew)

syntax (name := blast_bv) "blast_bv" : tactic

@[tactic blast_bv]
partial def blastBv : Tactic := fun _ => loop where
  loop : TacticM Unit := withMainContext <| do
    let ctx ← getLCtx
    let n ← mkFreshExprMVar (Expr.const ``Nat [])
    let decl ← ctx.findDeclM? (fun decl => do
      let isSucc ← isDefEq decl.type (.app (.const ``BitVec []) (.app (.const ``Nat.succ []) n))
      let isZero ← isDefEq decl.type (.app (.const ``BitVec []) (.const ``Nat.zero []) )
      if isZero || isSucc then
        pure <| some decl
      else
        pure none
    )
    match decl with
    | none => return ()
    | some decl =>
        casesBitVec (decl.toExpr)
        loop
        return

syntax "blast_bv " "with" ident+ : tactic
macro_rules
  | `(tactic| blast_bv with $xs:ident*) =>
      let xs := xs.reverse
      `(tactic| blast_bv; rename_i $[$xs:ident]*)

example (x : BitVec 2) (y : BitVec 2) : x + y = y + x := by
  blast_bv with a a' b b';
  /-
  b'ba'a: Bool
⊢ concat (concat nil a') b' + concat (concat nil a) b = concat (concat nil a) b + concat (concat nil a') b'
  -/
  sorry
