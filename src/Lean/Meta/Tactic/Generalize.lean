/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.KAbstract
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.Intro
import Lean.Meta.Tactic.FVarSubst
import Lean.Meta.Tactic.Revert

namespace Lean.Meta

/-- The `generalize` tactic takes arguments of the form `h : e = x` -/
structure GeneralizeArg where
  expr   : Expr
  xName? : Option Name := none
  hName? : Option Name := none
  deriving Inhabited

/--
Telescopic `generalize` tactic. It can simultaneously generalize many terms.
It uses `kabstract` to occurrences of the terms that need to be generalized.
-/
private partial def generalizeCore (mvarId : MVarId) (args : Array GeneralizeArg) : MetaM (Array FVarId × MVarId) :=
  mvarId.withContext do
    mvarId.checkNotAssigned `generalize
    let tag ← mvarId.getTag
    let target ← instantiateMVars (← mvarId.getType)
    let rec go (i : Nat) : MetaM Expr := do
      if _h : i < args.size then
        let arg := args[i]
        let e ← instantiateMVars arg.expr
        let eType ← instantiateMVars (← inferType e)
        let type ← go (i+1)
        let xName ← if let some xName := arg.xName? then pure xName else mkFreshUserName `x
        return Lean.mkForall xName BinderInfo.default eType (← kabstract type e)
      else
        return target
    let targetNew ← go 0
    unless (← isTypeCorrect targetNew) do
      throwTacticEx `generalize mvarId m!"result is not type correct{indentExpr targetNew}"
    let es := args.map (·.expr)
    if !args.any fun arg => arg.hName?.isSome then
      let mvarNew ← mkFreshExprSyntheticOpaqueMVar targetNew tag
      mvarId.assign (mkAppN mvarNew es)
      mvarNew.mvarId!.introNP args.size
    else
      let (rfls, targetNew) ← forallBoundedTelescope targetNew args.size fun xs type => do
        let rec go' (i : Nat) : MetaM (List Expr × Expr) := do
          if _h : i < xs.size then
            let arg := args[i]!
            if let some hName := arg.hName? then
              let xType ← inferType xs[i]
              let e ← instantiateMVars arg.expr
              let eType ← instantiateMVars (← inferType e)
              let (hType, r) ← if (← isDefEq xType eType) then
                pure (← mkEq e xs[i], ← mkEqRefl e)
              else
                pure (← mkHEq e xs[i], ← mkHEqRefl e)
              let (rs, type) ← go' (i+1)
              return (r :: rs, mkForall hName BinderInfo.default hType type)
            else
              go' (i+1)
          else
            return ([], type)
        let (rfls, type) ← go' 0
        return (rfls, ← mkForallFVars xs type)
      let mvarNew ← mkFreshExprSyntheticOpaqueMVar targetNew tag
      mvarId.assign (mkAppN (mkAppN mvarNew es) rfls.toArray)
      mvarNew.mvarId!.introNP (args.size + rfls.length)

@[inherit_doc generalizeCore]
def _root_.Lean.MVarId.generalize (mvarId : MVarId) (args : Array GeneralizeArg) : MetaM (Array FVarId × MVarId) :=
  generalizeCore mvarId args

@[inherit_doc generalizeCore, deprecated MVarId.generalize]
def generalize (mvarId : MVarId) (args : Array GeneralizeArg) : MetaM (Array FVarId × MVarId) :=
  generalizeCore mvarId args

/--
Extension of `generalize` to support generalizing within specified hypotheses.
The `hyps` array contains the list of hypotheses within which to look for occurrences
of the generalizing expressions.
-/
def _root_.Lean.MVarId.generalizeHyp (mvarId : MVarId) (args : Array GeneralizeArg) (hyps : Array FVarId := #[])
    (fvarSubst : FVarSubst := {}) : MetaM (FVarSubst × Array FVarId × MVarId) := do
  if hyps.isEmpty then
    -- trivial case
    return (fvarSubst, ← mvarId.generalize args)
  let args ← args.mapM fun arg => return { arg with expr := ← instantiateMVars arg.expr }
  let hyps ← hyps.filterM fun h => do
    let type ← instantiateMVars (← h.getType)
    args.anyM fun arg => return (← kabstract type arg.expr).hasLooseBVars
  let (reverted, mvarId) ← mvarId.revert hyps true
  let (newVars, mvarId) ← mvarId.generalize args
  let (reintros, mvarId) ← mvarId.introNP reverted.size
  let fvarSubst := Id.run do
    let mut subst : FVarSubst := fvarSubst
    for h in reverted, reintro in reintros do
      subst := subst.insert h (mkFVar reintro)
    pure subst
  return (fvarSubst, newVars, mvarId)

end Lean.Meta
