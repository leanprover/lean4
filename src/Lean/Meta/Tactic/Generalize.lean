/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.KAbstract
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.Intro

namespace Lean.Meta

/-- The `generalize` tactic takes arguments of the form `h : e = x` -/
structure GeneralizeArg where
  expr   : Expr
  xName? : Option Name := none
  hName? : Option Name := none
  deriving Inhabited

partial def generalize (mvarId : MVarId) (args : Array GeneralizeArg) : MetaM (Array FVarId × MVarId) :=
  withMVarContext mvarId do
    checkNotAssigned mvarId `generalize
    let tag ← getMVarTag mvarId
    let target ← instantiateMVars (← getMVarType mvarId)
    let rec go (i : Nat) : MetaM Expr := do
      if i < args.size then
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
      assignExprMVar mvarId (mkAppN mvarNew es)
      introNP mvarNew.mvarId! args.size
    else
      let (rfls, targetNew) ← forallBoundedTelescope targetNew args.size fun xs type => do
        let rec go' (i : Nat) : MetaM (List Expr × Expr) := do
          if i < xs.size then
            let arg := args[i]
            if let some hName := arg.hName? then
              let xType ← inferType xs[i]
              let e ← instantiateMVars arg.expr
              let eType ← instantiateMVars (← inferType e)
              let (hType, r) ←
                if (← isDefEq xType eType) then
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
      assignExprMVar mvarId (mkAppN (mkAppN mvarNew es) rfls.toArray)
      introNP mvarNew.mvarId! (args.size + rfls.length)

end Lean.Meta
