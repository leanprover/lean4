/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Basic
public import Lean.Meta.Tactic.FVarSubst
import Lean.Meta.Tactic.Subst

namespace Lean.Meta

/--
  Split goal `... |- C x`,, where `fvarId` is `x`s id, into two subgoals
  `..., |- (h : x = value)  → C x`
  `..., |- (h : x != value) → C x`
  The type of `x` must have decidable equality.
 -/
def caseValue (mvarId : MVarId) (fvarId : FVarId) (value : Expr) (hName : Name := `h)
    : MetaM (MVarId × MVarId) :=
  mvarId.withContext do
    let tag ← mvarId.getTag
    mvarId.checkNotAssigned `caseValue
    let target ← mvarId.getType
    let xEqValue ← mkEq (mkFVar fvarId) (← normLitValue value)
    let xNeqValue := mkApp (mkConst `Not) xEqValue
    let thenTarget := Lean.mkForall hName BinderInfo.default xEqValue  target
    let elseTarget := Lean.mkForall hName BinderInfo.default xNeqValue target
    let thenMVar ← mkFreshExprSyntheticOpaqueMVar thenTarget tag
    let elseMVar ← mkFreshExprSyntheticOpaqueMVar elseTarget tag
    let val ← mkAppOptM `dite #[none, xEqValue, none, thenMVar, elseMVar]
    mvarId.assign val
    return (thenMVar.mvarId!, elseMVar.mvarId!)

public structure CaseValuesSubgoal where
  mvarId : MVarId
  newHs  : Array FVarId := #[]
  subst  : FVarSubst := {}
  deriving Inhabited

/--
  Split goal `... |- C x`, where `fvarId` is `x`s id, into `values.size + 1` subgoals
  1)   `..., (h_1 : x = value[0])      |- C value[0]`
  ...
  n)   `..., (h_n : x = value[n - 1])  |- C value[n - 1]`
  n+1) `..., (h_1 : x != value[0]) ... (h_n : x != value[n-1]) |- C x`
  where `n = values.size`
  The type of `x` must have decidable equality.

  Remark: the last subgoal is for the "else" catchall case, and its `subst` is `{}`.
  Remark: the field `newHs` has size 1 forall but the last subgoal.

  If `needsHyps = false` then the else case comes without hypotheses.
-/
public def caseValues (mvarId : MVarId) (fvarId : FVarId) (values : Array Expr) (hNamePrefix := `h)
    (needHyps := true) : MetaM (Array CaseValuesSubgoal) :=
  let rec loop : Nat → MVarId → List Expr → Array FVarId → Array CaseValuesSubgoal → MetaM (Array CaseValuesSubgoal)
    | _, mvarId, [],    _,  _        => throwTacticEx `caseValues mvarId "list of values must not be empty"
    | i, mvarId, v::vs, hs, subgoals => do
      let (thenMVarId, elseMVarId) ← caseValue mvarId fvarId v (hNamePrefix.appendIndexAfter i)
      appendTagSuffix thenMVarId ((`case).appendIndexAfter i)
      let thenMVarId ← thenMVarId.tryClearMany hs
      let (subst, thenMVarId) ← introSubstEq thenMVarId (substLHS := true)
      let subgoals := subgoals.push { mvarId := thenMVarId, newHs := #[], subst }
      let (hs', elseMVarId) ←
        if needHyps then
          let (elseH, elseMVarId) ← elseMVarId.intro1P
          pure (hs.push elseH, elseMVarId)
        else
          let elseMVarId ← elseMVarId.intro1_
          pure (hs, elseMVarId)
      match vs with
      | [] => do
        appendTagSuffix elseMVarId ((`case).appendIndexAfter (i+1))
        pure $ subgoals.push { mvarId := elseMVarId, newHs := hs', subst := {} }
      | vs =>
        loop (i+1) elseMVarId vs hs' subgoals

  loop 1 mvarId values.toList #[] #[]

end Lean.Meta
