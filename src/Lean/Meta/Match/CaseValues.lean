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

structure CaseValueSubgoal where
  mvarId : MVarId
  newH   : FVarId
  deriving Inhabited

/--
  Split goal `... |- C x` into two subgoals
  `..., (h : x = value)  |- C x`
  `..., (h : x != value) |- C x`
  where `fvarId` is `x`s id.
  The type of `x` must have decidable equality.
 -/
def caseValue (mvarId : MVarId) (fvarId : FVarId) (value : Expr) (hName : Name := `h)
    : MetaM (CaseValueSubgoal × CaseValueSubgoal) :=
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
    let (elseH, elseMVarId) ← elseMVar.mvarId!.intro1P
    let elseSubgoal := { mvarId := elseMVarId, newH := elseH }
    let (thenH, thenMVarId) ← thenMVar.mvarId!.intro1P
    thenMVarId.withContext do
      trace[Meta] "searching for decl"
      let _ ← thenH.getDecl
      trace[Meta] "found decl"
    let thenSubgoal := { mvarId := thenMVarId, newH := thenH }
    pure (thenSubgoal, elseSubgoal)

public structure CaseValuesSubgoal where
  mvarId : MVarId
  newHs  : Array FVarId := #[]
  subst  : FVarSubst := {}
  deriving Inhabited

/--
  Split goal `... |- C x` into values.size + 1 subgoals
  1) `..., (h_1 : x = value[0])  |- C value[0]`
  ...
  n) `..., (h_n : x = value[n - 1])  |- C value[n - 1]`
  n+1) `..., (h_1 : x != value[0]) ... (h_n : x != value[n-1]) |- C x`
  where `n = values.size`
  where `fvarId` is `x`s id.
  The type of `x` must have decidable equality.

  Remark: the last subgoal is for the "else" catchall case, and its `subst` is `{}`.
  Remark: the field `newHs` has size 1 forall but the last subgoal.

  If `substNewEqs = true`, then the new `h_i` equality hypotheses are substituted in the first `n` cases.
-/
public def caseValues (mvarId : MVarId) (fvarId : FVarId) (values : Array Expr) (hNamePrefix := `h) : MetaM (Array CaseValuesSubgoal) :=
  let rec loop : Nat → MVarId → List Expr → Array FVarId → Array CaseValuesSubgoal → MetaM (Array CaseValuesSubgoal)
    | _, mvarId, [],    _,  _        => throwTacticEx `caseValues mvarId "list of values must not be empty"
    | i, mvarId, v::vs, hs, subgoals => do
      let (thenSubgoal, elseSubgoal) ← caseValue mvarId fvarId v (hNamePrefix.appendIndexAfter i)
      appendTagSuffix thenSubgoal.mvarId ((`case).appendIndexAfter i)
      let thenMVarId ← thenSubgoal.mvarId.tryClearMany  hs
      let (subst, mvarId) ← substCore thenMVarId thenSubgoal.newH (symm := false) {} (clearH := true)
      let subgoals := subgoals.push { mvarId := mvarId, newHs := #[], subst := subst }
      match vs with
      | [] => do
        appendTagSuffix elseSubgoal.mvarId ((`case).appendIndexAfter (i+1))
        pure $ subgoals.push { mvarId := elseSubgoal.mvarId, newHs := hs.push elseSubgoal.newH, subst := {} }
      | vs => loop (i+1) elseSubgoal.mvarId vs (hs.push elseSubgoal.newH) subgoals
  loop 1 mvarId values.toList #[] #[]

end Lean.Meta
