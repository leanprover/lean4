/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Subst
import Lean.Meta.Tactic.Clear
import Lean.Meta.Match.Value

namespace Lean.Meta

structure CaseValueSubgoal where
  mvarId : MVarId
  newH   : FVarId
  subst  : FVarSubst := {}
  deriving Inhabited

/--
  Split goal `... |- C x` into two subgoals
  `..., (h : x = value)  |- C value`
  `..., (h : x != value) |- C x`
  where `fvarId` is `x`s id.
  The type of `x` must have decidable equality.

  Remark: `subst` field of the second subgoal is equal to the input `subst`. -/
private def caseValueAux (mvarId : MVarId) (fvarId : FVarId) (value : Expr) (hName : Name := `h) (subst : FVarSubst := {})
    : MetaM (CaseValueSubgoal × CaseValueSubgoal) :=
  mvarId.withContext do
    let tag ← mvarId.getTag
    mvarId.checkNotAssigned `caseValue
    let target ← mvarId.getType
    let xEqValue ← mkEq (mkFVar fvarId) (foldPatValue value)
    let xNeqValue := mkApp (mkConst `Not) xEqValue
    let thenTarget := Lean.mkForall hName BinderInfo.default xEqValue  target
    let elseTarget := Lean.mkForall hName BinderInfo.default xNeqValue target
    let thenMVar ← mkFreshExprSyntheticOpaqueMVar thenTarget tag
    let elseMVar ← mkFreshExprSyntheticOpaqueMVar elseTarget tag
    let val ← mkAppOptM `dite #[none, xEqValue, none, thenMVar, elseMVar]
    mvarId.assign val
    let (elseH, elseMVarId) ← elseMVar.mvarId!.intro1P
    let elseSubgoal := { mvarId := elseMVarId, newH := elseH, subst := subst : CaseValueSubgoal }
    let (thenH, thenMVarId) ← thenMVar.mvarId!.intro1P
    let symm   := false
    let clearH := false
    let (thenSubst, thenMVarId) ← substCore thenMVarId thenH symm subst clearH
    thenMVarId.withContext do
      trace[Meta] "subst domain: {thenSubst.domain.map (·.name)}"
      let thenH := (thenSubst.get thenH).fvarId!
      trace[Meta] "searching for decl"
      let _ ← thenH.getDecl
      trace[Meta] "found decl"
    let thenSubgoal := { mvarId := thenMVarId, newH := (thenSubst.get thenH).fvarId!, subst := thenSubst : CaseValueSubgoal }
    pure (thenSubgoal, elseSubgoal)

def caseValue (mvarId : MVarId) (fvarId : FVarId) (value : Expr) : MetaM (CaseValueSubgoal × CaseValueSubgoal) := do
  let s ← caseValueAux mvarId fvarId value
  appendTagSuffix s.1.mvarId `thenBranch
  appendTagSuffix s.2.mvarId `elseBranch
  pure s

structure CaseValuesSubgoal where
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
def caseValues (mvarId : MVarId) (fvarId : FVarId) (values : Array Expr) (hNamePrefix := `h) (substNewEqs := false) : MetaM (Array CaseValuesSubgoal) :=
  let rec loop : Nat → MVarId → List Expr → Array FVarId → Array CaseValuesSubgoal → MetaM (Array CaseValuesSubgoal)
    | _, mvarId, [],    _,  _        => throwTacticEx `caseValues mvarId "list of values must not be empty"
    | i, mvarId, v::vs, hs, subgoals => do
      let (thenSubgoal, elseSubgoal) ← caseValueAux mvarId fvarId v (hNamePrefix.appendIndexAfter i) {}
      appendTagSuffix thenSubgoal.mvarId ((`case).appendIndexAfter i)
      let thenMVarId ← hs.foldlM
        (fun thenMVarId h => match thenSubgoal.subst.get h with
          | Expr.fvar fvarId => thenMVarId.tryClear fvarId
          | _                => pure thenMVarId)
        thenSubgoal.mvarId
      let subgoals ← if substNewEqs then
         let (subst, mvarId) ← substCore thenMVarId thenSubgoal.newH false thenSubgoal.subst true
         pure <| subgoals.push { mvarId := mvarId, newHs := #[], subst := subst }
      else
         pure <| subgoals.push { mvarId := thenMVarId, newHs := #[thenSubgoal.newH], subst := thenSubgoal.subst }
      match vs with
      | [] => do
        appendTagSuffix elseSubgoal.mvarId ((`case).appendIndexAfter (i+1))
        pure $ subgoals.push { mvarId := elseSubgoal.mvarId, newHs := hs.push elseSubgoal.newH, subst := {} }
      | vs => loop (i+1) elseSubgoal.mvarId vs (hs.push elseSubgoal.newH) subgoals
  loop 1 mvarId values.toList #[] #[]

end Lean.Meta
