/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

module
prelude
public import Lean.Meta.Basic
import Lean.Meta.Tactic.Contradiction

namespace Lean.Meta.Match.SimpH

/--
  State for the equational theorem hypothesis simplifier.

  Recall that each equation contains additional hypotheses to ensure the associated case does not taken by previous cases.
  We have one hypothesis for each previous case.

  Each hypothesis is of the form `forall xs, eqs → False`

  We use tactics to minimize code duplication.
-/
structure State where
  mvarId : MVarId            -- Goal representing the hypothesis
  xs  : List FVarId          -- Pattern variables for a previous case
  eqs : List FVarId          -- Equations to be processed
  eqsNew : List FVarId := [] -- Simplified (already processed) equations

abbrev M := StateRefT State MetaM

/--
  Apply the given substitution to `fvarIds`.
  This is an auxiliary method for `substRHS`.
-/
def applySubst (s : FVarSubst) (fvarIds : List FVarId) : List FVarId :=
  fvarIds.filterMap fun fvarId => match s.apply (mkFVar fvarId) with
    | Expr.fvar fvarId .. => some fvarId
    | _ => none

/--
  Given an equation of the form `lhs = rhs` where `rhs` is variable in `xs`,
  replace it everywhere with `lhs`.
-/
def substRHS (eq : FVarId) (rhs : FVarId) : M Unit := do
  assert! (← get).xs.contains rhs
  let (subst, mvarId) ← substCore (← get).mvarId eq (symm := true)
  modify fun s => { s with
    mvarId,
    xs  := applySubst subst (s.xs.erase rhs)
    eqs := applySubst subst s.eqs
    eqsNew := applySubst subst s.eqsNew
  }

def isDone : M Bool :=
  return (← get).eqs.isEmpty

/-- Customized `contradiction` tactic for `simpH?` -/
def contradiction (mvarId : MVarId) : MetaM Bool :=
   mvarId.contradictionCore { genDiseq := false, emptyType := false }

/--
  Auxiliary tactic that tries to replace as many variables as possible and then apply `contradiction`.
  We use it to discard redundant hypotheses.
-/
partial def trySubstVarsAndContradiction (mvarId : MVarId) (forbidden : FVarIdSet := {}) : MetaM Bool :=
  commitWhen do
    let mvarId ← substVars mvarId
    match (← injections mvarId (forbidden := forbidden)) with
    | .solved => return true -- closed goal
    | .subgoal mvarId' _ forbidden =>
      if mvarId' == mvarId then
        contradiction mvarId
      else
        trySubstVarsAndContradiction mvarId' forbidden

def processNextEq : M Bool := do
  let s ← get
  s.mvarId.withContext do
    if let eq :: eqs := s.eqs then
      modify fun s => { s with eqs }
      let eqType ← inferType (mkFVar eq)
      -- See `substRHS`. Recall that if `rhs` is a variable then if must be in `s.xs`
      if let some (_, lhs, rhs) ← matchEq? eqType then
        -- Common case: Different constructors
        match (← isConstructorApp? lhs), (← isConstructorApp? rhs) with
        | some lhsCtor, some rhsCtor =>
          if lhsCtor.name != rhsCtor.name then
            return false -- If the constructors are different, we can discard the hypothesis even if it a heterogeneous equality
        | _,_ => pure ()
        if (← isDefEq lhs rhs) then
          return true
        if rhs.isFVar && s.xs.contains rhs.fvarId! then
          substRHS eq rhs.fvarId!
          return true
      if let some (α, lhs, β, rhs) ← matchHEq? eqType then
        -- Try to convert `HEq` into `Eq`
        if (← isDefEq α β) then
          let (eqNew, mvarId) ← heqToEq s.mvarId eq (tryToClear := true)
          modify fun s => { s with mvarId, eqs := eqNew :: s.eqs }
          return true
        -- If it is not possible, we try to show the hypothesis is redundant by substituting even variables that are not at `s.xs`, and then use contradiction.
        else
          match (← isConstructorApp? lhs), (← isConstructorApp? rhs) with
          | some lhsCtor, some rhsCtor =>
            if lhsCtor.name != rhsCtor.name then
              return false -- If the constructors are different, we can discard the hypothesis even if it a heterogeneous equality
            else if (← trySubstVarsAndContradiction s.mvarId) then
              return false
          | _, _ =>
            if (← trySubstVarsAndContradiction s.mvarId) then
              return false
      try
        -- Try to simplify equation using `injection` tactic.
        match (← injection s.mvarId eq) with
        | InjectionResult.solved => return false
        | InjectionResult.subgoal mvarId eqNews .. =>
          modify fun s => { s with mvarId, eqs := eqNews.toList ++ s.eqs }
      catch _ =>
        modify fun s => { s with eqsNew := eq :: s.eqsNew }
    return true

partial def go : M Bool := do
  if (← isDone) then
    return true
  else if (← processNextEq) then
    go
  else
    return false

end SimpH


/--
  Auxiliary method for simplifying equational theorem hypotheses.

  Recall that each equation contains additional hypotheses to ensure the associated case was not taken by previous cases.
  We have one hypothesis for each previous case.
-/
public partial def simpH? (h : Expr) (numEqs : Nat) : MetaM (Option Expr) := withDefault do
  let numVars ← forallTelescope h fun ys _ => pure (ys.size - numEqs)
  let mvarId := (← mkFreshExprSyntheticOpaqueMVar h).mvarId!
  let (xs, mvarId) ← mvarId.introN numVars
  let (eqs, mvarId) ← mvarId.introN numEqs
  let (r, s) ← SimpH.go |>.run { mvarId, xs := xs.toList, eqs := eqs.toList }
  if r then
    s.mvarId.withContext do
      let eqs := s.eqsNew.reverse.toArray.map mkFVar
      let mut r ← mkForallFVars eqs (mkConst ``False)
      /- We only include variables in `xs` if there is a dependency. -/
      for x in s.xs.reverse do
        if (← dependsOn r x) then
          r ← mkForallFVars #[mkFVar x] r
      trace[Meta.Match.matchEqs] "simplified hypothesis{indentExpr r}"
      check r
      return some r
  else
    return none
