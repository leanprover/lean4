/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

module
prelude
public import Lean.Meta.Basic
import Lean.Meta.Tactic.Contradiction
import Lean.Meta.Tactic.Cleanup

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
        if (← isDefEq lhs rhs) then
          let mvarId ← s.mvarId.clear eq
          modify fun s => { s with mvarId }
          return true
        if (← s.mvarId.closeIfDistinctFloatLits (mkFVar eq) lhs rhs) then
          return false
        if rhs.isFVar && s.xs.contains rhs.fvarId! then
          substRHS eq rhs.fvarId!
          return true
      if let some _ ← matchHEq? eqType then
        -- Try to convert `HEq` into `Eq`
        let (eqNew, mvarId) ← heqToEq s.mvarId eq (tryToClear := true)
        if mvarId != s.mvarId then
          modify fun s => { s with mvarId, eqs := eqNew :: s.eqs }
          return true
        -- If it is not possible, we try to show the hypothesis is redundant by substituting even
        -- variables that are not at `s.xs`, and then use contradiction.
        else
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
Simplifies an overlap hypothesis of an equation for a `match` alternative.

The equation for an alternative has one hypothesis for each previous alternative that overlaps
it. The hypothesis states that the previous alternative does not match. Before it is simplified,
it has the form `∀ xs, eqs → False`, where `xs` are the pattern variables of the previous
alternative, and `eqs` are `numEqs` equations `p = q` or `p ≍ q` between the patterns of the two
alternatives.

The type of the goal `mvarId` must be a hypothesis of this form. This function returns
- `none` if the hypothesis is redundant: the equations `eqs` are contradictory, and `mvarId` has
  been closed. Example: `none = some 0 → False`.
- `some mvarId'` otherwise. The type of `mvarId'` is the simplified hypothesis, and `mvarId` has
  been proved using `mvarId'`.

The equations are processed one at a time.
- `p = q` is removed if `p` and `q` are definitionally equal.
- `p = x`, where `x` is one of the variables `xs`, is removed, and `x` is replaced with `p`.
- `p ≍ q` is replaced with `p = q` if `p` and `q` have the same type.
- An equation between constructor applications is replaced with the equations between their
  fields. If the constructors are different, the hypothesis is redundant.
- Any other equation is kept.

The simplified hypothesis is `∀ xs', eqs' → False`, where `eqs'` are the equations that were kept,
and `xs'` are the variables in `xs` that occur in them.

Examples, where `n : Nat` and `x : Nat × Nat` are variables of the alternative being processed:
- `some n = some 0 → False` is simplified to `n = 0 → False`.
- `∀ m, some n = some (m + 1) → False` is simplified to `∀ m, n = m + 1 → False`.
- `∀ a, n = a → x = (a, 0) → False` is simplified to `x = (n, 0) → False`.
- `∀ m, some n = some m → False` is simplified to `False`: the previous alternative always matches.
-/
public partial def simpH (mvarId : MVarId) (numEqs : Nat) : MetaM (Option MVarId) := withDefault do
  let numVars ← forallTelescope (← mvarId.getType) fun ys _ => pure (ys.size - numEqs)
  /-
  Remove the local declarations that the hypothesis does not depend on.

  We use `cleanup` because it builds the new local context in one pass. We used to use `tryClearMany`,
  which clears the declarations one at a time, and creates a new goal for each one it clears.
  Example: for
  ```
  match x with
  | "a₁" => ..
  ...
  | "aₙ" => ..
  | _ => ..
  ```
  the local context contains `motive`, `x`, the `n+1` alternatives, and the variable `y` of the
  last pattern. The last alternative has the `n` overlap hypotheses `y = "aᵢ" → False`, and each
  of them only depends on `y`.
  With `tryClearMany`, each call clears more than `n` declarations, and more than `n^2` goals
  are created. With `cleanup`, `n` goals are created.
  -/
  let mvarId ← mvarId.cleanup (indirectProps := false)
  let (xs, mvarId) ← mvarId.introN numVars
  let (eqs, mvarId) ← mvarId.introN numEqs
  let (r, s) ← SimpH.go |>.run { mvarId, xs := xs.toList, eqs := eqs.toList }
  if r then
    s.mvarId.withContext do
      let eqs := s.eqsNew.reverse.toArray
      let mvarId' := s.mvarId
      let mvarId' := (← mvarId'.revert eqs).2
      /- We only include variables in `xs` if there is a dependency. -/
      let r ← mvarId'.getType
      mvarId'.withContext do
      let xs ← s.xs.toArray.reverse.filterM (dependsOn r ·)
      let mvarId' := (← mvarId'.revert xs).2
      return (some mvarId')
  else
    return none

/--
Returns the simplified form of the overlap hypothesis `h` of an equation for a `match`
alternative, or `none` if `h` is redundant. `h` must be of the form `∀ xs, eqs → False`, where
`eqs` are `numEqs` equations. See `simpH` for the simplification steps and examples.

Only the statement is computed: `h` is the type of the hypothesis as generated from the patterns,
and the result is the type used in the statement of the equation.
-/
public def simpH? (h : Expr) (numEqs : Nat) : MetaM (Option Expr) := do
  let prf ← mkFreshExprSyntheticOpaqueMVar h
  match (← simpH prf.mvarId! numEqs) with
  | none   => return none
  | some mvarId' =>
    return some (← mvarId'.getType)
