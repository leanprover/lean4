/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.MatchUtil
import Lean.Meta.Tactic.Assumption
import Lean.Meta.Tactic.Cases
import Lean.Meta.Tactic.Apply

namespace Lean.Meta

structure Contradiction.Config where
  useDecide  : Bool := true
  /-- Check whether any of the hypotheses is an empty type. -/
  emptyType  : Bool := true
  /-- When checking for empty types, `searchFuel` specifies the number of goals visited. -/
  searchFuel : Nat  := 16
  /-- Support for hypotheses such as
     ```
     h : (x y : Nat) (ys : List Nat) → x = 0 → y::ys = [a, b, c] → False
     ```
     This kind of hypotheses appear when proving conditional equation theorems for match expressions. -/
  genDiseq : Bool := false

/--
  Try to close the current goal by looking for a proof of `False` nested in a `False.Elim` application in the target.
  Return `true` iff the goal has been closed.
-/
private def nestedFalseElim (mvarId : MVarId) : MetaM Bool := do
  let target ← mvarId.getType
  if let some falseElim := target.find? fun e => e.isAppOfArity ``False.elim 2 && !e.appArg!.hasLooseBVars then
    let falseProof := falseElim.appArg!
    mvarId.assign (← mkFalseElim (← mvarId.getType) falseProof)
    return true
  else
    return false

-- We only consider inductives with no constructors and indexed families
private def isElimEmptyInductiveCandidate (fvarId : FVarId) : MetaM Bool := do
  let type ← whnfD (← fvarId.getType)
  matchConstInduct type.getAppFn (fun _ => pure false) fun info _ => do
    return info.ctors.length == 0 || info.numIndices > 0

namespace ElimEmptyInductive

abbrev M := StateRefT Nat MetaM

instance : MonadBacktrack SavedState M where
  saveState      := Meta.saveState
  restoreState s := s.restore

partial def elim (mvarId : MVarId) (fvarId : FVarId) : M Bool := do
  if (← get) == 0 then
    trace[Meta.Tactic.contradiction] "elimEmptyInductive out-of-fuel"
    return false
  modify (· - 1)
  -- We only consider inductives with no constructors and indexed families
  commitWhen do
    let subgoals ← try mvarId.cases fvarId catch ex => trace[Meta.Tactic.contradiction] "{ex.toMessageData}"; return false
    trace[Meta.Tactic.contradiction] "elimEmptyInductive, number subgoals: {subgoals.size}"
    for subgoal in subgoals do
      -- If one of the fields is uninhabited, then we are done
      let found ← subgoal.mvarId.withContext do
        for field in subgoal.fields do
          let field := subgoal.subst.apply field
          if field.isFVar then
            if (← isElimEmptyInductiveCandidate field.fvarId!) then
              if (← elim subgoal.mvarId field.fvarId!) then
                return true
        return false
      unless found do
        return false
    return true

end ElimEmptyInductive

private def elimEmptyInductive (mvarId : MVarId) (fvarId : FVarId) (fuel : Nat) : MetaM Bool := do
  mvarId.withContext do
    if (← isElimEmptyInductiveCandidate fvarId) then
      commitWhen do
        ElimEmptyInductive.elim (← mvarId.exfalso) fvarId |>.run' fuel
    else
      return false

/--
  See `Simp.isEqnThmHypothesis`
-/
private abbrev isGenDiseq (e : Expr) : Bool :=
  Simp.isEqnThmHypothesis e

/--
  Given `e` s.t. `isGenDiseq e`, generate a bit-mask `mask` s.t. `mask[i] = true` iff
  the `i`-th binder is an equality without forward dependencies.

  See `processGenDiseq`
-/
private def mkGenDiseqMask (e : Expr) : Array Bool :=
  go e #[]
where
  go (e : Expr) (acc : Array Bool) : Array Bool :=
    match e with
    | Expr.forallE _ d b _ => go b (acc.push (!b.hasLooseBVar 0 && (d.isEq || d.isHEq)))
    | _ => acc

/--
  Close goal if `localDecl` is a "generalized disequality". Example:
  ```
  h : (x y : Nat) (ys : List Nat) → x = 0 → y::ys = [a, b, c] → False
  ```
  This kind of hypotheses is created when we generate conditional equations for match expressions.
-/
private def processGenDiseq (mvarId : MVarId) (localDecl : LocalDecl) : MetaM Bool := do
  assert! isGenDiseq localDecl.type
  let val? ← withNewMCtxDepth do
    let (args, _, _) ← forallMetaTelescope localDecl.type
    let mask  := mkGenDiseqMask localDecl.type
    for arg in args, useRefl in mask do
      if useRefl then
        /- Remark: we should not try to use `refl` for equalities that have forward dependencies because
           they correspond to constructor fields. We did not use to have this extra test, and this method failed
           to close the following goal.
           ```
            ...
            ns' : NEList String
            h' : NEList.notUno ns' = true
            : ∀ (ns : NEList String) (h : NEList.notUno ns = true), Value.lam (Lambda.mk ns' h') = Value.lam (Lambda.mk ns h) → False
            ⊢ h_1 l a = h_2 v

           ```
         -/
        if let some (_, lhs, _) ← matchEq? (← inferType arg) then
          unless (← isDefEq arg (← mkEqRefl lhs)) do
            return none
        if let some (_, lhs, _,  _) ← matchHEq? (← inferType arg) then
          unless (← isDefEq arg (← mkHEqRefl lhs)) do
            return none
    let falseProof ← instantiateMVars (mkAppN localDecl.toExpr args)
    if (← hasAssignableMVar falseProof) then
      return none
    return some (← mkFalseElim (← mvarId.getType) falseProof)
  if let some val := val? then
    mvarId.assign val
    return true
  else
    return false

/--
Return `true` if goal `mvarId` has contradictory hypotheses.
See `MVarId.contradiction` for the list of tests performed by this method.
-/
def _root_.Lean.MVarId.contradictionCore (mvarId : MVarId) (config : Contradiction.Config) : MetaM Bool := do
  mvarId.withContext do
    mvarId.checkNotAssigned `contradiction
    if (← nestedFalseElim mvarId) then
      return true
    for localDecl in (← getLCtx) do
      unless localDecl.isImplementationDetail do
        -- (h : ¬ p) (h' : p)
        if let some p ← matchNot? localDecl.type then
          if let some pFVarId ← findLocalDeclWithType? p then
            -- We use `False.elim` because `p`'s type may be Type
            mvarId.assign (← mkFalseElim (← mvarId.getType) (mkApp localDecl.toExpr (mkFVar pFVarId)))
            return true
        -- (h : x ≠ x)
        if let some (_, lhs, rhs) ← matchNe? localDecl.type then
          if (← isDefEq lhs rhs) then
            mvarId.assign (← mkAbsurd (←  mvarId.getType) (← mkEqRefl lhs) localDecl.toExpr)
            return true
        let mut isEq := false
        -- (h : ctor₁ ... = ctor₂ ...)
        if let some (_, lhs, rhs) ← matchEq? localDecl.type then
          isEq := true
          if let some lhsCtor ← matchConstructorApp? lhs then
          if let some rhsCtor ← matchConstructorApp? rhs then
          if lhsCtor.name != rhsCtor.name then
            mvarId.assign (← mkNoConfusion (← mvarId.getType) localDecl.toExpr)
            return true
        let mut isHEq := false
        -- (h : HEq (ctor₁ ...) (ctor₂ ...))
        if let some (α, lhs, β, rhs) ← matchHEq? localDecl.type then
          isHEq := true
          if let some lhsCtor ← matchConstructorApp? lhs then
          if let some rhsCtor ← matchConstructorApp? rhs then
          if lhsCtor.name != rhsCtor.name then
            if (← isDefEq α β) then
              mvarId.assign (← mkNoConfusion (← mvarId.getType) (← mkEqOfHEq localDecl.toExpr))
              return true
        -- (h : p) s.t. `decide p` evaluates to `false`
        if config.useDecide && !localDecl.type.hasFVar then
          let type ← instantiateMVars localDecl.type
          if !type.hasMVar && !type.hasFVar then
            try
              let d ← mkDecide localDecl.type
              let r ← withDefault <| whnf d
              if r.isConstOf ``false then
                let hn := mkAppN (mkConst ``of_decide_eq_false) <| d.getAppArgs.push (← mkEqRefl d)
                mvarId.assign (← mkAbsurd (← mvarId.getType) localDecl.toExpr hn)
                return true
            catch _ =>
              pure ()
        -- "generalized" diseq
        if config.genDiseq && isGenDiseq localDecl.type then
          if (← processGenDiseq mvarId localDecl) then
            return true
        -- (h : <empty-inductive-type>)
        if config.emptyType && !isEq && !isHEq then
          -- We do not use `elimEmptyInductive` for equality, since `cases h` produces a huge proof
          -- when `(h : 10000 = 10001)`. TODO: `cases` add a threshold at `cases`
          if (← elimEmptyInductive mvarId localDecl.fvarId config.searchFuel) then
            return true
    return false

/--
Try to close the goal using "contradictions" such as
- Contradictory hypotheses `h₁ : p` and `h₂ : ¬ p`.
- Contradictory disequality `h : x ≠ x`.
- Contradictory equality between different constructors, e.g., `h : List.nil = List.cons x xs`.
- Empty inductive types, e.g., `x : Fin 0`.
- Decidable propositions that evaluate to false, i.e., a hypothesis `h : p` s.t. `decide p` reduces to `false`.
  This is only tried if `Config.useDecide = true`.

Throw exception if goal failed to be closed.
-/
def _root_.Lean.MVarId.contradiction (mvarId : MVarId) (config : Contradiction.Config := {}) : MetaM Unit :=
  unless (← mvarId.contradictionCore config) do
    throwTacticEx `contradiction mvarId

builtin_initialize registerTraceClass `Meta.Tactic.contradiction

end Lean.Meta
