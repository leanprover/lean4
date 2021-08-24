/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.MatchUtil
import Lean.Meta.Tactic.Assumption
import Lean.Meta.Tactic.Cases
import Lean.Meta.Tactic.Apply

namespace Lean.Meta

structure Contradiction.Config where
  useDecide  : Bool := true
  /- When checking for empty types, `searchFuel` specifies the number of goals visited. -/
  searchFuel : Nat  := 16
  /- Support for hypotheses such as
     ```
     h : (x y : Nat) (ys : List Nat) → x = 0 → y::ys = [a, b, c] → False
     ```
     This kind of hypotheses appear when proving conditional equation theorems for match expressions. -/
  genDiseq : Bool := false

-- We only consider inductives with no constructors and indexed families
private def isElimEmptyInductiveCandidate (fvarId : FVarId) : MetaM Bool := do
  let localDecl ← getLocalDecl fvarId
  let type ← whnfD localDecl.type
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
  modify (. - 1)
  -- We only consider inductives with no constructors and indexed families
  commitWhen do
    let subgoals ← try cases mvarId fvarId catch ex => trace[Meta.Tactic.contradiction] "{ex.toMessageData}"; return false
    trace[Meta.Tactic.contradiction] "elimEmptyInductive, number subgoals: {subgoals.size}"
    for subgoal in subgoals do
      -- If one of the fields is uninhabited, then we are done
      let found ← withMVarContext subgoal.mvarId do
        for field in subgoal.fields do
          let field := subgoal.subst.apply field
          if field.isFVar then
            if (← isElimEmptyInductiveCandidate field.fvarId!) then
              if (← elim subgoal.mvarId field.fvarId!) then
                return true
        return false
      unless found == true do -- TODO: check why we need true here
        return false
    return true

end ElimEmptyInductive

private def elimEmptyInductive (mvarId : MVarId) (fvarId : FVarId) (fuel : Nat) : MetaM Bool := do
  withMVarContext mvarId do
    if (← isElimEmptyInductiveCandidate fvarId) then
      commitWhen do
        ElimEmptyInductive.elim (← exfalso mvarId) fvarId |>.run' fuel
    else
      return false

/-- Return true if `e` is of the form `(x : α) → ... → s = t → ... → False` -/
private def isGenDiseq (e : Expr) : Bool :=
  match e with
  | Expr.forallE _ d b _ => (d.isEq || b.hasLooseBVar 0) && isGenDiseq b
  | _ => e.isConstOf ``False

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
    for arg in args do
      let argType ← inferType arg
      if let some (_, lhs, rhs) ← matchEq? argType then
        unless (← isDefEq lhs rhs) do
          return none
        unless (← isDefEq arg (← mkEqRefl lhs)) do
          return none
    let falseProof ← instantiateMVars (mkAppN localDecl.toExpr args)
    if (← hasAssignableMVar falseProof) then
      return none
    return some (← mkFalseElim (← getMVarType mvarId) falseProof)
  if let some val := val? then
    assignExprMVar mvarId val
    return true
  else
    return false

def contradictionCore (mvarId : MVarId) (config : Contradiction.Config) : MetaM Bool := do
  withMVarContext mvarId do
    checkNotAssigned mvarId `contradiction
    for localDecl in (← getLCtx) do
      unless localDecl.isAuxDecl do
        -- (h : ¬ p) (h' : p)
        if let some p ← matchNot? localDecl.type then
          if let some pFVarId ← findLocalDeclWithType? p then
            assignExprMVar mvarId (← mkAbsurd (← getMVarType mvarId) (mkFVar pFVarId) localDecl.toExpr)
            return true
        -- (h : x ≠ x)
        if let some (_, lhs, rhs) ← matchNe? localDecl.type then
          if (← isDefEq lhs rhs) then
            assignExprMVar mvarId (← mkAbsurd (← getMVarType mvarId) (← mkEqRefl lhs) localDecl.toExpr)
            return true
        let mut isEq := false
        -- (h : ctor₁ ... = ctor₂ ...)
        if let some (_, lhs, rhs) ← matchEq? localDecl.type then
          isEq := true
          if let some lhsCtor ← matchConstructorApp? lhs then
          if let some rhsCtor ← matchConstructorApp? rhs then
          if lhsCtor.name != rhsCtor.name then
            assignExprMVar mvarId (← mkNoConfusion (← getMVarType mvarId) localDecl.toExpr)
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
                assignExprMVar mvarId (← mkAbsurd (← getMVarType mvarId) localDecl.toExpr hn)
                return true
            catch _ =>
              pure ()
        -- "generalized" diseq
        if config.genDiseq && isGenDiseq localDecl.type then
          if (← processGenDiseq mvarId localDecl) then
            return true
        -- (h : <empty-inductive-type>)
        unless isEq do
          -- We do not use `elimEmptyInductive` for equality, since `cases h` produces a huge proof
          -- when `(h : 10000 = 10001)`. TODO: `cases` add a threshold at `cases`
          if (← elimEmptyInductive mvarId localDecl.fvarId config.searchFuel) then
            return true
    return false

def contradiction (mvarId : MVarId) (config : Contradiction.Config := {}) : MetaM Unit :=
  unless (← contradictionCore mvarId config) do
    throwTacticEx `contradiction mvarId ""

builtin_initialize registerTraceClass `Meta.Tactic.contradiction

end Lean.Meta
