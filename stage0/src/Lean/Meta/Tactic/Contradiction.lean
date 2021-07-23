/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.MatchUtil
import Lean.Meta.Tactic.Assumption
import Lean.Meta.Tactic.Cases

namespace Lean.Meta

def elimEmptyInductive (mvarId : MVarId) (fvarId : FVarId) (searchDepth : Nat) : MetaM Bool :=
  match searchDepth with
  | 0 => return false
  | searchDepth + 1 =>
    withMVarContext mvarId do
      let localDecl ← getLocalDecl fvarId
      let type ← whnfD localDecl.type
      matchConstInduct type.getAppFn (fun _ => pure false) fun info _ => do
        if info.ctors.length == 0 || info.numIndices > 0 then
          -- We only consider inductives with no constructors and indexed families
          commitWhen do
            let subgoals ← try cases mvarId fvarId catch _ => return false
            for subgoal in subgoals do
              -- If one of the fields is uninhabited, then we are done
              let mut found := false
              for field in subgoal.fields do
                let field := subgoal.subst.apply field
                if field.isFVar then
                  if (← elimEmptyInductive subgoal.mvarId field.fvarId! searchDepth) then
                    found := true
                    break
              unless found == true do -- TODO: check why we need true here
                return false
            return true
        else
          return false

def contradictionCore (mvarId : MVarId) (useDecide : Bool) (searchDepth : Nat) : MetaM Bool := do
  withMVarContext mvarId do
    checkNotAssigned mvarId `contradiction
    for localDecl in (← getLCtx) do
      unless localDecl.isAuxDecl do
        -- (h : ¬ p) (h' : p)
        if let some p ← matchNot? localDecl.type then
          if let some pFVarId ← findLocalDeclWithType? p then
            assignExprMVar mvarId (← mkAbsurd (← getMVarType mvarId) (mkFVar pFVarId) localDecl.toExpr)
            return true
        -- (h : <empty-inductive-type>)
        if (← elimEmptyInductive mvarId localDecl.fvarId searchDepth) then
          return true
        -- (h : x ≠ x)
        if let some (_, lhs, rhs) ← matchNe? localDecl.type then
          if (← isDefEq lhs rhs) then
            assignExprMVar mvarId (← mkAbsurd (← getMVarType mvarId) (← mkEqRefl lhs) localDecl.toExpr)
            return true
        -- (h : ctor₁ ... = ctor₂ ...)
        if let some (_, lhs, rhs) ← matchEq? localDecl.type then
          if let some lhsCtor ← matchConstructorApp? lhs then
          if let some rhsCtor ← matchConstructorApp? rhs then
          if lhsCtor.name != rhsCtor.name then
            assignExprMVar mvarId (← mkNoConfusion (← getMVarType mvarId) localDecl.toExpr)
            return true
        -- (h : p) s.t. `decide p` evaluates to `false`
        if useDecide && !localDecl.type.hasFVar && !localDecl.type.hasMVar then
          try
            let d ← mkDecide localDecl.type
            let r ← withDefault <| whnf d
            if r.isConstOf ``false then
              let hn := mkAppN (mkConst ``ofDecideEqFalse) <| d.getAppArgs.push (← mkEqRefl d)
              assignExprMVar mvarId (← mkAbsurd (← getMVarType mvarId) localDecl.toExpr hn)
              return true
          catch _ =>
            pure ()
    return false

def contradiction (mvarId : MVarId) (useDecide : Bool := true) (searchDepth : Nat := 2) : MetaM Unit :=
  unless (← contradictionCore mvarId useDecide searchDepth) do
    throwTacticEx `contradiction mvarId ""

end Lean.Meta
