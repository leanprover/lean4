/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Types

namespace Lean.Meta.Grind

private partial def propagateInjEqs (eqs : Expr) (proof : Expr) : GoalM Unit := do
  -- Remark: we must use `shareCommon` before using `pushEq` and `pushHEq`.
  -- This is needed because the result type of the injection theorem may allocate
  match_expr eqs with
  | And left right =>
    propagateInjEqs left (.proj ``And 0 proof)
    propagateInjEqs right (.proj ``And 1 proof)
  | Eq _ lhs rhs    =>
    pushEq (← shareCommon lhs) (← shareCommon rhs) proof
  | HEq _ lhs _ rhs =>
    pushHEq (← shareCommon lhs) (← shareCommon rhs) proof
  | _ =>
   reportIssue! "unexpected injectivity theorem result type{indentExpr eqs}"
   return ()

/--
Given constructors `a` and `b`, propagate equalities if they are the same,
and close goal if they are different.
-/
def propagateCtor (a b : Expr) : GoalM Unit := do
  let aType ← whnfD (← inferType a)
  let bType ← whnfD (← inferType b)
  unless (← withDefault <| isDefEq aType bType) do
    return ()
  let ctor₁ := a.getAppFn
  let ctor₂ := b.getAppFn
  if ctor₁ == ctor₂ then
    let .const ctorName _ := a.getAppFn | return ()
    let injDeclName := Name.mkStr ctorName "inj"
    unless (← getEnv).contains injDeclName do return ()
    let info ← getConstInfo injDeclName
    let n := info.type.getForallArity
    let mask : Array (Option Expr) := mkArray n none
    let mask := mask.set! (n-1) (some (← mkEqProof a b))
    let injLemma ← mkAppOptM injDeclName mask
    propagateInjEqs (← inferType injLemma) injLemma
  else
    let .const declName _ := aType.getAppFn | return ()
    let noConfusionDeclName := Name.mkStr declName "noConfusion"
    unless (← getEnv).contains noConfusionDeclName do return ()
    closeGoal (← mkNoConfusion (← getFalseExpr) (← mkEqProof a b))

end Lean.Meta.Grind
