/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util

namespace Lean.Meta.Grind.Arith.Cutsat
/-!
`Int` expressions are normalized by the `grind` preprocessor, but we
dynamically convert expressions from other types into `Int` expressions
and these expressions must be normalized inside of the cutsat module.
-/

/-- Converts the given integer expression into `Int.Linear.Expr` -/
partial def toLinearExpr (e : Expr) (generation : Nat := 0) : GoalM Int.Linear.Expr := do
  let toVar (e : Expr) := do
    let e ← shareCommon e
    if (← alreadyInternalized e) then
      return .var (← mkVar e)
    else
      internalize e generation
      return .var (← mkVar e)
  let mul (a b : Expr) := do
    match (← getIntValue? a) with
    | some k => return .mulL k (← toLinearExpr b)
    | none => match (← getIntValue? b) with
      | some k => return .mulR (← toLinearExpr a) k
      | none => toVar e
  match_expr e with
  | OfNat.ofNat _ _ _ =>
    if let some n ← getIntValue? e then return .num n
    else toVar e
  | Neg.neg _ i a =>
    if (← isInstNegInt i) then return .neg (← toLinearExpr a)
    else toVar e
  | HAdd.hAdd _ _ _ i a b =>
    if (← isInstHAddInt i) then return .add (← toLinearExpr a) (← toLinearExpr b)
    else toVar e
  | HSub.hSub _ _ _ i a b =>
    if (← isInstHSubInt i) then return .sub (← toLinearExpr a) (← toLinearExpr b)
    else toVar e
  | HMul.hMul _ _ _ i a b =>
    if (← isInstHMulInt i) then mul a b
    else toVar e
  | _ => toVar e

end Lean.Meta.Grind.Arith.Cutsat
