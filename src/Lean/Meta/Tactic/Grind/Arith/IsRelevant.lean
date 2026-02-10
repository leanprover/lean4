/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.Arith.Cutsat.ToInt
import Lean.Meta.Tactic.Grind.Arith.Linear.StructId
public section
namespace Lean.Meta.Grind.Arith

def isSupportedType (α  : Expr) : GoalM Bool := do
  if isNatType α || isIntType α then
    return true
  else if (← Cutsat.getToIntId? α).isSome then
    return true
  else if (← Linear.getStructId? α).isSome then
    return true
  else
    return false

partial def isRelevantPred (e : Expr) : GoalM Bool :=
  match_expr e with
  | Not p => isRelevantPred p
  | LE.le α _ _ _ => isSupportedType α
  | LT.lt α _ _ _ => isSupportedType α
  | Eq α _ _ => isSupportedType α
  | Dvd.dvd α _ _ _ => isSupportedType α
  | _ => return false

end Lean.Meta.Grind.Arith
