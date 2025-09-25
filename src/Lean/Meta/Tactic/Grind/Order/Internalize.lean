/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Order.OrderM
import Lean.Meta.Tactic.Grind.Order.StructId
namespace Lean.Meta.Grind.Order

def getType? (e : Expr) : Option Expr :=
  match_expr e with
  | LE.le α _ _ _ => some α
  | LT.lt α _ _ _ => some α
  | HAdd.hAdd α _ _ _ _ _ => some α
  | HSub.hSub α _ _ _ _ _ => some α
  | OfNat.ofNat α _ _ => some α
  | _ => none

def isForbiddenParent (parent? : Option Expr) : Bool :=
  if let some parent := parent? then
    getType? parent |>.isSome
  else
    false

public def internalize (e : Expr) (parent? : Option Expr) : GoalM Unit := do
  unless (← getConfig).order do return ()
  let some α := getType? e | return ()
  if isForbiddenParent parent? then return ()
  let some structId ← getStructId? α | return ()
  OrderM.run structId do
  trace[grind.order.internalize] "{e}"
  -- TODO

end Lean.Meta.Grind.Order
