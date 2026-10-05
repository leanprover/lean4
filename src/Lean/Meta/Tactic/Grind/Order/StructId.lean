/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Order.Types
import Lean.Meta.Sym.Arith.Classify
public section
namespace Lean.Meta.Grind.Order

/--
Returns the order structure id for `type`, if it is at least a preorder.
The classification is done and cached by `Sym.Arith.classifyOrder?` for the whole run;
this function only applies the `order` configuration flag.
-/
def getStructId? (type : Expr) : GoalM (Option Nat) := do
  unless (← getConfig).order do return none
  Sym.Arith.classifyOrder? type

end Lean.Meta.Grind.Order
