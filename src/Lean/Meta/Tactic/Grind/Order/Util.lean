/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Order.OrderM
import Lean.Meta.Tactic.Grind.Arith.Util
namespace Lean.Meta.Grind.Order

public def Cnstr.pp (c : Cnstr NodeId) : OrderM MessageData := do
  let u ← getExpr c.u
  let v ← getExpr c.v
  let op := match c.kind with
    | .le => "≤"
    | .lt => "<"
    | .eq => "="
  if c.k != 0 then
    return m!"{Arith.quoteIfArithTerm u} {op} {Arith.quoteIfArithTerm v} + {c.k}"
  else
    return m!"{Arith.quoteIfArithTerm u} {op} {Arith.quoteIfArithTerm v}"

end Lean.Meta.Grind.Order
