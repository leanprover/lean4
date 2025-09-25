/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Order.Types
public import Lean.Meta.Tactic.Grind.Order.Internalize
public import Lean.Meta.Tactic.Grind.Order.StructId
public import Lean.Meta.Tactic.Grind.Order.OrderM
public section
namespace Lean.Meta.Grind.Order
builtin_initialize registerTraceClass `grind.order
builtin_initialize registerTraceClass `grind.order.internalize

builtin_initialize
  orderExt.setMethods
    (internalize := Order.internalize)

end Lean.Meta.Grind.Order
