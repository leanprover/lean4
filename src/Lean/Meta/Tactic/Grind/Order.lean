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
public import Lean.Meta.Tactic.Grind.Order.Assert
public import Lean.Meta.Tactic.Grind.Order.Util
public section
namespace Lean.Meta.Grind.Order
builtin_initialize registerTraceClass `grind.order
builtin_initialize registerTraceClass `grind.order.assert
builtin_initialize registerTraceClass `grind.order.internalize
builtin_initialize registerTraceClass `grind.order.internalize.term

builtin_initialize registerTraceClass `grind.debug.order
builtin_initialize registerTraceClass `grind.debug.order.add_edge (inherited := true)
builtin_initialize registerTraceClass `grind.debug.order.propagate (inherited := true)
builtin_initialize registerTraceClass `grind.debug.order.check_eq_true (inherited := true)
builtin_initialize registerTraceClass `grind.debug.order.check_eq_false (inherited := true)

builtin_initialize
  orderExt.setMethods
    (internalize := Order.internalize)
    (newEq       := Order.processNewEq)

end Lean.Meta.Grind.Order
