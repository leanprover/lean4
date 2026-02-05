/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
import Init.Grind.Propagator
import Lean.Meta.Tactic.Grind.Arith.Cutsat.LeCnstr
import Lean.Meta.Tactic.Grind.Arith.Linear.IneqCnstr
public import Lean.Meta.Tactic.Grind.PropagatorAttr
public section
namespace Lean.Meta.Grind.Arith

builtin_grind_propagator propagateLE ↓LE.le := fun e => do
  if (← isEqTrue e) then
    Cutsat.propagateLe e (eqTrue := true)
    Linear.propagateIneq e (eqTrue := true)
  else if (← isEqFalse e) then
    Cutsat.propagateLe e (eqTrue := false)
    Linear.propagateIneq e (eqTrue := false)

builtin_grind_propagator propagateLT ↓LT.lt := fun e => do
  if (← isEqTrue e) then
    Linear.propagateIneq e (eqTrue := true)
    Cutsat.propagateLt e (eqTrue := true)
  else if (← isEqFalse e) then
    Linear.propagateIneq e (eqTrue := false)
    Cutsat.propagateLt e (eqTrue := false)

end Lean.Meta.Grind.Arith
