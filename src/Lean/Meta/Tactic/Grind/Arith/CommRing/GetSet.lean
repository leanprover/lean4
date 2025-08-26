/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
public section
namespace Lean.Meta.Grind.Arith.CommRing
def get' : GoalM State := do
  return (← get).arith.ring

@[inline] def modify' (f : State → State) : GoalM Unit := do
  modify fun s => { s with arith.ring := f s.arith.ring }
end Lean.Meta.Grind.Arith.CommRing
