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

builtin_initialize ringExt : SolverExtension State ← registerSolverExtension (return {})

def get' : GoalM State := do
  ringExt.getState

@[inline] def modify' (f : State → State) : GoalM Unit := do
  ringExt.modifyState f

end Lean.Meta.Grind.Arith.CommRing
