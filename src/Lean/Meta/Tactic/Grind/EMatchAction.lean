/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Action
public import Lean.Meta.Tactic.Grind.Intro
import Lean.Meta.Tactic.Grind.EMatch
public section
namespace Lean.Meta.Grind.Action

def instantiate' : Action := fun goal kna kp => do
  let (progress, goal') ← GoalM.run goal ematch
  -- **TODO**: filter relevant instances
  if progress then
    concatTactic (← kp goal') `(grind| instantiate)
  else
    kna goal

def instantiate : Action :=
  instantiate' >> assertAll

end Lean.Meta.Grind.Action
