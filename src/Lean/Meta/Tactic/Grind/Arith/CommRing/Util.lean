/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Types

namespace Lean.Meta.Grind.Arith.CommRing

def get' : GoalM State := do
  return (← get).arith.ring

@[inline] def modify' (f : State → State) : GoalM Unit := do
  modify fun s => { s with arith.ring := f s.arith.ring }

def getRing (ringId : Nat) : GoalM Ring := do
  let s ← get'
  if h : ringId < s.rings.size then
    return s.rings[ringId]
  else
    throwError "`grind` internal error, invalid ringId"

@[inline] def modifyRing (ringId : Nat) (f : Ring → Ring) : GoalM Unit := do
  modify' fun s => { s with rings := s.rings.modify ringId f }

end Lean.Meta.Grind.Arith.CommRing
