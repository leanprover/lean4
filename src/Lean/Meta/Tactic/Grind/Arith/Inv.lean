/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Arith.Offset
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Inv
import Lean.Meta.Tactic.Grind.Arith.Linear.Inv

namespace Lean.Meta.Grind.Arith

def checkInvariants : GoalM Unit := do
  Offset.checkInvariants
  Cutsat.checkInvariants
  Linear.checkInvariants

end Lean.Meta.Grind.Arith
