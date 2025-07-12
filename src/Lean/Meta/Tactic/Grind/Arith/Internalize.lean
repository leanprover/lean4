/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Tactic.Grind.Arith.Offset
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.EqCnstr
public import Lean.Meta.Tactic.Grind.Arith.CommRing.Internalize
public import Lean.Meta.Tactic.Grind.Arith.Linear.Internalize

public section

namespace Lean.Meta.Grind.Arith

def internalize (e : Expr) (parent? : Option Expr) : GoalM Unit := do
  Offset.internalize e parent?
  Cutsat.internalize e parent?
  CommRing.internalize e parent?
  Linear.internalize e parent?

end Lean.Meta.Grind.Arith
