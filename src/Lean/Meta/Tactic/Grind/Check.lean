/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.Arith.Main
import Lean.Meta.Tactic.Grind.AC.Eq
namespace Lean.Meta.Grind
/--
Checks whether satellite solvers can make progress (e.g., detect unsatisfiability, propagate equations, etc)
-/
public def check : GoalM Bool := do
  Arith.check <||> AC.check

namespace Lean.Meta.Grind
