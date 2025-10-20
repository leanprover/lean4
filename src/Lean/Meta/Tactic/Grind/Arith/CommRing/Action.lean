/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Action
import Lean.Meta.Tactic.Grind.Arith.CommRing.EqCnstr
namespace Lean.Meta.Grind.Action

/-- Ring solver action. -/
public def ring : Action :=
  solverAction Arith.CommRing.check `(grind| ring)

end Lean.Meta.Grind.Action
