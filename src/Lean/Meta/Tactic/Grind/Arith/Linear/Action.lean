/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Action
import Lean.Meta.Tactic.Grind.Arith.Linear.Search
namespace Lean.Meta.Grind.Action

/-- Linear arithmetic action. -/
public def linarith : Action :=
  terminalAction Arith.Linear.check `(grind| linarith)

end Lean.Meta.Grind.Action
