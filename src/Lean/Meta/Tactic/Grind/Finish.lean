/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Action
import Lean.Meta.Tactic.Grind.EMatchAction
import Lean.Meta.Tactic.Grind.Split
namespace Lean.Meta.Grind.Action

public abbrev maxIterationsDefault := 10000 -- **TODO**: Add option

/--
The `finish` action: introduces hypotheses, asserts all pending facts, and then repeats
the solvers, E-matching, case-splitting, and model-based theory combination until the goal is
closed, no step applies, or `maxIterations` is reached.

The action does not validate the script it generates when tracing. Callers that report the
script (e.g., `grind?` and `finish?`) replay it at the goal they consider appropriate.
-/
public def mkFinish (maxIterations : Nat := maxIterationsDefault) : IO Action := do
  let solvers ← Solvers.mkAction
  let step : Action := solvers <|> instantiate <|> splitNext <|> mbtc
  return intros 0 >> assertAll >> step.loop maxIterations

end Lean.Meta.Grind.Action
