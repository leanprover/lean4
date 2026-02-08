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

public def mkFinish (maxIterations : Nat := maxIterationsDefault) : IO Action := do
  let solvers ← Solvers.mkAction
  let step : Action := solvers <|> instantiate <|> splitNext <|> mbtc
  return checkTactic (warnOnly := true) >> intros 0 >> assertAll >> step.loop maxIterations

end Lean.Meta.Grind.Action
