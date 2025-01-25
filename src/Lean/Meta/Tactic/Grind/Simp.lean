/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.Lemmas
import Lean.Meta.Tactic.Assert
import Lean.Meta.Tactic.Simp.Main
import Lean.Meta.Tactic.Grind.Util
import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.MatchDiscrOnly
import Lean.Meta.Tactic.Grind.MarkNestedProofs
import Lean.Meta.Tactic.Grind.Canon

namespace Lean.Meta.Grind
/-- Simplifies the given expression using the `grind` simprocs and normalization theorems. -/
def simpCore (e : Expr) : GrindM Simp.Result := do
  let simpStats := (← get).simpStats
  let (r, simpStats) ← Meta.simp e (← readThe Context).simp (← readThe Context).simprocs (stats := simpStats)
  modify fun s => { s with simpStats }
  return r

/--
Simplifies `e` using `grind` normalization theorems and simprocs,
and then applies several other preprocessing steps.
-/
def simp (e : Expr) : GoalM Simp.Result := do
  let e ← instantiateMVars e
  let r ← simpCore e
  let e' := r.expr
  let e' ← unfoldReducible e'
  let e' ← abstractNestedProofs e'
  let e' ← markNestedProofs e'
  let e' ← eraseIrrelevantMData e'
  let e' ← foldProjs e'
  let e' ← normalizeLevels e'
  let e' ← eraseSimpMatchDiscrsOnly e'
  let e' ← canon e'
  let e' ← shareCommon e'
  trace[grind.simp] "{e}\n===>\n{e'}"
  return { r with expr := e' }

end Lean.Meta.Grind
