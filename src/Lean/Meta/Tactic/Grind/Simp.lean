/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Simp.Main
import Lean.Meta.Tactic.Grind.Util
import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.MarkNestedProofs

namespace Lean.Meta.Grind

-- TODO: use congruence closure and decision procedures during pre-processing
-- TODO: implement `simp` discharger using preprocessor state

/-- Simplifies the given expression using the `grind` simprocs and normalization theorems. -/
def simp (e : Expr) : GrindM Simp.Result := do
  let simpStats := (← get).simpStats
  let (r, simpStats) ← Meta.simp e (← readThe Context).simp (← readThe Context).simprocs (stats := simpStats)
  modify fun s => { s with simpStats }
  return r

/--
Simplifies `e` using `grind` normalization theorems and simprocs,
and then applies several other preprocessing steps.
-/
def pre (e : Expr) : GrindM Simp.Result := do
  let r ← simp e
  let e' := r.expr
  let e' ← markNestedProofs e'
  let e' ← unfoldReducible e'
  let e' ← eraseIrrelevantMData e'
  let e' ← foldProjs e'
  let e' ← normalizeLevels e'
  let e' ← canon e'
  let e' ← shareCommon e'
  trace[grind.simp] "{e}\n===>\n{e'}"
  return { r with expr := e' }

end Lean.Meta.Grind
