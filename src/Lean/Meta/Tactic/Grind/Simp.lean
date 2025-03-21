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
private def simpCore (e : Expr) : GrindM Simp.Result := do
  let simpStats := (← get).simpStats
  let (r, simpStats) ← Meta.simp e (← readThe Context).simp (← readThe Context).simprocs (stats := simpStats)
  modify fun s => { s with simpStats }
  return r

/--
Preprocesses `e` using `grind` normalization theorems and simprocs,
and then applies several other preprocessing steps.
-/
def preprocess (e : Expr) : GoalM Simp.Result := do
  let e ← instantiateMVars e
  let r ← simpCore e
  let e' := r.expr
  let e' ← unfoldReducible e'
  let e' ← abstractNestedProofs e'
  let e' ← markNestedProofs e'
  let e' ← eraseIrrelevantMData e'
  let e' ← foldProjs e'
  let e' ← normalizeLevels e'
  let r' ← eraseSimpMatchDiscrsOnly e'
  let r ← r.mkEqTrans r'
  let e' := r'.expr
  let r' ← replacePreMatchCond e'
  let r ← r.mkEqTrans r'
  let e' := r'.expr
  let e' ← canon e'
  let e' ← shareCommon e'
  trace_goal[grind.simp] "{e}\n===>\n{e'}"
  return { r with expr := e' }

def pushNewFact' (prop : Expr) (proof : Expr) (generation : Nat := 0) : GoalM Unit := do
  let r ← preprocess prop
  let prop' := r.expr
  let proof := if let some h := r.proof? then
    mkApp4 (mkConst ``Eq.mp [levelZero]) prop prop' h proof
  else
    proof
  modify fun s => { s with newFacts := s.newFacts.push <| .fact prop' proof generation }


/-- Infers the type of the proof, preprocess it, and adds it to todo list. -/
def pushNewFact (proof : Expr) (generation : Nat := 0) : GoalM Unit := do
  let prop ← inferType proof
  pushNewFact' prop proof generation

end Lean.Meta.Grind
