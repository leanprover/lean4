/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Grind.Lemmas
public import Lean.Meta.Tactic.Assert
public import Lean.Meta.Tactic.Simp.Main
public import Lean.Meta.Tactic.Grind.Util
public import Lean.Meta.Tactic.Grind.Types
public import Lean.Meta.Tactic.Grind.MatchDiscrOnly
public import Lean.Meta.Tactic.Grind.MarkNestedSubsingletons
public import Lean.Meta.Tactic.Grind.Canon

public section

namespace Lean.Meta.Grind

/-- Simplifies the given expression using the `grind` simprocs and normalization theorems. -/
def simpCore (e : Expr) : GrindM Simp.Result := do profileitM Exception "grind simp" (← getOptions) do
  let simp ← modifyGet fun s => (s.simp, { s with simp := {} })
  let ctx := (← readThe Context).simp
  let m := (← get).scState.map
  let skipIfInShareCommon : Simp.Simproc := fun e => if m.contains { expr := e } then return .done { expr := e } else return .continue
  let methods := (← readThe Context).simpMethods
  let methods := { methods with pre := skipIfInShareCommon >> methods.pre }
  let (r, simp) ← Simp.mainCore e ctx simp (methods := methods)
  modify fun s => { s with simp }
  return r

/-- Similar to `simpCore`, but uses `dsimp`. -/
def dsimpCore (e : Expr) : GrindM Expr := do profileitM Exception "grind dsimp" (← getOptions) do
  let simp ← modifyGet fun s => (s.simp, { s with simp := {} })
  let ctx := (← readThe Context).simp
  let (r, simp) ← Simp.dsimpMainCore e ctx simp (methods := (← readThe Context).simpMethods)
  modify fun s => { s with simp }
  return r

/--
Unfolds all `reducible` declarations occurring in `e`.
Similar to `unfoldReducible`, but uses `inShareCommon` as an extra filter
-/
def unfoldReducible' (e : Expr) : GrindM Expr := do
  if !(← isUnfoldReducibleTarget e) then return e
  let pre (e : Expr) : GrindM TransformStep := do
    if (← inShareCommon e) then return .done e
    let .const declName _ := e.getAppFn | return .continue
    unless (← isReducible declName) do return .continue
    if isGrindGadget declName then return .continue
    let some v ← unfoldDefinition? e | return .continue
    return .visit v
  Core.transform e (pre := pre)

/--
Preprocesses `e` using `grind` normalization theorems and simprocs,
and then applies several other preprocessing steps.
-/
def preprocess (e : Expr) : GoalM Simp.Result := do
  let e ← instantiateMVars e
  let r ← simpCore e
  let e' := r.expr
  let e' ← unfoldReducible' e'
  let e' ← abstractNestedProofs e'
  let e' ← markNestedSubsingletons e'
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
  trace[grind.debug.pushNewFact] "{prop} ==> {prop'}"
  modify fun s => { s with newFacts := s.newFacts.push <| .fact prop' proof generation }


/-- Infers the type of the proof, preprocess it, and adds it to todo list. -/
def pushNewFact (proof : Expr) (generation : Nat := 0) : GoalM Unit := do
  let prop ← inferType proof
  trace[grind.debug.pushNewFact] "{prop}"
  pushNewFact' prop proof generation

end Lean.Meta.Grind
