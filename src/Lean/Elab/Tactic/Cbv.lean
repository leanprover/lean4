/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Lean.Meta.Tactic.Cbv
public import Lean.Meta.Tactic
public import Lean.Elab.Tactic.Location

public section

namespace Lean.Elab.Tactic.Cbv

open Lean.Meta.Tactic.Cbv

/-- Reduces the type of hypothesis `fvarId` using `cbv`, in its own `SymM` session. -/
def cbvLocalDecl (fvarId : FVarId) : TacticM Unit :=
  liftMetaTactic fun mvarId => do
    match (← cbvHyp mvarId fvarId) with
    | .none => return []
    | .some newGoal => return [newGoal]

/-- Reduces the goal target using `cbv`, in its own `SymM` session. -/
def cbvTarget : TacticM Unit :=
  liftMetaTactic fun mvarId => do
    match (← cbvGoal mvarId) with
    | .none => return []
    | .some newGoal => return [newGoal]

@[builtin_tactic Lean.Parser.Tactic.cbv] def evalCbv : Tactic := fun stx => withMainContext do
  if cbv.warning.get (← getOptions) then
    logWarningAt stx "The `cbv` usage warning option is enabled. Disable it by setting `set_option cbv.warning false`."
  let loc := expandOptLocation stx[1]
  let wildcardHyps? ← match loc with
    | .wildcard => some <$> (← getMainGoal).getNondepPropHyps
    | _ => pure none
  withLocation loc
    (atLocal := fun fvarId => do
      if let some wildcardHyps := wildcardHyps? then
        unless wildcardHyps.contains fvarId do return
      cbvLocalDecl fvarId)
    (atTarget := cbvTarget)
    (failed := fun _ => throwError "`cbv` failed")

@[builtin_tactic Lean.Parser.Tactic.decide_cbv] def evalDecideCbv : Tactic := fun stx =>
  match stx with
  | `(tactic| decide_cbv) => withMainContext do
    if cbv.warning.get (← getOptions) then
      logWarningAt stx "The `decide_cbv` usage warning option is enabled. Disable it by setting `set_option cbv.warning false`."
    liftMetaFinishingTactic fun mvar => do
      let [mvar'] ← mvar.applyConst ``of_decide_eq_true | throwError "Could not apply `of_decide_eq_true`"
      cbvDecideGoal mvar'
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic.Cbv
