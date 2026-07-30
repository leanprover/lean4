/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Lean.Meta.Tactic.Cbv
public import Lean.Meta.Tactic

public section

namespace Lean.Elab.Tactic.Cbv

open Lean.Meta.Tactic.Cbv

@[builtin_tactic Lean.Parser.Tactic.cbv] def evalCbv : Tactic := fun stx => withMainContext do
  if cbv.warning.get (← getOptions) then
    logWarningAt stx "The `cbv` usage warning option is enabled. Disable it by setting `set_option cbv.warning false`."
  liftMetaTactic fun mvar => do
    match (← cbvGoal mvar) with
    | .none => return []
    | .some newGoal => return [newGoal]

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
