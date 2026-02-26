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

@[builtin_tactic Lean.Parser.Tactic.cbv] def evalCbv : Tactic := fun stx =>
  match stx with
  | `(tactic| cbv) => withMainContext do
    if cbv.warning.get (← getOptions) then
      logWarningAt stx "The `cbv` tactic is experimental and still under development. Avoid using it in production projects"
    liftMetaTactic fun mvar => do
      match (← cbvGoal mvar) with
      | .none => return []
      | .some newGoal => return [newGoal]
  | _ => throwUnsupportedSyntax

@[builtin_tactic Lean.Parser.Tactic.decide_cbv] def evalDecideCbv : Tactic := fun stx =>
  match stx with
  | `(tactic| decide_cbv) => withMainContext do
    if cbv.warning.get (← getOptions) then
      logWarningAt stx "The `decide_cbv` tactic is experimental and still under development. Avoid using it in production projects"
    liftMetaFinishingTactic fun mvar => do
      let [mvar'] ← mvar.applyConst ``of_decide_eq_true | throwError "Could not apply `of_decide_eq_true`"
      cbvDecideGoal mvar'
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic.Cbv
