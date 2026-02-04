/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/

module

prelude
public import Lean.Meta.Tactic.Cbv
public import Lean.Elab.Tactic.Conv.Basic

section

namespace Lean.Elab.Tactic.Conv
open Lean.Meta.Tactic.Cbv


@[builtin_tactic Lean.Parser.Tactic.Conv.cbv] public def evalCbv : Tactic := fun stx => withMainContext do
  if cbv.warning.get (← getOptions) then
    logWarningAt stx "The `cbv` tactic is experimental and still under development. Avoid using it in production projects"
  let lhs ← getLhs
  let evalResult ← cbvEntry lhs
  match evalResult with
  | .rfl .. => return ()
  | .step e' proof _ =>
    updateLhs e' proof

end Lean.Elab.Tactic.Conv
