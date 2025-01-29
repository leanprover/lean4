/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Init.Tactics
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Meta
import Lean.MetavarContext
import Lean.Meta.Closure

open Lean Meta Elab Tactic Parser.Tactic

@[builtin_tactic as_aux_lemma]
def elabAsAuxLemma : Lean.Elab.Tactic.Tactic
| `(tactic| as_aux_lemma => $s) =>
  liftMetaTactic fun mvarId => do
    let (mvars, _) ← runTactic mvarId s
    unless mvars.isEmpty do
      throwError "Left-over goals, cannot abstract"
    let e ← instantiateMVars (mkMVar mvarId)
    let e ← mkAuxTheorem (`Std.DTreeMap.Internal.Impl ++ (← mkFreshUserName `test)) (← mvarId.getType) e
    mvarId.assign e
    return []
| _ => throwError "Invalid as_aux_lemma syntax"
