/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
module

prelude
public import Lean.Elab.Tactic.Meta

public section

open Lean Meta Elab Tactic Parser.Tactic

@[builtin_tactic as_aux_lemma]
def elabAsAuxLemma : Lean.Elab.Tactic.Tactic
| `(tactic| as_aux_lemma => $s) => withMainContext do
  let mvarId ← getMainGoal
  let mvars ← Tactic.run mvarId (evalTactic s)
  unless mvars.isEmpty do
    throwError "Cannot abstract term into auxiliary lemma because there are open goals."
  let e ← instantiateMVars (mkMVar mvarId)
  let e ← mkAuxTheorem (← mvarId.getType) e
  mvarId.assign e
| _ => throwError "Invalid as_aux_lemma syntax"
