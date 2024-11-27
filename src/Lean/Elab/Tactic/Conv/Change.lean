/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Change
import Lean.Elab.Tactic.Conv.Basic
import Lean.Elab.Tactic.Change

namespace Lean.Elab.Tactic.Conv
open Meta

@[builtin_tactic Lean.Parser.Tactic.Conv.change] def evalChange : Tactic := fun stx => do
  match stx with
  | `(conv| change $e) => withMainContext do
    let lhs ← getLhs
    let mvarCounterSaved := (← getMCtx).mvarCounter
    let lhs' ← elabChange lhs e
    logUnassignedAndAbort (← filterOldMVars (← getMVars lhs') mvarCounterSaved)
    changeLhs lhs'
  | _ => throwUnsupportedSyntax

@[builtin_tactic Lean.Parser.Tactic.Conv.changeMatching] def evalChangeMatching : Tactic
  | `(conv| change_matching $p:term with $t:term) => do
    let lhs ← getLhs
    let mvarCounterSaved := (← getMCtx).mvarCounter
    let lhs' ← elabChangeMatching lhs p t
    logUnassignedAndAbort (← filterOldMVars (← getMVars lhs') mvarCounterSaved)
    changeLhs lhs'
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic.Conv
