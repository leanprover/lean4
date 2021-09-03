/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Conv.Basic

namespace Lean.Elab.Tactic.Conv
open Meta

@[builtinTactic Lean.Parser.Tactic.Conv.change] def evalChange : Tactic := fun stx => do
  match stx with
  | `(conv| change $e) => do
    let lhs ← getLhs
    let mvarCounterSaved := (← getMCtx).mvarCounter
    let r ← elabTermEnsuringType e (← inferType lhs)
    logUnassignedAndAbort (← filterOldMVars (← getMVars r) mvarCounterSaved)
    unless (← isDefEqGuarded r lhs) do
      throwError "invalid 'change' conv tactic, term{indentExpr r}\nis not definitionally equal to current left-hand-side{indentExpr lhs}"
    changeLhs r
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic.Conv
