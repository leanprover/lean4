/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Mario Carneiro
-/
prelude
import Lean.Elab.ElabRules
import Lean.Meta.Tactic.TryThis

namespace Lean.Elab.Tactic.ShowTerm
open Lean Elab Term Tactic Meta.Tactic.TryThis Parser.Tactic

@[builtin_tactic showTerm] def evalShowTerm : Tactic := fun stx =>
  match stx with
  | `(tactic| show_term%$tk $t) => withMainContext do
    let g ← getMainGoal
    evalTactic t
    addExactSuggestion tk (← instantiateMVars (mkMVar g)).headBeta (origSpan? := ← getRef)
  | _ => throwUnsupportedSyntax

/-- Implementation of `show_term` term elaborator. -/
@[builtin_term_elab showTermElabImpl] def elabShowTerm : TermElab
  | `(show_term_elab%$tk $t), ty => do
    let e ← Term.elabTermEnsuringType t ty
    Term.synthesizeSyntheticMVarsNoPostponing
    addTermSuggestion tk (← instantiateMVars e).headBeta (origSpan? := ← getRef)
    pure e
  | _, _ => throwUnsupportedSyntax

end Lean.Elab.Tactic.ShowTerm
