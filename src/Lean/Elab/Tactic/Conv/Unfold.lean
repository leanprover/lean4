/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Elab.Tactic.Unfold
import Lean.Elab.Tactic.Conv.Simp

namespace Lean.Elab.Tactic.Conv
open Meta

@[builtin_tactic Lean.Parser.Tactic.Conv.unfold] def evalUnfold : Tactic := fun stx => withMainContext do
  for declNameId in stx[1].getArgs do
    withRef declNameId do
      let e ← withoutRecover <| elabTermForApply declNameId (mayPostpone := false)
      match e with
      | .const declName _ =>
        applySimpResult (← unfold (← getLhs) declName)
      | .fvar declFVarId =>
        unless ← declFVarId.isLetVar do
          throwError "conv tactic 'unfold' failed, local variable '{Expr.fvar declFVarId}' has no definition"
        let lhs ← instantiateMVars (← getLhs)
        changeLhs (← Meta.zetaDeltaFVars lhs #[declFVarId])
      | _ => throwError "conv tactic 'unfold' failed, expression {e} is not a global or local constant"

end Lean.Elab.Tactic.Conv
