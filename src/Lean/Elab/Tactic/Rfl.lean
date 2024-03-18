/-
Copyright (c) 2022 Newell Jensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Newell Jensen, Thomas Murrills
-/
prelude
import Lean.Meta.Tactic.Rfl
import Lean.Elab.Tactic.Basic

/-!
# `rfl` tactic extension for reflexive relations

This implements the extensible `rfl`, which works on any reflexive relation,
provided the reflexivity lemma has been marked as `@[refl]`.
-/

namespace Lean.Elab.Tactic.Rfl

@[builtin_tactic Lean.Parser.Tactic.rfl] def evalRfl : Tactic := fun stx =>
  match stx with
  | `(tactic| apply_rfl) => withMainContext do liftMetaFinishingTactic (·.applyRfl)
  | _ => throwUnsupportedSyntax

-- Temporary until after stage0 update
@[builtin_tactic Lean.Parser.Tactic.applyRfl] def evalApplyRfl : Tactic := fun stx =>
  match stx with
  | `(tactic| apply_rfl) => withMainContext do liftMetaFinishingTactic (·.applyRfl)
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic.Rfl
