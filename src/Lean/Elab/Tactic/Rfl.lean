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

This extends the `rfl` tactic so that it works on reflexive relations other than `=`,
provided the reflexivity lemma has been marked as `@[refl]`.
-/

namespace Lean.Elab.Tactic.Rfl

/--
This tactic applies to a goal whose target has the form `x ~ x`, where `~` is a reflexive
relation, that is, a relation which has a reflexive lemma tagged with the attribute [refl].
-/
@[builtin_tactic Lean.Parser.Tactic.applyRfl] def evalApplyRfl : Tactic := fun stx =>
  match stx with
  | `(tactic| apply_rfl) => withMainContext do liftMetaFinishingTactic (·.applyRfl)
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic.Rfl
