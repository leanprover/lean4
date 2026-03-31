/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Do.Triple.SpecLemmas
import Std.Tactic.Do.Syntax

set_option linter.missingDocs true

@[expose] public section

namespace Std.Do

/-!
# Specification theorem for `Repeat` loops

This file contains the `@[spec]` theorem for `forIn` over `Lean.Repeat`, which enables
verified reasoning about `repeat`/`while` loops using `mvcgen`.
-/

set_option mvcgen.warning false

section

variable {β : Type u} {m : Type u → Type v} {ps : PostShape.{u}}
variable [Monad m] [MonadAttach m] [WeaklyLawfulMonadAttach m] [WPMonad m ps]

/--
Specification for `forIn` over a `Lean.Repeat` value.
Takes a variant (termination measure), an invariant, a proof that the variant decreases,
and a proof that each step preserves the invariant.
-/
@[spec]
theorem Spec.forIn_repeat
    {l : _root_.Lean.Repeat} {init : β} {f : Unit → β → m (ForInStep β)}
    (_variant : RepeatVariant β)
    (inv : RepeatInvariant β ps)
    (hwf : WellFounded (_root_.Lean.Repeat.IsPlausibleStep f))
    (step : ∀ b,
      Triple
        (f () b)
        (inv.1 (.repeat b))
        (fun r => match r with
          | .yield b' => inv.1 (.repeat b')
          | .done b' => inv.1 (.done b'), inv.2)) :
    Triple (forIn l init f) (inv.1 (.repeat init)) (fun b => inv.1 (.done b), inv.2) := by
  change Triple (_root_.Lean.Repeat.forIn l init f) _ _
  simp only [_root_.Lean.Repeat.forIn, WellFounded.extrinsicFix_eq_fix hwf]
  induction hwf.apply init with
  | intro b hacc ih =>
  rw [WellFounded.fix_eq]
  mvcgen [step, ih]
  rename_i stp
  apply SPred.forall_intro
  intro _
  cases stp <;> mvcgen [ih]

end

end Std.Do
