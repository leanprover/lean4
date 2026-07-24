/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Std.Internal.Do.Triple.Basic
public import Std.Internal.Do.Order.Heyting

@[expose] public section

set_option linter.missingDocs true

open Lean Order Std.Internal.Do Lean.Order

namespace Std.Internal.Do

universe u v
variable {m : Type u → Type v} {Pred : Type u} {EPred : Type u} [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]

set_option linter.unusedVariables false in

/-- A no-op computation used as a verification gadget to inject assertions into the program.

The `name` parameter is used by VCGen to name the introduced hypothesis. The `as` parameter
is the assertion to be checked. At runtime, `assertGadget` is simply `pure ⟨⟩`. -/
def assertGadget [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] (name : Name) (as : Pred) : m PUnit := pure ⟨⟩

/-- Specification for `assertGadget`: the precondition requires both the assertion `as` and
the Heyting implication `as ⇨ post ⟨⟩`, ensuring the assertion holds and the postcondition
follows from it. -/
theorem Spec.assertGadget (name : Name) (as : Pred) [∀ a : Pred, PreservesSup (meet a)] :
  Triple (Std.Internal.Do.assertGadget (m := m) name as) (as ⊓ (as ⇨ post ⟨⟩)) post epost := by
  simpa [Std.Internal.Do.assertGadget] using
    (Triple.pure (m := m) (pre := as ⊓ (as ⇨ post ⟨⟩)) (post := post) (epost := epost)
      (a := ⟨⟩) (h := meet_himp_le))

set_option linter.unusedVariables false in
/-- The identity on `x`, tagging it with the join-point function `fv` so `vcgen +jp` can recognize
the continuation `x` of a shared join point. -/
def jpGadget.{ua, ub} {α : Sort ua} {β : Sort ub} (fv : β) (x : α) : α := x

end Std.Internal.Do

end -- public section
