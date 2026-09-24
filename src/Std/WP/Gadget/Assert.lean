/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Std.WP.Triple.Monad
public import Std.Internal.Order.Heyting
public import Std.Internal.Order.Automation

@[expose] public section

set_option linter.missingDocs true

open Lean Order Std.WP Lean.Order

namespace Std.WP

universe u v
variable {m : Type u → Type v} {Pred : Type u} {EPosts : Type u} [Monad m] [Assertion Pred] [Assertion EPosts] [WPMonad m Pred EPosts]

namespace Gadget

set_option linter.unusedVariables false in

/-- A no-op computation used as a verification gadget to inject assertions into the program.

The `as` parameter is the assertion to be checked. At runtime, `assertGadget` is simply
`pure ⟨⟩`. -/
def assertGadget [Monad m] [Assertion Pred] [Assertion EPosts] [WPMonad m Pred EPosts] (as : Pred) : m PUnit := pure ⟨⟩

end Gadget

open Gadget

/-- Specification for `assertGadget`: the precondition requires both the assertion `as` and
the Heyting implication `as ⇨ post ⟨⟩`, ensuring the assertion holds and the postcondition
follows from it. -/
@[spec]
theorem Spec.assertGadget (as : Pred) [Heyting Pred] :
  Triple (Gadget.assertGadget (m := m) as) (as ⊓ (as ⇨ post ⟨⟩)) post eposts := by
  simpa [Gadget.assertGadget] using
    (Triple.pure (m := m) (pre := as ⊓ (as ⇨ post ⟨⟩)) (post := post) (eposts := eposts)
      (a := ⟨⟩) (h := meet_himp_le))

end Std.WP

end -- public section
