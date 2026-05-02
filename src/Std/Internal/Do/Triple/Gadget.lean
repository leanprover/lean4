/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Std.Internal.Do.Triple.Basic
public import Std.Internal.Do.Frame

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
theorem Spec.assertGadget (name : Name) (as : Pred) [Frame Pred] :
  Triple (m := m) (as ⊓ (as ⇨ post ⟨⟩)) (Std.Internal.Do.assertGadget name as) post epost := by
  simpa [Std.Internal.Do.assertGadget] using
    (Triple.pure (m := m) (pre := as ⊓ himp as (post ⟨⟩)) (post := post) (epost := epost)
      (a := ⟨⟩) (h := himp_sound (a := as) (b := post ⟨⟩)))

end Std.Internal.Do

end -- public section
