/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Internal.Do.WP.Basic
public import Std.Internal.Do.WP.Conjunctive
public import Std.Internal.Do.Order.Lemmas
universe u v w z
@[expose] public section

set_option linter.missingDocs true

open Lean.Order Std.Internal.Do

namespace Std.Internal.Do

variable {Prog : Type u} {Value : Type v} {Pred : Type w} {EPred : Type z}
  [Assertion Pred] [Assertion EPred] [WP Prog Value Pred EPred]

/--
`x` preserves the frame `F`: `F` commutes into the postcondition of `wp x` for every postcondition.
The side condition discharged when framing a spec for `x`.
-/
def WP.Preserving (x : Prog) (F : Pred) : Prop :=
  ∀ (Q : Value → Pred) (E : EPred), F ⊓ wp x Q E ⊑ wp x (fun a => F ⊓ Q a) E

/-- A meet frame `(F ⊓ ·)` is preserved by `x` when `x` preserves `F` and `wp x` is conjunctive:
the side condition reduces to the preservation triple `F ⊑ wp x (fun _ => F)`. -/
theorem WP.Preserving.of_meet {Prog : Type u} {Value : Type v} {Pred : Type w} {EPred : Type z}
    [Assertion Pred] [Assertion EPred] [WP Prog Value Pred EPred]
    [WPConjunctive Prog Value Pred EPred] {x : Prog} {F : Pred} (h : ∀ E, F ⊑ wp x (fun _ => F) E) :
    WP.Preserving x F := by
  intro Q E
  refine PartialOrder.rel_trans (y := wp x (fun _ => F) E ⊓ wp x Q E) ?_ ?_
  · exact le_meet _ _ _ (PartialOrder.rel_trans (meet_le_left _ _) (h E)) (meet_le_right _ _)
  · refine PartialOrder.rel_trans (WPConjunctive.wp_meet_wp_le x (fun _ => F) Q E)
      (WP.wp_consequence _ _ _ _ ?_)
    intro a
    simp only [meet_apply]
    exact PartialOrder.rel_refl

/-- When `x` preserves `F`, meeting with `F` commutes into the postcondition of `wp x`. -/
theorem meet_wp_le_wp_meet {x : Prog} {F : Pred} {Q : Value → Pred} {E : EPred}
    (hframe : WP.Preserving x F) :
    F ⊓ wp x Q E ⊑ wp x (fun r => F ⊓ Q r) E :=
  hframe Q E

/-- The framed spec `vcgen` applies for `x`: residualizing the postcondition through `F ⇨ ·` makes
`F ⊓ wp x (F ⇨ Q)` a precondition for `wp x Q`. -/
theorem meet_wp_imp_le_wp [Frame Pred] {x : Prog} {F : Pred} {Q : Value → Pred} {E : EPred}
    (hframe : WP.Preserving x F) :
    F ⊓ wp x (fun a => F ⇨ Q a) E ⊑ wp x Q E :=
  PartialOrder.rel_trans (meet_wp_le_wp_meet hframe)
    (WP.wp_consequence x _ Q E (fun _ => CompleteLattice.meet_himp_le))
