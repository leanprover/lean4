/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Internal.Do.WP.Basic
public import Std.Internal.Do.Order.Lemmas
universe u v w z
@[expose] public section

set_option linter.missingDocs true

open Lean.Order Std.Internal.Do

namespace Std.Internal.Do

/-- `wp x` is sub-conjunctive: a meet of postconditions maps below the `wp` of their meet. A
healthiness condition of the `WP` interpretation; it holds for the base interpretations and lifts
through the transformers. -/
class WPConjunctive (Prog : Type u) (Value : outParam (Type v)) (Pred : outParam (Type w))
    (EPred : outParam (Type z)) [Assertion Pred] [Assertion EPred] [WP Prog Value Pred EPred] where
  /-- A meet of postconditions maps below the `wp` of their meet. -/
  wp_meet_wp_le (x : Prog) (Q₁ Q₂ : Value → Pred) (E : EPred) :
    wp x Q₁ E ⊓ wp x Q₂ E ⊑ wp x (Q₁ ⊓ Q₂) E

/-- `Id` is conjunctive: its `wp` is evaluation at the result. -/
instance Id.instWPConjunctive {α : Type u} : WPConjunctive (Id α) α Prop EPost.Nil where
  wp_meet_wp_le x Q₁ Q₂ E := by simp only [wp, WP.wpTrans, meet_apply]; exact PartialOrder.rel_refl

/-- `Option` is conjunctive: its `wp` is evaluation at the result. -/
instance Option.instWPConjunctive {α : Type u} : WPConjunctive (Option α) α Prop Prop where
  wp_meet_wp_le x Q₁ Q₂ E := by
    cases x <;>
      simp only [meet_apply, wp, WP.wpTrans, Option.elim] <;>
      first | exact PartialOrder.rel_refl | exact meet_le_left _ _

/-- `Except ε` is conjunctive: its `wp` is evaluation at the result. -/
instance Except.instWPConjunctive {ε α : Type u} :
    WPConjunctive (Except ε α) α Prop EPost⟨ε → Prop⟩ where
  wp_meet_wp_le x Q₁ Q₂ E := by
    cases x <;>
      simp only [meet_apply, wp, WP.wpTrans] <;>
      first | exact PartialOrder.rel_refl | exact meet_le_left _ _

/-- `EStateM` is conjunctive: its `wp` is evaluation at the result. -/
instance EStateM.instWPConjunctive {ε σ α : Type} :
    WPConjunctive (EStateM ε σ α) α (σ → Prop) (ε → σ → Prop) where
  wp_meet_wp_le x Q₁ Q₂ E := by
    intro s
    simp only [meet_apply, wp, WP.wpTrans]
    cases x s <;> first | exact PartialOrder.rel_refl | exact meet_le_left _ _

/-- `StateT` lifts conjunctivity from its base monad. -/
instance StateT.instWPConjunctive {m : Type u → Type v} {σ : Type u} {Pred : Type w} {EPred : Type z}
    {α : Type u} [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [WPConjunctive (m (α × σ)) (α × σ) Pred EPred] :
    WPConjunctive (StateT σ m α) α (σ → Pred) EPred where
  wp_meet_wp_le x Q₁ Q₂ E := by
    intro s
    simp only [meet_apply, StateT.wp_apply_eq]
    refine PartialOrder.rel_trans
      (WPConjunctive.wp_meet_wp_le (x.run s) (fun p => Q₁ p.1 p.2) (fun p => Q₂ p.1 p.2) E)
      (WP.wp_consequence _ _ _ _ ?_)
    intro p
    simp only [meet_apply]
    exact PartialOrder.rel_refl

/-- `ReaderT` lifts conjunctivity from its base monad. -/
instance ReaderT.instWPConjunctive {m : Type u → Type v} {ρ : Type u} {Pred : Type w} {EPred : Type z}
    {α : Type u} [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [WPConjunctive (m α) α Pred EPred] :
    WPConjunctive (ReaderT ρ m α) α (ρ → Pred) EPred where
  wp_meet_wp_le x Q₁ Q₂ E := by
    intro r
    simp only [meet_apply, ReaderT.wp_apply_eq]
    refine PartialOrder.rel_trans
      (WPConjunctive.wp_meet_wp_le (x.run r) (fun a => Q₁ a r) (fun a => Q₂ a r) E)
      (WP.wp_consequence _ _ _ _ ?_)
    intro a
    simp only [meet_apply]
    exact PartialOrder.rel_refl

/-- `OptionT` lifts conjunctivity from its base monad. -/
instance OptionT.instWPConjunctive {m : Type u → Type v} {Pred : Type u} {EPred : Type z}
    {α : Type u} [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [WPConjunctive (m (Option α)) (Option α) Pred EPred] :
    WPConjunctive (OptionT m α) α Pred (EPost.Cons Pred EPred) where
  wp_meet_wp_le x Q₁ Q₂ E := by
    simp only [OptionT.wp_apply_eq]
    refine PartialOrder.rel_trans
      (WPConjunctive.wp_meet_wp_le x.run (E.pushOption Q₁) (E.pushOption Q₂) E.tail)
      (WP.wp_consequence _ _ _ _ ?_)
    intro o
    cases o <;>
      simp only [meet_apply, EPost.Cons.pushOption] <;>
      first | exact PartialOrder.rel_refl | exact meet_le_left _ _

/-- `ExceptT` lifts conjunctivity from its base monad. -/
instance ExceptT.instWPConjunctive {m : Type u → Type v} {ε α : Type u} {Pred : Type w}
    {EPred : Type z} [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    [WPConjunctive (m (Except ε α)) (Except ε α) Pred EPred] :
    WPConjunctive (ExceptT ε m α) α Pred (EPost.Cons (ε → Pred) EPred) where
  wp_meet_wp_le x Q₁ Q₂ E := by
    simp only [ExceptT.wp_apply_eq]
    refine PartialOrder.rel_trans
      (WPConjunctive.wp_meet_wp_le x.run (E.pushExcept Q₁) (E.pushExcept Q₂) E.tail)
      (WP.wp_consequence _ _ _ _ ?_)
    intro e
    cases e <;>
      simp only [meet_apply, EPost.Cons.pushExcept] <;>
      first | exact PartialOrder.rel_refl | exact meet_le_left _ _

end Std.Internal.Do
