/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Internal.Do.WP.Basic
public import Std.Internal.Do.Order.Instances
universe u v w z
@[expose] public section

set_option linter.missingDocs true

open Lean.Order Std.Internal.Do

namespace Std.Internal.Do

/-- `wp x` is sub-conjunctive: a meet of postconditions maps below the `wp` of their meet. A
healthiness condition of the `WP` interpretation for the individual program `x`; it holds for the base
interpretations and lifts through the transformers. -/
class WPConjunctive {Prog : Type u} {Value : outParam (Type v)} {Pred : outParam (Type w)}
    {EPred : outParam (Type z)} [Assertion Pred] [Assertion EPred] [WP Prog Value Pred EPred]
    (x : Prog) : Prop where
  /-- A meet of postconditions maps below the `wp` of their meet. -/
  wp_meet_wp_le (Q₁ Q₂ : Value → Pred) (E₁ E₂ : EPred) :
    wp x Q₁ E₁ ⊓ wp x Q₂ E₂ ⊑ wp x (Q₁ ⊓ Q₂) (E₁ ⊓ E₂)

/-- An `Id` program is conjunctive: its `wp` is evaluation at the result. -/
instance Id.instWPConjunctive {α : Type u} (x : Id α) : WPConjunctive x where
  wp_meet_wp_le Q₁ Q₂ E₁ E₂ := by simp only [wp, WP.wpTrans, meet_apply]; exact PartialOrder.rel_refl

/-- An `Option` program is conjunctive: its `wp` is evaluation at the result. -/
instance Option.instWPConjunctive {α : Type u} (x : Option α) : WPConjunctive x where
  wp_meet_wp_le Q₁ Q₂ E₁ E₂ := by
    cases x <;>
      simp only [meet_apply, wp, WP.wpTrans, Option.elim] <;>
      first | exact PartialOrder.rel_refl | exact meet_le_left _ _

/-- An `Except ε` program is conjunctive: its `wp` is evaluation at the result. -/
instance Except.instWPConjunctive {ε α : Type u} (x : Except ε α) : WPConjunctive x where
  wp_meet_wp_le Q₁ Q₂ E₁ E₂ := by
    cases x <;>
      simp only [meet_apply, wp, WP.wpTrans, EPost.Cons.head_meet] <;>
      exact PartialOrder.rel_refl

/-- An `EStateM` program is conjunctive: its `wp` is evaluation at the result. -/
instance EStateM.instWPConjunctive {ε σ α : Type} (x : EStateM ε σ α) : WPConjunctive x where
  wp_meet_wp_le Q₁ Q₂ E₁ E₂ := by
    intro s
    simp only [meet_apply, wp, WP.wpTrans]
    cases x s <;> first | exact PartialOrder.rel_refl | exact meet_le_left _ _

/-- A `StateT` program lifts conjunctivity from its base monad. -/
instance StateT.instWPConjunctive {m : Type u → Type v} {σ : Type u} {Pred : Type w} {EPred : Type z}
    {α : Type u} [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    (x : StateT σ m α) [base : ∀ s, WPConjunctive (x.run s)] : WPConjunctive x where
  wp_meet_wp_le Q₁ Q₂ E₁ E₂ := by
    intro s
    simp only [meet_apply, StateT.wp_apply_eq]
    refine PartialOrder.rel_trans
      ((base s).wp_meet_wp_le (fun p => Q₁ p.1 p.2) (fun p => Q₂ p.1 p.2) E₁ E₂)
      (WP.wp_consequence _ _ _ _ ?_)
    intro p
    simp only [meet_apply]
    exact PartialOrder.rel_refl

/-- A `ReaderT` program lifts conjunctivity from its base monad. -/
instance ReaderT.instWPConjunctive {m : Type u → Type v} {ρ : Type u} {Pred : Type w} {EPred : Type z}
    {α : Type u} [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    (x : ReaderT ρ m α) [base : ∀ r, WPConjunctive (x.run r)] : WPConjunctive x where
  wp_meet_wp_le Q₁ Q₂ E₁ E₂ := by
    intro r
    simp only [meet_apply, ReaderT.wp_apply_eq]
    refine PartialOrder.rel_trans
      ((base r).wp_meet_wp_le (fun a => Q₁ a r) (fun a => Q₂ a r) E₁ E₂)
      (WP.wp_consequence _ _ _ _ ?_)
    intro a
    simp only [meet_apply]
    exact PartialOrder.rel_refl

/-- An `OptionT` program lifts conjunctivity from its base monad. -/
instance OptionT.instWPConjunctive {m : Type u → Type v} {Pred : Type u} {EPred : Type z}
    {α : Type u} [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    (x : OptionT m α) [base : WPConjunctive x.run] : WPConjunctive x where
  wp_meet_wp_le Q₁ Q₂ E₁ E₂ := by
    simp only [OptionT.wp_apply_eq, EPost.Cons.tail_meet]
    refine PartialOrder.rel_trans
      (base.wp_meet_wp_le (E₁.pushOption Q₁) (E₂.pushOption Q₂) E₁.tail E₂.tail)
      (WP.wp_consequence _ _ _ _ ?_)
    intro o
    cases o <;>
      simp only [meet_apply, EPost.Cons.pushOption, EPost.Cons.head_meet] <;>
      exact PartialOrder.rel_refl

/-- An `ExceptT` program lifts conjunctivity from its base monad. -/
instance ExceptT.instWPConjunctive {m : Type u → Type v} {ε α : Type u} {Pred : Type w}
    {EPred : Type z} [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    (x : ExceptT ε m α) [base : WPConjunctive x.run] : WPConjunctive x where
  wp_meet_wp_le Q₁ Q₂ E₁ E₂ := by
    simp only [ExceptT.wp_apply_eq, EPost.Cons.tail_meet]
    refine PartialOrder.rel_trans
      (base.wp_meet_wp_le (E₁.pushExcept Q₁) (E₂.pushExcept Q₂) E₁.tail E₂.tail)
      (WP.wp_consequence _ _ _ _ ?_)
    intro e
    cases e <;>
      simp only [meet_apply, EPost.Cons.pushExcept, EPost.Cons.head_meet] <;>
      exact PartialOrder.rel_refl

end Std.Internal.Do
