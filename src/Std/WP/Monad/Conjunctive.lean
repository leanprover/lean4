/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.WP.Conjunctive
public import Std.WP.Monad.Instances
universe u v w z
@[expose] public section

set_option linter.missingDocs true

open Lean.Order Std.WP

/-!
# Conjunctivity of the monadic weakest preconditions

`PredTrans.IsConjunctive` instances for the programs of the base monads and of the monad
transformers. Each transformer instance lifts conjunctivity from the programs of its base monad
through the combinator that builds its transformer.
-/

namespace Std.WP

/-- An `Id` program is conjunctive: its `wp` is evaluation at the result. -/
instance {α : Type u} (x : Id α) : WP.IsConjunctive x where
  meet_apply_le Q₁ Q₂ E₁ E₂ := by simp only [WP.trans, meet_apply]; exact PartialOrder.rel_refl

/-- An `Option` program is conjunctive: its `wp` is evaluation at the result. -/
instance {α : Type u} (x : Option α) : WP.IsConjunctive x where
  meet_apply_le Q₁ Q₂ E₁ E₂ := by
    cases x <;>
      simp only [meet_apply, WP.trans, pushOption] <;>
      exact PartialOrder.rel_refl

/-- An `Except ε` program is conjunctive: its `wp` is evaluation at the result. -/
instance {ε α : Type u} (x : Except ε α) : WP.IsConjunctive x where
  meet_apply_le Q₁ Q₂ E₁ E₂ := by
    cases x <;>
      simp only [meet_apply, WP.trans, pushExcept] <;>
      exact PartialOrder.rel_refl

/-- An `EStateM` program is conjunctive: its `wp` is evaluation at the result. -/
instance {ε σ α : Type} (x : EStateM ε σ α) : WP.IsConjunctive x where
  meet_apply_le Q₁ Q₂ E₁ E₂ := by
    intro s
    simp only [meet_apply, WP.trans]
    cases x s <;> first | exact PartialOrder.rel_refl | exact meet_le_left _ _

/-- The transformer of every program of the monad `m` is conjunctive. -/
abbrev MonadicWP.IsConjunctive (m : Type u → Type v) {Pred : Type w} {EPosts : Type z} [Monad m]
    [MonadicWP m Pred EPosts] [CompleteLattice Pred] [CompleteLattice EPosts] : Prop :=
  ∀ α (x : m α), WP.IsConjunctive x

variable {m : Type u → Type v} {Pred : Type w} {EPosts : Type z}
  [CompleteLattice Pred] [CompleteLattice EPosts]

/-- A `StateT` program lifts conjunctivity from its base monad. -/
instance {σ α : Type u} [WP (m (α × σ)) (α × σ) Pred EPosts] [WP.IsMonotone (m (α × σ))]
    (x : StateT σ m α) [∀ s, WP.IsConjunctive (x.run s)] : WP.IsConjunctive x :=
  inferInstanceAs (PredTrans.pushArg (WP.trans <| x.run ·)).IsConjunctive

/-- A `ReaderT` program lifts conjunctivity from its base monad. -/
instance {ρ α : Type u} [WP (m α) α Pred EPosts] [WP.IsMonotone (m α)]
    (x : ReaderT ρ m α) [base : ∀ r, WP.IsConjunctive (x.run r)] :
    WP.IsConjunctive x where
  meet_apply_le Q₁ Q₂ E₁ E₂ := by
    intro r
    simp only [meet_apply]
    refine PartialOrder.rel_trans
      (PredTrans.IsConjunctive.meet_apply_le (pt := WP.trans (x.run r))
        (fun a => Q₁ a r) (fun a => Q₂ a r) E₁ E₂)
      (WP.wp_monotone_post ?_)
    intro a
    simp only [meet_apply]
    exact PartialOrder.rel_refl

/-- An `OptionT` program lifts conjunctivity from its base monad. -/
instance {m : Type u → Type v} {α Pred : Type u} {EPosts : Type z} [CompleteLattice Pred]
    [CompleteLattice EPosts] [WP (m (Option α)) (Option α) Pred EPosts]
    [WP.IsMonotone (m (Option α))] (x : OptionT m α) [WP.IsConjunctive x.run] :
    WP.IsConjunctive x :=
  inferInstanceAs (PredTrans.pushOptionT (WP.trans x.run)).IsConjunctive

/-- An `ExceptT` program lifts conjunctivity from its base monad. -/
instance {ε α : Type u} [WP (m (Except ε α)) (Except ε α) Pred EPosts]
    [WP.IsMonotone (m (Except ε α))] (x : ExceptT ε m α) [WP.IsConjunctive x.run] :
    WP.IsConjunctive x :=
  inferInstanceAs (PredTrans.pushExceptT (WP.trans x.run)).IsConjunctive

end Std.WP
