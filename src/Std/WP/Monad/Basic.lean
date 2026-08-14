/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Std.WP.Basic
universe u v w z
@[expose] public section

set_option linter.missingDocs true

open Lean.Order Std.WP

/-!
# The Weakest Precondition Interpretation of a Monad

`WPMonad m Pred EPred` carries a `WP (m α) α Pred EPred` interpretation for every result type `α`,
together with soundness of that interpretation for `pure` and `bind`. An instance supplies the
`WP` interpretation of `m α` at low priority, so a program type with a bespoke interpretation keeps
its own.
-/

namespace Std.WP

variable {m : Type u → Type z}

/-- Weakest precondition monad: a monad `m` whose weakest precondition interpretation is sound for
`pure` and `bind`. The interpretation for every result type is carried as the `toWP` field; an
instance exposes it as a `WP (m α) …` interpretation. -/
class WPMonad (m : Type u → Type v) (Pred : outParam (Type w)) (EPred : outParam (Type w'))
    [Monad m] [Assertion Pred] [Assertion EPred] extends LawfulMonad m where
  /-- The weakest precondition interpretation of `m` at every result type. -/
  toWP : ∀ α, WP (m α) α Pred EPred
  /-- Soundness of `pure`: the postcondition applied to `x` implies the weakest precondition of
  `pure x`. -/
  pure_le_wp_pure (x : α) (post : α → Pred) (epost : EPred) :
    post x ⊑ (toWP α).wp (pure (f := m) x) post epost
  /-- Soundness of `bind`: composing weakest preconditions is at least as strong as the weakest
  precondition of `>>=`. -/
  bind_le_wp_bind (x : m α) (f : α → m β) (post : β → Pred) (epost : EPred) :
    (toWP α).wp x (fun a => (toWP β).wp (f a) post epost) epost ⊑ (toWP β).wp (x >>= f) post epost

/-- A monadic `WP` interpretation is sourced from the monad's `WPMonad` instance. Low priority so a
program type with a bespoke `WP` instance (e.g. a non-monadic one) is preferred. -/
instance (priority := low)
    {m : Type u → Type v} {Pred : Type w} {EPred : Type w'} {α : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [inst : WPMonad m Pred EPred] :
    WP (m α) α Pred EPred :=
  inst.toWP α

/-!
## Derived WPMonad Lemmas

One-directional consequences of the `WPMonad` axioms for `pure`, `bind`, `map`, and `seq`.
-/

namespace WPMonad

variable [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]

/-- Soundness of `Functor.map`: mapping `f` over `x` preserves the WP. -/
theorem map_le_wp_map (f : α → β) (x : m α) :
  ∀ post epost, wp x (fun a => post (f a)) epost ⊑ wp (f <$> x) post epost := by
  intro post epost
  rw [← bind_pure_comp]
  apply PartialOrder.rel_trans; rotate_left
  exact bind_le_wp_bind x (pure <| f ·) post epost
  apply WP.wp_consequence
  intro a; exact pure_le_wp_pure (f a) post epost

/-- Variant of `map_le_wp_map` with an explicit postcondition equality hypothesis. -/
theorem map_le_wp_map' (f : α → β) (x : m α) :
  ∀ post post' epost (_ : post = fun a => post' (f a)),
    wp x post epost ⊑ wp (f <$> x) post' epost := by
  intro post post' epost h
  subst h
  apply map_le_wp_map

/-- Soundness of `Seq.seq`: sequencing `f <*> x` preserves the WP. -/
theorem seq_le_wp_seq (f : m (α → β)) (x : m α) :
  ∀ post epost,
    wp f (fun g => wp x (fun a => post (g a)) epost) epost ⊑
      wp (f <*> x) post epost := by
  intro post epost
  rw [← bind_map]
  apply PartialOrder.rel_trans _ (bind_le_wp_bind f (fun g => g <$> x) post epost)
  apply WP.wp_consequence; intro g; exact map_le_wp_map g x post epost

end WPMonad

end Std.WP
