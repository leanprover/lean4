/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Std.WP.Basic
universe u v w w' z
@[expose] public section

set_option linter.missingDocs true

open Lean.Order Std.WP

/-!
# The Weakest Precondition Interpretation of a Monad

`MonadicWP m Pred EPosts` is a `WP` interpretation of the programs `m α` for every result type `α`.
A low-priority instance derives `WP (m α) α Pred EPosts` from it.

The laws relate `wp` to `pure` and `bind` of `m`:

* `MonadicWP.IsLaxMonadMorphism m`: `wp` is sound for `pure` and `bind`. `WP.trans` is then a lax
  monad morphism.
* `MonadicWP.IsMonadMorphism m`: `wp` computes `pure` and `bind`. `WP.trans` is then a monad
  morphism.
-/

namespace Std.WP

/-- The `WP` interpretation of all programs `m α` of a monad `m`. -/
class MonadicWP (m : Type u → Type v) (Pred : outParam (Type w)) (EPosts : outParam (Type w'))
    [PartialOrder Pred] [PartialOrder EPosts] where
  /-- The interpretation of the programs `m α`. -/
  toWP : ∀ α, WP (m α) α Pred EPosts

instance (priority := low) {m : Type u → Type v} {Pred : Type w} {EPosts : Type w'}
    [PartialOrder Pred] [PartialOrder EPosts] [inst : MonadicWP m Pred EPosts] {α : Type u} :
    WP (m α) α Pred EPosts :=
  inst.toWP α

/-- `wp` is sound for `pure` and `bind`. `WP.trans` is then a lax monad morphism from `m` to
`PredTrans Pred EPosts`. -/
class MonadicWP.IsLaxMonadMorphism (m : Type u → Type v) {Pred : outParam (Type w)}
    {EPosts : outParam (Type w')} [Monad m] [PartialOrder Pred] [PartialOrder EPosts]
    [MonadicWP m Pred EPosts] : Prop where
  /-- Soundness of `pure`: the postcondition applied to `x` implies the weakest precondition of
  `pure x`. -/
  pure_le_wp_pure {α : Type u} (x : α) (post : α → Pred) (eposts : EPosts) :
    post x ⊑ wp (pure x : m α) post eposts
  /-- Soundness of `bind`: composing weakest preconditions is at least as strong as the weakest
  precondition of `>>=`. -/
  bind_le_wp_bind {α β : Type u} (x : m α) (f : α → m β) (post : β → Pred) (eposts : EPosts) :
    wp x (fun a => wp (f a) post eposts) eposts ⊑ wp (x >>= f) post eposts

/-- `wp` computes `pure` and `bind`: `WP.trans` is a monad morphism to `PredTrans Pred EPosts`. -/
class MonadicWP.IsMonadMorphism (m : Type u → Type v) {Pred : outParam (Type w)}
    {EPosts : outParam (Type w')} [Monad m] [PartialOrder Pred] [PartialOrder EPosts]
    [MonadicWP m Pred EPosts] : Prop extends MonadicWP.IsLaxMonadMorphism m where
  /-- `wp (pure x) post` is `post x`. -/
  wp_pure_eq {α : Type u} (x : α) (post : α → Pred) (eposts : EPosts) :
    wp (pure x : m α) post eposts = post x
  /-- `wp (x >>= f)` is `wp x` of `wp (f a)`. -/
  wp_bind_eq {α β : Type u} (x : m α) (f : α → m β) (post : β → Pred) (eposts : EPosts) :
    wp (x >>= f) post eposts = wp x (fun a => wp (f a) post eposts) eposts
  pure_le_wp_pure x post eposts := PartialOrder.rel_of_eq (wp_pure_eq x post eposts).symm
  bind_le_wp_bind x f post eposts := PartialOrder.rel_of_eq (wp_bind_eq x f post eposts).symm

namespace MonadicWP

variable {m : Type u → Type v} {Pred : Type w} {EPosts : Type w'} [PartialOrder Pred]
  [PartialOrder EPosts] [MonadicWP m Pred EPosts]

/-!
## Derived Lemmas

The laws at the level of `wp`.
-/

section Strict

variable [Monad m] [IsMonadMorphism m]

theorem wp_pure_eq {α : Type u} (a : α) (post : α → Pred) (eposts : EPosts) :
    wp (pure a : m α) post eposts = post a :=
  IsMonadMorphism.wp_pure_eq a post eposts

theorem wp_bind_eq {α β : Type u} (x : m α) (f : α → m β) (post : β → Pred) (eposts : EPosts) :
    wp (x >>= f) post eposts = wp x (fun a => wp (f a) post eposts) eposts :=
  IsMonadMorphism.wp_bind_eq x f post eposts

end Strict

section Lax

theorem pure_le_wp_pure [Monad m] [MonadicWP.IsLaxMonadMorphism m]
    {α : Type u} (x : α) (post : α → Pred) (eposts : EPosts) :
    post x ⊑ wp (pure (f := m) x) post eposts :=
  IsLaxMonadMorphism.pure_le_wp_pure x post eposts

theorem bind_le_wp_bind [Monad m] [MonadicWP.IsLaxMonadMorphism m]
    {α β : Type u} (x : m α) (f : α → m β) (post : β → Pred)
    (eposts : EPosts) :
    wp x (fun a => wp (f a) post eposts) eposts ⊑ wp (x >>= f) post eposts :=
  IsLaxMonadMorphism.bind_le_wp_bind x f post eposts

/-- Soundness of `Functor.map`: mapping `f` over `x` preserves the WP. -/
theorem map_le_wp_map [Monad m] [LawfulMonad m]
    [MonadicWP.IsLaxMonadMorphism m] {α β : Type u} (f : α → β) (x : m α) :
  ∀ post eposts, wp x (fun a => post (f a)) eposts ⊑ wp (f <$> x) post eposts := by
  intro post eposts
  rw [← bind_pure_comp]
  apply PartialOrder.rel_trans; rotate_left
  exact bind_le_wp_bind x (pure <| f ·) post eposts
  apply WP.wp_monotone_post
  intro a; exact pure_le_wp_pure (f a) post eposts

/-- Soundness of `Seq.seq`: sequencing `f <*> x` preserves the WP. -/
theorem seq_le_wp_seq [Monad m] [LawfulMonad m]
    [MonadicWP.IsLaxMonadMorphism m] {α β : Type u} (f : m (α → β)) (x : m α) :
  ∀ post eposts,
    wp f (fun g => wp x (fun a => post (g a)) eposts) eposts ⊑
      wp (f <*> x) post eposts := by
  intro post eposts
  rw [← bind_map]
  apply PartialOrder.rel_trans _ (bind_le_wp_bind f (fun g => g <$> x) post eposts)
  apply WP.wp_monotone_post; intro g; exact map_le_wp_map g x post eposts

end Lax

end MonadicWP

section Deprecated

set_option linter.missingDocs false

@[deprecated "use `[MonadicWP m Pred EPosts] [MonadicWP.IsLaxMonadMorphism m]`" (since := "2026-11-18")]
abbrev WPMonad (m : Type u → Type v) (Pred : Type w) (EPosts : Type w') [PartialOrder Pred]
    [PartialOrder EPosts] := MonadicWP m Pred EPosts

@[deprecated MonadicWP.bind_le_wp_bind (since := "2026-11-18")]
abbrev WPMonad.bind_le_wp_bind := @MonadicWP.bind_le_wp_bind

@[deprecated MonadicWP.map_le_wp_map (since := "2026-11-18")]
abbrev WPMonad.map_le_wp_map := @MonadicWP.map_le_wp_map

@[deprecated MonadicWP.pure_le_wp_pure (since := "2026-11-18")]
abbrev WPMonad.pure_le_wp_pure := @MonadicWP.pure_le_wp_pure

@[deprecated MonadicWP.seq_le_wp_seq (since := "2026-11-18")]
abbrev WPMonad.seq_le_wp_seq := @MonadicWP.seq_le_wp_seq

end Deprecated

end Std.WP
