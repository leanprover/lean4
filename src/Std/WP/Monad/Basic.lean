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

Two classes express how lawful `wp` is for `pure` and `bind` of `m`:

* `MonadicWP.IsLaxMonadMorphism m`: `WP.trans` is a lax monad morphism, so `wp` is sound for
  `pure` and `bind`.
* `MonadicWP.IsMonadMorphism m`: `WP.trans` is a monad morphism, so `wp` computes `pure` and
  `bind`.
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

/-- `pure` and `bind` of the transformers in `PredTrans Pred EPosts` lie below the transformers of
`pure` and `bind`. `WP.trans` is then a lax monad morphism from `m` to `PredTrans Pred EPosts`. -/
class MonadicWP.IsLaxMonadMorphism (m : Type u → Type v) {Pred : outParam (Type w)}
    {EPosts : outParam (Type w')} [Monad m] [PartialOrder Pred] [PartialOrder EPosts]
    [MonadicWP m Pred EPosts] : Prop where
  /-- `pure a` lies below the transformer of `pure a`. -/
  pure_le {α : Type u} (a : α) :
    (pure a : PredTrans Pred EPosts α) ⊑ WP.trans (pure a : m α)
  /-- The `bind` of the transformers lies below the transformer of `x >>= f`. -/
  bind_le {α β : Type u} (x : m α) (f : α → m β) :
    (WP.trans x >>= fun a => WP.trans (f a)) ⊑ WP.trans (x >>= f)

/-- `WP.trans` is a monad morphism from `m` to `PredTrans Pred EPosts`: it commutes with `pure` and
`bind`. -/
class MonadicWP.IsMonadMorphism (m : Type u → Type v) {Pred : outParam (Type w)}
    {EPosts : outParam (Type w')} [Monad m] [PartialOrder Pred] [PartialOrder EPosts]
    [MonadicWP m Pred EPosts] : Prop extends MonadicWP.IsLaxMonadMorphism m where
  /-- The transformer of `pure a` is `pure a`. -/
  trans_pure {α : Type u} (a : α) :
    WP.trans (pure a : m α) = (pure a : PredTrans Pred EPosts α)
  /-- The transformer of `x >>= f` is the `bind` of the transformers. -/
  trans_bind {α β : Type u} (x : m α) (f : α → m β) :
    WP.trans (x >>= f) = WP.trans x >>= fun a => WP.trans (f a)
  pure_le a := PartialOrder.rel_of_eq (trans_pure a).symm
  bind_le x f := PartialOrder.rel_of_eq (trans_bind x f).symm

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
    wp (pure a : m α) post eposts = post a := by
  rw [← WP.trans_apply_eq (pure a : m α), IsMonadMorphism.trans_pure (m := m) a,
    PredTrans.apply_Pure_pure]

theorem wp_bind_eq {α β : Type u} (x : m α) (f : α → m β) (post : β → Pred) (eposts : EPosts) :
    wp (x >>= f) post eposts = wp x (fun a => wp (f a) post eposts) eposts := by
  rw [← WP.trans_apply_eq (x >>= f), IsMonadMorphism.trans_bind x f, PredTrans.apply_Bind_bind]
  simp only [WP.trans_apply_eq]

end Strict

section Lax

theorem le_wp_pure [Monad m] [MonadicWP.IsLaxMonadMorphism m]
    {α : Type u} (x : α) (post : α → Pred) (eposts : EPosts) :
    post x ⊑ wp (pure (f := m) x) post eposts := by
  simpa only [PredTrans.apply_Pure_pure, WP.trans_apply_eq] using
    IsLaxMonadMorphism.pure_le (m := m) x post eposts

theorem wp_wp_le_wp_bind [Monad m] [MonadicWP.IsLaxMonadMorphism m]
    {α β : Type u} (x : m α) (f : α → m β) (post : β → Pred)
    (eposts : EPosts) :
    wp x (fun a => wp (f a) post eposts) eposts ⊑ wp (x >>= f) post eposts := by
  simpa only [PredTrans.apply_Bind_bind, WP.trans_apply_eq] using
    IsLaxMonadMorphism.bind_le x f post eposts

/-- Soundness of `Functor.map`: mapping `f` over `x` preserves the WP. -/
theorem wp_le_wp_map [Monad m] [LawfulMonad m]
    [MonadicWP.IsLaxMonadMorphism m] {α β : Type u} (f : α → β) (x : m α) :
  ∀ post eposts, wp x (fun a => post (f a)) eposts ⊑ wp (f <$> x) post eposts := by
  intro post eposts
  rw [← bind_pure_comp]
  apply PartialOrder.rel_trans; rotate_left
  exact wp_wp_le_wp_bind x (pure <| f ·) post eposts
  apply WP.wp_monotone_post
  intro a; exact le_wp_pure (f a) post eposts

/-- Soundness of `Seq.seq`: sequencing `f <*> x` preserves the WP. -/
theorem wp_wp_le_wp_seq [Monad m] [LawfulMonad m]
    [MonadicWP.IsLaxMonadMorphism m] {α β : Type u} (f : m (α → β)) (x : m α) :
  ∀ post eposts,
    wp f (fun g => wp x (fun a => post (g a)) eposts) eposts ⊑
      wp (f <*> x) post eposts := by
  intro post eposts
  rw [← bind_map]
  apply PartialOrder.rel_trans _ (wp_wp_le_wp_bind f (fun g => g <$> x) post eposts)
  apply WP.wp_monotone_post; intro g; exact wp_le_wp_map g x post eposts

end Lax

end MonadicWP

section Deprecated

set_option linter.missingDocs false

@[deprecated "use `[MonadicWP m Pred EPosts] [MonadicWP.IsLaxMonadMorphism m]`" (since := "2026-11-18")]
abbrev WPMonad (m : Type u → Type v) (Pred : Type w) (EPosts : Type w') [PartialOrder Pred]
    [PartialOrder EPosts] := MonadicWP m Pred EPosts

@[deprecated MonadicWP.wp_wp_le_wp_bind (since := "2026-11-18")]
abbrev WPMonad.bind_le_wp_bind := @MonadicWP.wp_wp_le_wp_bind

@[deprecated MonadicWP.wp_le_wp_map (since := "2026-11-18")]
abbrev WPMonad.map_le_wp_map := @MonadicWP.wp_le_wp_map

@[deprecated MonadicWP.le_wp_pure (since := "2026-11-18")]
abbrev WPMonad.pure_le_wp_pure := @MonadicWP.le_wp_pure

@[deprecated MonadicWP.wp_wp_le_wp_seq (since := "2026-11-18")]
abbrev WPMonad.seq_le_wp_seq := @MonadicWP.wp_wp_le_wp_seq

end Deprecated

end Std.WP
