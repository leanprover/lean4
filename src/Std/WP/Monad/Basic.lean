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

`MonadicWP m Pred EPosts` carries a `WP (m α) α Pred EPosts` interpretation for every result type
`α`. An instance supplies the `WP` interpretation of `m α` at low priority, so a program type with
a bespoke interpretation keeps its own.

The laws relate `WP.trans : m α → PredTrans Pred EPosts α` to the monad structure of
`PredTrans Pred EPosts`:

* `MonadicWP.IsLaxMonadMorphism m`: `pure` and `bind` of the transformers lie below the
  transformers of `pure` and `bind`, so `wp` is sound for `pure` and `bind`. Together with
  `MonadicWP.IsMonotone`, `WP.trans` is then a lax monad morphism into the monotone transformers.
* `MonadicWP.IsMonadMorphism m`: `WP.trans` is a monad morphism. It commutes with `pure` and
  `bind`, so `wp` computes `pure` and `bind`.
-/

namespace Std.WP

/-- The weakest precondition interpretation of the programs `m α` of a monad `m`, for every result
type `α`. -/
class MonadicWP (m : Type u → Type v) (Pred : outParam (Type w)) (EPosts : outParam (Type w'))
    [Monad m] where
  /-- The weakest precondition interpretation of `m` at every result type. -/
  toWP : ∀ α, WP (m α) α Pred EPosts

/-- A monadic `WP` interpretation is sourced from the monad's `MonadicWP` instance. Low priority
so a program type with a bespoke `WP` instance (e.g. a non-monadic one) is preferred. -/
instance (priority := low)
    {m : Type u → Type v} {Pred : Type w} {EPosts : Type w'} {α : Type u}
    [Monad m] [inst : MonadicWP m Pred EPosts] :
    WP (m α) α Pred EPosts :=
  inst.toWP α

/-- The transformer of every program of the monad `m` is monotone. -/
abbrev MonadicWP.IsMonotone (m : Type u → Type v) {Pred : Type w} {EPosts : Type w'} [Monad m]
    [MonadicWP m Pred EPosts] [PartialOrder Pred] [PartialOrder EPosts] : Prop :=
  ∀ α, WP.IsMonotone (m α)

/-- `WP.trans` is a monad morphism from `m` to `PredTrans Pred EPosts`: it commutes with `pure` and
`bind`. -/
class MonadicWP.IsMonadMorphism (m : Type u → Type v) {Pred : outParam (Type w)}
    {EPosts : outParam (Type w')} [Monad m] [MonadicWP m Pred EPosts] : Prop where
  /-- The transformer of `pure a` is `pure a`. -/
  trans_pure {α : Type u} (a : α) :
    WP.trans (pure a : m α) = (PredTrans.pure a : PredTrans Pred EPosts α)
  /-- The transformer of `x >>= f` is the `bind` of the transformers. -/
  trans_bind {α β : Type u} (x : m α) (f : α → m β) :
    WP.trans (x >>= f) = WP.trans x >>= fun a => WP.trans (f a)

/-- `pure` and `bind` of the transformers in `PredTrans Pred EPosts` lie below the transformers of
`pure` and `bind`. Together with `MonadicWP.IsMonotone`, `WP.trans` is then a lax monad morphism
from `m` to the monotone transformers. -/
class MonadicWP.IsLaxMonadMorphism (m : Type u → Type v) {Pred : outParam (Type w)}
    {EPosts : outParam (Type w')} [Monad m] [MonadicWP m Pred EPosts]
    [PartialOrder Pred] [PartialOrder EPosts] : Prop where
  /-- `pure a` lies below the transformer of `pure a`. -/
  pure_le {α : Type u} (a : α) :
    (PredTrans.pure a : PredTrans Pred EPosts α) ⊑ WP.trans (pure a : m α)
  /-- The `bind` of the transformers lies below the transformer of `x >>= f`. -/
  bind_le {α β : Type u} (x : m α) (f : α → m β) :
    (WP.trans x >>= fun a => WP.trans (f a)) ⊑ WP.trans (x >>= f)

namespace MonadicWP

variable {m : Type u → Type v} {Pred : Type w} {EPosts : Type w'} [Monad m] [MonadicWP m Pred EPosts]

instance [IsMonadMorphism m] [PartialOrder Pred] [PartialOrder EPosts] :
    IsLaxMonadMorphism m where
  pure_le a := PartialOrder.rel_of_eq (IsMonadMorphism.trans_pure a).symm
  bind_le x f := PartialOrder.rel_of_eq (IsMonadMorphism.trans_bind x f).symm

/-!
## Derived Lemmas

The laws at the level of `wp`.
-/

section Strict

variable [IsMonadMorphism m]

theorem wp_pure_eq {α : Type u} (a : α) (post : α → Pred) (eposts : EPosts) :
    wp (pure a : m α) post eposts = post a :=
  congrArg (PredTrans.apply · post eposts) (IsMonadMorphism.trans_pure (m := m) a)

theorem wp_bind_eq {α β : Type u} (x : m α) (f : α → m β) (post : β → Pred) (eposts : EPosts) :
    wp (x >>= f) post eposts = wp x (fun a => wp (f a) post eposts) eposts :=
  congrArg (PredTrans.apply · post eposts) (IsMonadMorphism.trans_bind x f)

end Strict

section Lax

variable [PartialOrder Pred] [PartialOrder EPosts] [IsLaxMonadMorphism m]

theorem pure_le_wp_pure {α : Type u} (x : α) (post : α → Pred) (eposts : EPosts) :
    post x ⊑ wp (pure (f := m) x) post eposts :=
  IsLaxMonadMorphism.pure_le x post eposts

theorem bind_le_wp_bind {α β : Type u} (x : m α) (f : α → m β) (post : β → Pred)
    (eposts : EPosts) :
    wp x (fun a => wp (f a) post eposts) eposts ⊑ wp (x >>= f) post eposts :=
  IsLaxMonadMorphism.bind_le x f post eposts

/-- Soundness of `Functor.map`: mapping `f` over `x` preserves the WP. -/
theorem map_le_wp_map [LawfulMonad m] [MonadicWP.IsMonotone m] {α β : Type u} (f : α → β) (x : m α) :
  ∀ post eposts, wp x (fun a => post (f a)) eposts ⊑ wp (f <$> x) post eposts := by
  intro post eposts
  rw [← bind_pure_comp]
  apply PartialOrder.rel_trans; rotate_left
  exact bind_le_wp_bind x (pure <| f ·) post eposts
  apply WP.wp_monotone_post
  intro a; exact pure_le_wp_pure (f a) post eposts

/-- Soundness of `Seq.seq`: sequencing `f <*> x` preserves the WP. -/
theorem seq_le_wp_seq [LawfulMonad m] [MonadicWP.IsMonotone m] {α β : Type u} (f : m (α → β)) (x : m α) :
  ∀ post eposts,
    wp f (fun g => wp x (fun a => post (g a)) eposts) eposts ⊑
      wp (f <*> x) post eposts := by
  intro post eposts
  rw [← bind_map]
  apply PartialOrder.rel_trans _ (bind_le_wp_bind f (fun g => g <$> x) post eposts)
  apply WP.wp_monotone_post; intro g; exact map_le_wp_map g x post eposts

end Lax

end MonadicWP

end Std.WP
