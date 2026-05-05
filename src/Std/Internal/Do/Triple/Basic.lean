/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Std.Internal.Do.WP
@[expose] public section

set_option linter.missingDocs true

open Lean.Order

/-!
# Hoare triples

Hoare triples form the basis for compositional functional correctness proofs about monadic programs.

As usual, `Triple pre x post epost` holds iff the precondition `pre` entails the weakest
precondition `wp x post epost` of `x : m α` for the postcondition `post` and error
postcondition `epost`.
It is thus defined in terms of an instance `WPMonad m Pred EPred`.
-/

namespace Std.Internal.Do

universe u v
variable {m : Type u → Type v} {Pred : Type u} {EPred : Type u}

/-- A Hoare triple for reasoning about monadic programs. A Hoare triple `Triple pre x post epost`
is a *specification* for `x`: if assertion `pre` holds before `x`, then postcondition `post` holds
after running `x` (and `epost` handles any errors). -/
structure Triple [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] (pre : Pred) (x : m α) (post : α → Pred) (epost : EPred) : Prop where
  /-- Construct a triple from a weakest precondition entailment. -/
  intro ::
  /-- The weakest precondition entailment witnessing the triple. -/
  (hwp : pre ⊑ wp x post epost)

/-- Hoare triple notation without exception postcondition (defaults to `⊥`). -/
scoped notation:60 "⦃ " pre " ⦄ " x " ⦃ " post " ⦄" => Triple pre x post ⊥
/-- Hoare triple notation with a binder for the return value. -/
scoped notation:60 "⦃ " pre " ⦄ " x " ⦃ " v ", " post " ⦄" => Triple pre x (fun v => post) ⊥
namespace Triple

variable [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]

theorem iff {x : m α} {pre : Pred} {post : α → Pred} {epost : EPred} :
    Triple pre x post epost ↔ (pre ⊑ wp x post epost) :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

theorem iff_conseq {x : m α} {pre : Pred} {post : α → Pred} {epost : EPred} :
    Triple pre x post epost ↔
    (∀ pre' post', (pre' ⊑ pre) → (post ⊑ post') → pre' ⊑ wp x post' epost) := by
  constructor
  · intro ⟨h⟩ pre' post' hpre hpost
    exact PartialOrder.rel_trans hpre (PartialOrder.rel_trans h (WPMonad.wp_consequence x _ _ epost hpost))
  · intro h
    exact ⟨h _ _ PartialOrder.rel_refl (fun _ => PartialOrder.rel_refl)⟩

theorem entails_wp_of_pre_post {x : m α} {pre pre' : Pred} {post post' : α → Pred} {epost : EPred}
    (h : Triple pre' x post' epost) (hpre : pre ⊑ pre') (hpost : post' ⊑ post) :
    pre ⊑ wp x post epost :=
  iff_conseq.mp h _ _ hpre hpost

theorem entails_wp_of_pre {x : m α} {pre pre' : Pred} {post : α → Pred} {epost : EPred}
    (h : Triple pre' x post epost) (hpre : pre ⊑ pre') :
    pre ⊑ wp x post epost :=
  iff_conseq.mp h _ _ hpre (fun _ => PartialOrder.rel_refl)

theorem entails_wp_of_post {x : m α} {pre : Pred} {post post' : α → Pred} {epost : EPred}
    (h : Triple pre x post' epost) (hpost : post' ⊑ post) :
    pre ⊑ wp x post epost :=
  iff_conseq.mp h _ _ PartialOrder.rel_refl hpost

theorem pure (a : α) (h : pre ⊑ post a) :
    Triple pre (pure (f := m) a) post epost :=
  iff.mpr (PartialOrder.rel_trans h (WPMonad.wp_pure a post epost))

theorem bind (x : m α) (f : α → m β)
    (mid : α → Pred)
    (hx : Triple pre x mid epost)
    (hf : ∀ a, Triple (mid a) (f a) post epost) :
    Triple pre (x >>= f) post epost := by
  apply iff.mpr
  apply PartialOrder.rel_trans (iff.mp hx)
  apply PartialOrder.rel_trans (WPMonad.wp_consequence x mid (fun a => wp (f a) post epost) epost
    (fun a => iff.mp (hf a)))
  exact WPMonad.wp_bind x f post epost

end Triple

end Std.Internal.Do
