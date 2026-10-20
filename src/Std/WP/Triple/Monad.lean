/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Std.WP.Triple.Basic
public import Std.WP.Monad.Basic
@[expose] public section

set_option linter.missingDocs true

open Lean.Order

/-!
# Hoare triples for the monadic combinators

The rules that build a `Triple` for `pure`, `>>=`, `<$>` and `<*>` from triples for the parts.
-/

namespace Std.WP

universe u v w w'
variable {Pred : Type w} {EPosts : Type w'}

namespace Triple

variable {m : Type v → Type u} [Monad m] [Assertion Pred] [Assertion EPosts]
  [WPMonad m Pred EPosts]

theorem pure (a : α) (h : pre ⊑ post a) :
    Triple (pure (f := m) a) pre post eposts :=
  ⟨PartialOrder.rel_trans h (WPMonad.pure_le_wp_pure a post eposts)⟩

theorem bind (x : m α) (f : α → m β)
    (mid : α → Pred)
    (hx : Triple x pre mid eposts)
    (hf : ∀ a, Triple (f a) (mid a) post eposts) :
    Triple (x >>= f) pre post eposts :=
  ⟨PartialOrder.rel_trans hx.le_wp
    (PartialOrder.rel_trans
      (WP.wp_monotone_post (fun a => (hf a).le_wp))
      (WPMonad.bind_le_wp_bind x f post eposts))⟩

theorem map [LawfulMonad m] (f : α → β) (x : m α)
    (h : Triple x pre (fun a => post (f a)) eposts) :
    Triple (f <$> x) pre post eposts :=
  ⟨PartialOrder.rel_trans h.le_wp (WPMonad.map_le_wp_map f x post eposts)⟩

theorem seq [LawfulMonad m] (x : m (α → β)) (y : m α)
    (h : Triple x pre (fun f => wp y (fun a => post (f a)) eposts) eposts) :
    Triple (x <*> y) pre post eposts :=
  ⟨PartialOrder.rel_trans h.le_wp (WPMonad.seq_le_wp_seq x y post eposts)⟩

end Triple

end Std.WP
