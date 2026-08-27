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
variable {Pred : Type w} {EPred : Type w'}

namespace Triple

variable {m : Type v → Type u} [Monad m] [Assertion Pred] [Assertion EPred]
  [WPMonad m Pred EPred]

theorem pure (a : α) (h : pre ⊑ post a) :
    Triple (pure (f := m) a) pre post epost :=
  ⟨PartialOrder.rel_trans h (WPMonad.pure_le_wp_pure a post epost)⟩

theorem bind (x : m α) (f : α → m β)
    (mid : α → Pred)
    (hx : Triple x pre mid epost)
    (hf : ∀ a, Triple (f a) (mid a) post epost) :
    Triple (x >>= f) pre post epost :=
  ⟨PartialOrder.rel_trans hx.le_wp
    (PartialOrder.rel_trans
      (WP.wp_consequence x mid (fun a => wp (f a) post epost) epost (fun a => (hf a).le_wp))
      (WPMonad.bind_le_wp_bind x f post epost))⟩

theorem map [LawfulMonad m] (f : α → β) (x : m α)
    (h : Triple x pre (fun a => post (f a)) epost) :
    Triple (f <$> x) pre post epost :=
  ⟨PartialOrder.rel_trans h.le_wp (WPMonad.map_le_wp_map f x post epost)⟩

theorem seq [LawfulMonad m] (x : m (α → β)) (y : m α)
    (h : Triple x pre (fun f => wp y (fun a => post (f a)) epost) epost) :
    Triple (x <*> y) pre post epost :=
  ⟨PartialOrder.rel_trans h.le_wp (WPMonad.seq_le_wp_seq x y post epost)⟩

end Triple

end Std.WP
