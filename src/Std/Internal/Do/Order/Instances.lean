/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Internal.Do.Order.Lemmas

public section

/-!
# Algebraic typeclass instances for `CompleteLattice`

The order `⊑` is reflexive, transitive and antisymmetric, and meet and join are commutative,
associative and idempotent monoid operations with units `⊤` and `⊥`. These instances expose that
structure to the generic algebra in `Std` (`Std.Commutative`, `Std.Associative`, `Trans`, ...).
-/

namespace Std.Internal.Do.CompleteLattice

open Lean.Order PartialOrder

instance [CompleteLattice l] : Std.Refl (α := l) (· ⊑ ·) := ⟨fun _ => rel_refl⟩
instance [CompleteLattice l] : Trans (· ⊑ · : l → l → Prop) (· ⊑ ·) (· ⊑ ·) := ⟨rel_trans⟩
instance [CompleteLattice l] : Std.Antisymm (α := l) (· ⊑ ·) := ⟨fun _ _ => rel_antisymm⟩

instance [CompleteLattice l] : Std.Commutative (α := l) (· ⊓ ·) := ⟨fun _ _ => meet_comm⟩
instance [CompleteLattice l] : Std.Commutative (α := l) (· ⊔ ·) := ⟨fun _ _ => join_comm⟩
instance [CompleteLattice l] : Std.Associative (α := l) (· ⊓ ·) := ⟨fun _ _ _ => meet_assoc⟩
instance [CompleteLattice l] : Std.Associative (α := l) (· ⊔ ·) := ⟨fun _ _ _ => join_assoc⟩
instance [CompleteLattice l] : Std.IdempotentOp (α := l) (· ⊓ ·) := ⟨fun _ => meet_self⟩
instance [CompleteLattice l] : Std.IdempotentOp (α := l) (· ⊔ ·) := ⟨fun _ => join_self⟩
instance [CompleteLattice l] : Std.LeftIdentity (· ⊓ ·) (⊤ : l) where
instance [CompleteLattice l] : Std.RightIdentity (· ⊓ ·) (⊤ : l) where
instance [CompleteLattice l] : Std.LeftIdentity (· ⊔ ·) (⊥ : l) where
instance [CompleteLattice l] : Std.RightIdentity (· ⊔ ·) (⊥ : l) where
instance [CompleteLattice l] : Std.LawfulIdentity (· ⊓ ·) (⊤ : l) where
  left_id _ := top_meet
  right_id _ := meet_top
instance [CompleteLattice l] : Std.LawfulIdentity (· ⊔ ·) (⊥ : l) where
  left_id _ := bot_join
  right_id _ := join_bot

end Std.Internal.Do.CompleteLattice
