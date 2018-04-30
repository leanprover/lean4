/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad

The sum type, aka disjoint union.
-/
prelude
import init.core

notation α ⊕ β := sum α β

universes u v

variables {α : Type u} {β : Type v}

instance sum.inhabited_left [h : inhabited α] : inhabited (α ⊕ β) :=
⟨sum.inl (default α)⟩

instance sum.inhabited_right [h : inhabited β] : inhabited (α ⊕ β) :=
⟨sum.inr (default β)⟩

instance {α : Type u} {β : Type v} [decidable_eq α] [decidable_eq β] : decidable_eq (α ⊕ β)
| (sum.inl a) (sum.inl b) := if h : a = b then is_true (h ▸ rfl)
                             else is_false (λ h', sum.no_confusion h' (λ h', absurd h' h))
| (sum.inr a) (sum.inr b) := if h : a = b then is_true (h ▸ rfl)
                             else is_false (λ h', sum.no_confusion h' (λ h', absurd h' h))
| (sum.inr a) (sum.inl b) := is_false (λ h, sum.no_confusion h)
| (sum.inl a) (sum.inr b) := is_false (λ h, sum.no_confusion h)
