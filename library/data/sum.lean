/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: data.sum
Authors: Leonardo de Moura, Jeremy Avigad

The sum type, aka disjoint union.
-/
import logic.connectives
open inhabited eq.ops

notation A ⊎ B := sum A B
notation A + B := sum A B

namespace sum
  namespace low_precedence_plus
    reserve infixr `+`:25  -- conflicts with notation for addition
    infixr `+` := sum
  end low_precedence_plus

  variables {A B : Type}

  definition inl_ne_inr (a : A) (b : B) : inl a ≠ inr b :=
  assume H, no_confusion H

  definition inr_ne_inl (b : B) (a : A) : inr b ≠ inl a :=
  assume H, no_confusion H

  definition inl_inj {a₁ a₂ : A} : intro_left B a₁ = intro_left B a₂ → a₁ = a₂ :=
  assume H, no_confusion H (λe, e)

  definition inr_inj {b₁ b₂ : B} : intro_right A b₁ = intro_right A b₂ → b₁ = b₂ :=
  assume H, no_confusion H (λe, e)

  protected definition is_inhabited_left [instance] : inhabited A → inhabited (A + B) :=
  assume H : inhabited A, inhabited.mk (inl (default A))

  protected definition is_inhabited_right [instance] : inhabited B → inhabited (A + B) :=
  assume H : inhabited B, inhabited.mk (inr (default B))

  protected definition has_eq_decidable [instance] (h₁ : decidable_eq A) (h₂ : decidable_eq B) : ∀ s₁ s₂ : A + B, decidable (s₁ = s₂),
  has_eq_decidable (inl a₁) (inl a₂) :=
    match h₁ a₁ a₂ with
      decidable.inl hp := decidable.inl (hp ▸ rfl),
      decidable.inr hn := decidable.inr (λ he, absurd (inl_inj he) hn)
    end,
  has_eq_decidable (inl a₁) (inr b₂) := decidable.inr (λ e, sum.no_confusion e),
  has_eq_decidable (inr b₁) (inl a₂) := decidable.inr (λ e, sum.no_confusion e),
  has_eq_decidable (inr b₁) (inr b₂) :=
    match h₂ b₁ b₂ with
      decidable.inl hp := decidable.inl (hp ▸ rfl),
      decidable.inr hn := decidable.inr (λ he, absurd (inr_inj he) hn)
    end
end sum
