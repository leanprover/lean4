/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad

The sum type, aka disjoint union.
-/
import logic.connectives
open inhabited eq.ops

notation A ⊎ B := sum A B

namespace sum
  notation A + B := sum A B
  namespace low_precedence_plus
    reserve infixr ` + `:25  -- conflicts with notation for addition
    infixr + := sum
  end low_precedence_plus

  variables {A B : Type}

  definition inl_ne_inr (a : A) (b : B) : inl a ≠ inr b :=
  by contradiction

  definition inr_ne_inl (b : B) (a : A) : inr b ≠ inl a :=
  by contradiction

  definition inl_inj {a₁ a₂ : A} : intro_left B a₁ = intro_left B a₂ → a₁ = a₂ :=
  assume H, by injection H; assumption

  definition inr_inj {b₁ b₂ : B} : intro_right A b₁ = intro_right A b₂ → b₁ = b₂ :=
  assume H, by injection H; assumption

  protected definition is_inhabited_left [instance] [h : inhabited A] : inhabited (A + B) :=
  inhabited.mk (inl (default A))

  protected definition is_inhabited_right [instance] [h : inhabited B] : inhabited (A + B) :=
  inhabited.mk (inr (default B))

  protected definition has_decidable_eq [instance] [h₁ : decidable_eq A] [h₂ : decidable_eq B] : ∀ s₁ s₂ : A + B, decidable (s₁ = s₂)
  | has_decidable_eq (inl a₁) (inl a₂) :=
    match h₁ a₁ a₂ with
      | decidable.inl hp := by left; congruence; assumption
      | decidable.inr hn := by right; intro h; injection h; contradiction
    end
  | has_decidable_eq (inl a₁) (inr b₂) := by right; contradiction
  | has_decidable_eq (inr b₁) (inl a₂) := by right; contradiction
  | has_decidable_eq (inr b₁) (inr b₂) :=
    match h₂ b₁ b₂ with
      | decidable.inl hp := by left; congruence; assumption
      | decidable.inr hn := by right; intro h; injection h; contradiction
    end
end sum
