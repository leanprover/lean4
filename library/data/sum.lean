/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: data.sum
Authors: Leonardo de Moura, Jeremy Avigad

The sum type, aka disjoint union.
-/
import logic.connectives
open inhabited decidable eq.ops

namespace sum
  notation A ⊎ B := sum A B
  notation A + B := sum A B
  namespace low_precedence_plus
    reserve infixr `+`:25  -- conflicts with notation for addition
    infixr `+` := sum
  end low_precedence_plus

  variables {A B : Type}
  variables {a a₁ a₂ : A} {b b₁ b₂ : B}

  theorem inl_neq_inr : inl a ≠ inr b :=
  assume H, no_confusion H

  theorem inl_inj : intro_left B a₁ = intro_left B a₂ → a₁ = a₂ :=
  assume H, no_confusion H (λe, e)

  theorem inr_inj : intro_right A b₁ = intro_right A b₂ → b₁ = b₂ :=
  assume H, no_confusion H (λe, e)

  protected definition is_inhabited_left [instance] : inhabited A → inhabited (A + B) :=
  assume H : inhabited A, inhabited.mk (inl (default A))

  protected definition is_inhabited_right [instance] : inhabited B → inhabited (A + B) :=
  assume H : inhabited B, inhabited.mk (inr (default B))

  protected definition has_eq_decidable [instance] :
    decidable_eq A → decidable_eq B → decidable_eq (A + B) :=
  assume (H₁ : decidable_eq A) (H₂ : decidable_eq B),
  take s₁ s₂ : A + B,
    rec_on s₁
      (take a₁, show decidable (inl a₁ = s₂), from
        rec_on s₂
          (take a₂, show decidable (inl a₁ = inl a₂), from
            decidable.rec_on (H₁ a₁ a₂)
              (assume Heq : a₁ = a₂, decidable.inl (Heq ▸ rfl))
              (assume Hne : a₁ ≠ a₂, decidable.inr (mt inl_inj Hne)))
          (take b₂,
            have H₃ : (inl a₁ = inr b₂) ↔ false,
              from iff.intro inl_neq_inr (assume H₄, !false.rec H₄),
            show decidable (inl a₁ = inr b₂), from decidable_of_decidable_of_iff _ (iff.symm H₃)))
      (take b₁, show decidable (inr b₁ = s₂), from
        rec_on s₂
          (take a₂,
            have H₃ : (inr b₁ = inl a₂) ↔ false,
              from iff.intro (assume H₄, inl_neq_inr (H₄⁻¹)) (assume H₄, !false.rec H₄),
            show decidable (inr b₁ = inl a₂), from decidable_of_decidable_of_iff _ (iff.symm H₃))
          (take b₂, show decidable (inr b₁ = inr b₂), from
            decidable.rec_on (H₂ b₁ b₂)
              (assume Heq : b₁ = b₂, decidable.inl (Heq ▸ rfl))
              (assume Hne : b₁ ≠ b₂, decidable.inr (mt inr_inj Hne))))
end sum
