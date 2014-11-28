/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: data.sum
Authors: Leonardo de Moura, Jeremy Avigad

The sum type, aka disjoint union.
-/

import logic.prop logic.inhabited logic.decidable
open inhabited decidable eq.ops

inductive sum (A B : Type) : Type :=
  inl : A → sum A B,
  inr : B → sum A B

namespace sum
  notation A ⊎ B := sum A B
  notation A + B := sum A B
  namespace low_precedence_plus
    reserve infixr `+`:25  -- conflicts with notation for addition
    infixr `+` := sum
  end low_precedence_plus

  variables {A B : Type}
  variables {a a₁ a₂ : A} {b b₁ b₂ : B}

  theorem inl_neq_inr : inl B a ≠ inr A b :=
  assume H, no_confusion H

  theorem inl_inj : inl B a₁ = inl B a₂ → a₁ = a₂ :=
  assume H, no_confusion H (λe, e)

  theorem inr_inj : inr A b₁ = inr A b₂ → b₁ = b₂ :=
  assume H, no_confusion H (λe, e)

  protected definition is_inhabited_left [instance] : inhabited A → inhabited (A + B) :=
  assume H : inhabited A, inhabited.mk (inl B (default A))

  protected definition is_inhabited_right [instance] : inhabited B → inhabited (A + B) :=
  assume H : inhabited B, inhabited.mk (inr A (default B))

  protected definition has_eq_decidable [instance] :
    decidable_eq A → decidable_eq B → decidable_eq (A + B) :=
  assume (H₁ : decidable_eq A) (H₂ : decidable_eq B),
  take s₁ s₂ : A + B,
    rec_on s₁
      (take a₁, show decidable (inl B a₁ = s₂), from
        rec_on s₂
          (take a₂, show decidable (inl B a₁ = inl B a₂), from
            decidable.rec_on (H₁ a₁ a₂)
              (assume Heq : a₁ = a₂, decidable.inl (Heq ▸ rfl))
              (assume Hne : a₁ ≠ a₂, decidable.inr (mt inl_inj Hne)))
          (take b₂,
            have H₃ : (inl B a₁ = inr A b₂) ↔ false,
              from iff.intro inl_neq_inr (assume H₄, false_elim H₄),
            show decidable (inl B a₁ = inr A b₂), from decidable_iff_equiv _ (iff.symm H₃)))
      (take b₁, show decidable (inr A b₁ = s₂), from
        rec_on s₂
          (take a₂,
            have H₃ : (inr A b₁ = inl B a₂) ↔ false,
              from iff.intro (assume H₄, inl_neq_inr (H₄⁻¹)) (assume H₄, false_elim H₄),
            show decidable (inr A b₁ = inl B a₂), from decidable_iff_equiv _ (iff.symm H₃))
          (take b₂, show decidable (inr A b₁ = inr A b₂), from
            decidable.rec_on (H₂ b₁ b₂)
              (assume Heq : b₁ = b₂, decidable.inl (Heq ▸ rfl))
              (assume Hne : b₁ ≠ b₂, decidable.inr (mt inr_inj Hne))))
end sum
