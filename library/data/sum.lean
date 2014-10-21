-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura, Jeremy Avigad
import logic.prop logic.inhabited logic.decidable
open inhabited decidable eq.ops
-- data.sum
-- ========
-- The sum type, aka disjoint union.

inductive sum (A B : Type) : Type :=
  inl : A → sum A B,
  inr : B → sum A B

namespace sum
  notation A ⊎ B := sum A B
  namespace extra_notation
    reserve infixr `+`:25 -- conflicts with notation for addition
    infixr `+` := sum
  end extra_notation

  variables {A B : Type}
  variables {a a₁ a₂ : A} {b b₁ b₂ : B}
  protected definition rec_on {C : (A ⊎ B) → Type} (s : A ⊎ B) (H₁ : ∀a : A, C (inl B a)) (H₂ : ∀b : B, C (inr A b)) : C s :=
  rec H₁ H₂ s

  protected definition cases_on {P : (A ⊎ B) → Prop} (s : A ⊎ B) (H₁ : ∀a : A, P (inl B a)) (H₂ : ∀b : B, P (inr A b)) : P s :=
  rec H₁ H₂ s

  -- Here is the trick for the theorems that follow:
  -- Fixing a₁, "f s" is a recursive description of "inl B a₁ = s".
  -- When s is (inl B a₁), it reduces to a₁ = a₁.
  -- When s is (inl B a₂), it reduces to a₁ = a₂.
  -- When s is (inr A b), it reduces to false.

  theorem inl_inj : inl B a₁ = inl B a₂ → a₁ = a₂ :=
  assume H,
  let f := λs, rec_on s (λa, a₁ = a) (λb, false) in
  have H₁ : f (inl B a₁), from rfl,
  have H₂ : f (inl B a₂), from H ▸ H₁,
  H₂

  theorem inl_neq_inr : inl B a ≠ inr A b :=
  assume H,
  let f := λs, rec_on s (λa', a = a') (λb, false) in
  have H₁ : f (inl B a), from rfl,
  have H₂ : f (inr A b), from H ▸ H₁,
  H₂

  theorem inr_inj : inr A b₁ = inr A b₂ → b₁ = b₂ :=
  assume H,
  let f := λs, rec_on s (λa, false) (λb, b₁ = b) in
  have H₁ : f (inr A b₁), from rfl,
  have H₂ : f (inr A b₂), from H ▸ H₁,
  H₂

  protected definition is_inhabited_left [instance] : inhabited A → inhabited (A ⊎ B) :=
  assume H : inhabited A, inhabited.mk (inl B (default A))

  protected definition is_inhabited_right [instance] : inhabited B → inhabited (A ⊎ B) :=
  assume H : inhabited B, inhabited.mk (inr A (default B))

  protected definition has_eq_decidable [instance] : decidable_eq A → decidable_eq B → decidable_eq (A ⊎ B) :=
  assume (H₁ : decidable_eq A) (H₂ : decidable_eq B),
  take s₁ s₂ : A ⊎ B,
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
