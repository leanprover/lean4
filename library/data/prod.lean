/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: data.prod
Author: Leonardo de Moura, Jeremy Avigad
-/
import logic.eq
open inhabited decidable eq.ops

namespace prod
  variables {A B : Type} {a₁ a₂ : A} {b₁ b₂ : B} {u : A × B}

  theorem pair_eq : a₁ = a₂ → b₁ = b₂ → (a₁, b₁) = (a₂, b₂) :=
  assume H1 H2, H1 ▸ H2 ▸ rfl

  protected theorem equal {p₁ p₂ : prod A B} : pr₁ p₁ = pr₁ p₂ → pr₂ p₁ = pr₂ p₂ → p₁ = p₂ :=
  destruct p₁ (take a₁ b₁, destruct p₂ (take a₂ b₂ H₁ H₂, pair_eq H₁ H₂))

  protected definition is_inhabited [instance] : inhabited A → inhabited B → inhabited (prod A B) :=
  take (H₁ : inhabited A) (H₂ : inhabited B),
    inhabited.destruct H₁ (λa, inhabited.destruct H₂ (λb, inhabited.mk (pair a b)))

  protected definition has_decidable_eq [instance] : decidable_eq A → decidable_eq B → decidable_eq (A × B) :=
  take (H₁ : decidable_eq A) (H₂ : decidable_eq B) (u v : A × B),
    have H₃ : u = v ↔ (pr₁ u = pr₁ v) ∧ (pr₂ u = pr₂ v), from
      iff.intro
        (assume H, H ▸ and.intro rfl rfl)
        (assume H, and.elim H (assume H₄ H₅, equal H₄ H₅)),
    decidable_of_decidable_of_iff _ (iff.symm H₃)
end prod
