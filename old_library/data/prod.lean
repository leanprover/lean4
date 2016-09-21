/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad
-/
import logic.eq
open inhabited decidable

namespace prod
  variables {A B : Type} {a₁ a₂ : A} {b₁ b₂ : B} {u : A × B}

  theorem pair_eq : a₁ = a₂ → b₁ = b₂ → (a₁, b₁) = (a₂, b₂) :=
  assume H1 H2, H1 ▸ H2 ▸ rfl

  protected theorem eq {p₁ p₂ : prod A B} : pr₁ p₁ = pr₁ p₂ → pr₂ p₁ = pr₂ p₂ → p₁ = p₂ :=
  destruct p₁ (take a₁ b₁, destruct p₂ (take a₂ b₂ H₁ H₂, pair_eq H₁ H₂))

  definition swap {A : Type} : A × A → A × A
  | (a, b) := (b, a)

  theorem swap_swap {A : Type} : ∀ p : A × A, swap (swap p) = p
  | (a, b) := rfl

  theorem eq_of_swap_eq {A : Type} : ∀ p₁ p₂ : A × A, swap p₁ = swap p₂ → p₁ = p₂ :=
  take p₁ p₂, assume seqs,
  have swap (swap p₁) = swap (swap p₂), from congr_arg swap seqs,
  sorry -- by rewrite *swap_swap at this; exact this
end prod
