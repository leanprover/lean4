/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad

The sum type, aka disjoint union.
-/
import logic.connectives
open inhabited

notation A ⊎ B := sum A B

namespace sum
  notation A + B := sum A B
  namespace low_precedence_plus
    reserve infixr ` + `:25  -- conflicts with notation for addition
    infixr + := sum
  end low_precedence_plus

  variables {A B : Type}

  definition inl_ne_inr (a : A) (b : B) : inl a ≠ inr b :=
  sorry -- by contradiction

  definition inr_ne_inl (b : B) (a : A) : inr b ≠ inl a :=
  sorry -- by contradiction

  definition inl_inj {a₁ a₂ : A} : intro_left B a₁ = intro_left B a₂ → a₁ = a₂ :=
  sorry -- assume H, by injection H; assumption

  definition inr_inj {b₁ b₂ : B} : intro_right A b₁ = intro_right A b₂ → b₁ = b₂ :=
  sorry -- assume H, by injection H; assumption

  attribute [instance]
  protected definition is_inhabited_left [h : inhabited A] : inhabited (A + B) :=
  inhabited.mk (inl (default A))

  attribute [instance]
  protected definition is_inhabited_right [h : inhabited B] : inhabited (A + B) :=
  inhabited.mk (inr (default B))
end sum
