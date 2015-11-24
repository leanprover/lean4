/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Cubeovers
-/

import .squareover .cube

open equiv is_equiv

namespace eq

  -- we need to specify B explicitly, also in pathovers
  inductive cubeover {A : Type} (B : A → Type) {a₀₀₀ : A} {b₀₀₀ : B a₀₀₀}
    : Π{a₂₀₀ a₀₂₀ a₂₂₀ a₀₀₂ a₂₀₂ a₀₂₂ a₂₂₂ : A}
       {p₁₀₀ : a₀₀₀ = a₂₀₀} {p₀₁₀ : a₀₀₀ = a₀₂₀} {p₀₀₁ : a₀₀₀ = a₀₀₂}
       {p₁₂₀ : a₀₂₀ = a₂₂₀} {p₂₁₀ : a₂₀₀ = a₂₂₀} {p₂₀₁ : a₂₀₀ = a₂₀₂}
       {p₁₀₂ : a₀₀₂ = a₂₀₂} {p₀₁₂ : a₀₀₂ = a₀₂₂} {p₀₂₁ : a₀₂₀ = a₀₂₂}
       {p₁₂₂ : a₀₂₂ = a₂₂₂} {p₂₁₂ : a₂₀₂ = a₂₂₂} {p₂₂₁ : a₂₂₀ = a₂₂₂}
       {s₁₁₀ : square p₀₁₀ p₂₁₀ p₁₀₀ p₁₂₀}
       {s₁₁₂ : square p₀₁₂ p₂₁₂ p₁₀₂ p₁₂₂}
       {s₀₁₁ : square p₀₁₀ p₀₁₂ p₀₀₁ p₀₂₁}
       {s₂₁₁ : square p₂₁₀ p₂₁₂ p₂₀₁ p₂₂₁}
       {s₁₀₁ : square p₁₀₀ p₁₀₂ p₀₀₁ p₂₀₁}
       {s₁₂₁ : square p₁₂₀ p₁₂₂ p₀₂₁ p₂₂₁}
       (c : cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂)
                       {b₀₂₀ : B a₀₂₀} {b₂₀₀ : B a₂₀₀} {b₂₂₀ : B a₂₂₀}
       {b₀₀₂ : B a₀₀₂} {b₀₂₂ : B a₀₂₂} {b₂₀₂ : B a₂₀₂} {b₂₂₂ : B a₂₂₂}
       {q₁₀₀ : pathover B b₀₀₀ p₁₀₀ b₂₀₀} {q₀₁₀ : pathover B b₀₀₀ p₀₁₀ b₀₂₀}
       {q₀₀₁ : pathover B b₀₀₀ p₀₀₁ b₀₀₂} {q₁₂₀ : pathover B b₀₂₀ p₁₂₀ b₂₂₀}
       {q₂₁₀ : pathover B b₂₀₀ p₂₁₀ b₂₂₀} {q₂₀₁ : pathover B b₂₀₀ p₂₀₁ b₂₀₂}
       {q₁₀₂ : pathover B b₀₀₂ p₁₀₂ b₂₀₂} {q₀₁₂ : pathover B b₀₀₂ p₀₁₂ b₀₂₂}
       {q₀₂₁ : pathover B b₀₂₀ p₀₂₁ b₀₂₂} {q₁₂₂ : pathover B b₀₂₂ p₁₂₂ b₂₂₂}
       {q₂₁₂ : pathover B b₂₀₂ p₂₁₂ b₂₂₂} {q₂₂₁ : pathover B b₂₂₀ p₂₂₁ b₂₂₂}
       (t₀₁₁ : squareover B s₀₁₁ q₀₁₀ q₀₁₂ q₀₀₁ q₀₂₁)
       (t₂₁₁ : squareover B s₂₁₁ q₂₁₀ q₂₁₂ q₂₀₁ q₂₂₁)
       (t₁₀₁ : squareover B s₁₀₁ q₁₀₀ q₁₀₂ q₀₀₁ q₂₀₁)
       (t₁₂₁ : squareover B s₁₂₁ q₁₂₀ q₁₂₂ q₀₂₁ q₂₂₁)
       (t₁₁₀ : squareover B s₁₁₀ q₀₁₀ q₂₁₀ q₁₀₀ q₁₂₀)
       (t₁₁₂ : squareover B s₁₁₂ q₀₁₂ q₂₁₂ q₁₀₂ q₁₂₂), Type :=
  idcubeo : cubeover B idc idso idso idso idso idso idso



  -- variables {A : Type} {a₀₀₀ a₂₀₀ a₀₂₀ a₂₂₀ a₀₀₂ a₂₀₂ a₀₂₂ a₂₂₂ : A}
  --           {p₁₀₀ : a₀₀₀ = a₂₀₀} {p₀₁₀ : a₀₀₀ = a₀₂₀} {p₀₀₁ : a₀₀₀ = a₀₀₂}
  --           {p₁₂₀ : a₀₂₀ = a₂₂₀} {p₂₁₀ : a₂₀₀ = a₂₂₀} {p₂₀₁ : a₂₀₀ = a₂₀₂}
  --           {p₁₀₂ : a₀₀₂ = a₂₀₂} {p₀₁₂ : a₀₀₂ = a₀₂₂} {p₀₂₁ : a₀₂₀ = a₀₂₂}
  --           {p₁₂₂ : a₀₂₂ = a₂₂₂} {p₂₁₂ : a₂₀₂ = a₂₂₂} {p₂₂₁ : a₂₂₀ = a₂₂₂}
  --           {s₁₁₀ : square p₀₁₀ p₂₁₀ p₁₀₀ p₁₂₀}
  --           {s₁₁₂ : square p₀₁₂ p₂₁₂ p₁₀₂ p₁₂₂}
  --           {s₁₀₁ : square p₁₀₀ p₁₀₂ p₀₀₁ p₂₀₁}
  --           {s₁₂₁ : square p₁₂₀ p₁₂₂ p₀₂₁ p₂₂₁}
  --           {s₀₁₁ : square p₀₁₀ p₀₁₂ p₀₀₁ p₀₂₁}
  --           {s₂₁₁ : square p₂₁₀ p₂₁₂ p₂₀₁ p₂₂₁}

end eq
