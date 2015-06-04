/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Definition of squares, cubes, squareovers and cubeovers
-/

--path (eq) and pathover are defined in init.datatypes and init.pathover, respectively

exit

namespace eq

  variable {A : Type}

  inductive square {A : Type} {a₀₀ : A}
    : Π{a₂₀ a₀₂ a₂₂ : A}, a₀₀ = a₂₀ → a₀₂ = a₂₂ → a₀₀ = a₀₂ → a₂₀ = a₂₂ → Type :=
  ids : square idp idp idp idp

  definition ids      [reducible] [constructor]         := @square.ids
  definition idsquare [reducible] [constructor] (a : A) := @square.ids A a

  inductive squareover {A : Type} (B : A → Type) {a₀₀ : A} {b₀₀ : B a₀₀} :
    Π{a₂₀ a₀₂ a₂₂ : A}
     {p₁₀ : a₀₀ = a₂₀} {p₁₂ : a₀₂ = a₂₂} {p₀₁ : a₀₀ = a₀₂} {p₂₁ : a₂₀ = a₂₂}
     (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
     {b₂₀ : B a₂₀} {b₀₂ : B a₀₂} {b₂₂ : B a₂₂}
     (q₁₀ : pathover B b₀₀ p₁₀ b₂₀) (q₁₂ : pathover B b₀₂ p₁₂ b₂₂)
     (q₀₁ : pathover B b₀₀ p₀₁ b₀₂) (q₂₁ : pathover B b₂₀ p₂₁ b₂₂),
     Type :=
  idsquareo : squareover B ids idpo idpo idpo idpo



end eq
