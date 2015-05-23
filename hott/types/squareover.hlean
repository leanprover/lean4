/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Theorems about squareovers
-/

import cubical.pathover cubical.square

open eq equiv is_equiv equiv.ops

namespace cubical

  variables {A A' : Type} {B : A → Type}
            {a a' a'' a₀₀ a₂₀ a₄₀ a₀₂ a₂₂ a₂₄ a₀₄ a₄₂ a₄₄ : A}
            /-a₀₀-/ {p₁₀ : a₀₀ = a₂₀} /-a₂₀-/ {p₃₀ : a₂₀ = a₄₀} /-a₄₀-/
       {p₀₁ : a₀₀ = a₀₂} /-s₁₁-/ {p₂₁ : a₂₀ = a₂₂} /-s₃₁-/ {p₄₁ : a₄₀ = a₄₂}
            /-a₀₂-/ {p₁₂ : a₀₂ = a₂₂} /-a₂₂-/ {p₃₂ : a₂₂ = a₄₂} /-a₄₂-/
       {p₀₃ : a₀₂ = a₀₄} /-s₁₃-/ {p₂₃ : a₂₂ = a₂₄} /-s₃₃-/ {p₄₃ : a₄₂ = a₄₄}
            /-a₀₄-/ {p₁₄ : a₀₄ = a₂₄} /-a₂₄-/ {p₃₄ : a₂₄ = a₄₄} /-a₄₄-/
            {s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁}
            {b₀₀ : B a₀₀} {b₂₀ : B a₂₀} {b₄₀ : B a₄₀}
            {b₀₂ : B a₀₂} {b₂₂ : B a₂₂} {b₄₂ : B a₄₂}
            {b₀₄ : B a₀₄} {b₂₄ : B a₂₄} {b₄₄ : B a₄₄}
            /-b₀₀-/ {q₁₀ : b₀₀ =[p₁₀] b₂₀} /-b₂₀-/ {q₃₀ : b₂₀ =[p₃₀] b₄₀} /-b₄₀-/
   {q₀₁ : b₀₀ =[p₀₁] b₀₂} /-s₁₁-/ {q₂₁ : b₂₀ =[p₂₁] b₂₂} /-s₃₁-/ {q₄₁ : b₄₀ =[p₄₁] b₄₂}
            /-b₀₂-/ {q₁₂ : b₀₂ =[p₁₂] b₂₂} /-b₂₂-/ {q₃₂ : b₂₂ =[p₃₂] b₄₂} /-b₄₂-/
   {q₀₃ : b₀₂ =[p₀₃] b₀₄} /-s₁₃-/ {q₂₃ : b₂₂ =[p₂₃] b₂₄} /-s₃₃-/ {q₄₃ : b₄₂ =[p₄₃] b₄₄}
            /-b₀₄-/ {q₁₄ : b₀₄ =[p₁₄] b₂₄} /-b₂₄-/ {q₃₄ : b₂₄ =[p₃₄] b₄₄} /-b₄₄-/

  inductive squareover (B : A → Type) {b₀₀ : B a₀₀} :
    Π{a₂₀ a₀₂ a₂₂ : A} {p₁₀ : a₀₀ = a₂₀} {p₁₂ : a₀₂ = a₂₂} {p₀₁ : a₀₀ = a₀₂} {p₂₁ : a₂₀ = a₂₂}
     (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
     {b₂₀ : B a₂₀} {b₀₂ : B a₀₂} {b₂₂ : B a₂₂}
     (q₁₀ : b₀₀ =[p₁₀] b₂₀) (q₁₂ : b₀₂ =[p₁₂] b₂₂) (q₀₁ : b₀₀ =[p₀₁] b₀₂) (q₂₁ : b₂₀ =[p₂₁] b₂₂),
     Type :=
  idsquareo : squareover B ids idpo idpo idpo idpo

  definition squareo := @squareover A a₀₀ B
  definition idsquareo [reducible] [constructor] (b₀₀ : B a₀₀) := @squareover.idsquareo A a₀₀ B b₀₀
  definition idso [reducible] [constructor] := @squareover.idsquareo A a₀₀ B b₀₀



end cubical
