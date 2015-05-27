/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Squareovers
-/

import types.square

open eq equiv is_equiv equiv.ops

namespace eq

  -- we give the argument B explicitly, because Lean would find (λa, B a) by itself, which
  -- makes the type uglier (of course the two terms are definitionally equal)
  inductive squareover {A : Type} (B : A → Type) {a₀₀ : A} {b₀₀ : B a₀₀} :
    Π{a₂₀ a₀₂ a₂₂ : A}
     {p₁₀ : a₀₀ = a₂₀} {p₁₂ : a₀₂ = a₂₂} {p₀₁ : a₀₀ = a₀₂} {p₂₁ : a₂₀ = a₂₂}
     (s₁₁ : square p₁₀ p₁₂ p₀₁ p₂₁)
     {b₂₀ : B a₂₀} {b₀₂ : B a₀₂} {b₂₂ : B a₂₂}
     (q₁₀ : pathover B b₀₀ p₁₀ b₂₀) (q₁₂ : pathover B b₀₂ p₁₂ b₂₂)
     (q₀₁ : pathover B b₀₀ p₀₁ b₀₂) (q₂₁ : pathover B b₂₀ p₂₁ b₂₂),
     Type :=
  idsquareo : squareover B ids idpo idpo idpo idpo


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
   {q₀₁ : b₀₀ =[p₀₁] b₀₂} /-t₁₁-/ {q₂₁ : b₂₀ =[p₂₁] b₂₂} /-t₃₁-/ {q₄₁ : b₄₀ =[p₄₁] b₄₂}
            /-b₀₂-/ {q₁₂ : b₀₂ =[p₁₂] b₂₂} /-b₂₂-/ {q₃₂ : b₂₂ =[p₃₂] b₄₂} /-b₄₂-/
   {q₀₃ : b₀₂ =[p₀₃] b₀₄} /-t₁₃-/ {q₂₃ : b₂₂ =[p₂₃] b₂₄} /-t₃₃-/ {q₄₃ : b₄₂ =[p₄₃] b₄₄}
            /-b₀₄-/ {q₁₄ : b₀₄ =[p₁₄] b₂₄} /-b₂₄-/ {q₃₄ : b₂₄ =[p₃₄] b₄₄} /-b₄₄-/

  definition squareo := @squareover A B a₀₀
  definition idsquareo [reducible] [constructor] (b₀₀ : B a₀₀) := @squareover.idsquareo A B a₀₀ b₀₀
  definition idso      [reducible] [constructor]               := @squareover.idsquareo A B a₀₀ b₀₀

  definition apds (f : Πa, B a) (s : square p₁₀ p₁₂ p₀₁ p₂₁)
    : squareover B s (apdo f p₁₀) (apdo f p₁₂) (apdo f p₀₁) (apdo f p₂₁) :=
  square.rec_on s idso

  definition vrflo : squareover B vrfl q₁₀ q₁₀ idpo idpo :=
  by cases q₁₀; exact idso

  definition vdeg_squareover {q₁₀' : b₀₀ =[p₁₀] b₂₀} (p : q₁₀ = q₁₀')
    : squareover B vrfl q₁₀ q₁₀' idpo idpo :=
  by cases p;exact vrflo

  definition eq_of_vdeg_squareover {q₁₀' : b₀₀ =[p₁₀] b₂₀}
    (p : squareover B vrfl q₁₀ q₁₀' idpo idpo) : q₁₀ = q₁₀' :=
  sorry
end eq
