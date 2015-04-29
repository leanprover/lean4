import algebra.category

open category

section
  parameter {D₀ : Type}
  parameter (C  : precategory D₀)
  parameter (D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d), Type)
  attribute comp [reducible]

  definition comp₁_type [reducible]  : Type :=
  Π ⦃a b c₁ d₁ c₂ d₂ : D₀⦄
    ⦃f₁ : hom a b⦄ ⦃g₁ : hom c₁ d₁⦄ ⦃h₁ : hom a c₁⦄ ⦃i₁ : hom b d₁⦄
    ⦃g₂ : hom c₂ d₂⦄ ⦃h₂ : hom c₁ c₂⦄ ⦃i₂ : hom d₁ d₂⦄,
    (D₂ g₁ g₂ h₂ i₂) → (D₂ f₁ g₁ h₁ i₁) → (@D₂ a b c₂ d₂ f₁ g₂ (h₂ ∘ h₁) (i₂ ∘ i₁))

  definition ID₁_type [reducible] : Type :=
  Π ⦃a b : D₀⦄ (f : hom a b), D₂ f f (ID a) (ID b)

  structure worm_precat [class] : Type :=
  (comp₁     : comp₁_type)
  (ID₁       : ID₁_type)
end

section
  parameter {D₀ : Type}
  parameter [C : precategory D₀]
  parameter {D₂ : Π ⦃a b c d : D₀⦄ (f : hom a b) (g : hom c d) (h : hom a c) (i : hom b d), Type}
  parameter [D : worm_precat C D₂]
  include D

  structure two_cell_ob : Type :=
  (vo1 : D₀) (vo2 : D₀) (vo3 : hom vo1 vo2)
end
