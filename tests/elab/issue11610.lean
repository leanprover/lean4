import Lean

variable {α β γ δ : Sort _}

structure Prod' (α : Type u) (β : Type v) where
  /--
  Constructs a pair. This is usually written `(x, y)` instead of `Prod.mk x y`.
  -/
  mk ::
  /-- The first element of a pair. -/
  fst : α
  /-- The second element of a pair. -/
  snd : β

def mk.injArrow' {α : Type _} {β : Type _} {x₁ : α} {y₁ : β} {x₂ : α} {y₂ : β} :
    Prod'.mk x₁ y₁ = Prod'.mk x₂ y₂ → ∀ ⦃P : Sort _⦄, (x₁ = x₂ → y₁ = y₂ → P) → P :=
  fun h₁ _ h₂ ↦ Prod'.noConfusion rfl rfl (heq_of_eq h₁)
    (fun h₃ h₄ ↦ h₂ (eq_of_heq h₃) (eq_of_heq h₄))

-- Also for structures in Init:

def mk.injArrow {α : Type _} {β : Type _} {x₁ : α} {y₁ : β} {x₂ : α} {y₂ : β} :
    Prod.mk x₁ y₁ = Prod.mk x₂ y₂ → ∀ ⦃P : Sort _⦄, (x₁ = x₂ → y₁ = y₂ → P) → P :=
  fun h₁ _ h₂ ↦ Prod.noConfusion rfl rfl (heq_of_eq h₁)
    (fun h₃ h₄ ↦ h₂ (eq_of_heq h₃) (eq_of_heq h₄))
