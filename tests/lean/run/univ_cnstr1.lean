constant {u₁ u₂ v} M : (Type (max 1 u₁ u₂) → Type v) → Type
attribute [class] M

constant {u} L : Type u → Type (max 1 u)

constant {u₁ u₂} I : M.{u₁ u₂ (max 1 u₁ u₂)} L.{max 1 u₁ u₂}

attribute [instance] I

constant {u₁ u₂ v} R : ∀ {m : Type (max 1 u₁ u₂) → Type v} [M m] {A : Type u₁} (a : A), m (ulift.{u₂} A)

noncomputable example : L (ulift.{3} unit) :=
R ()
