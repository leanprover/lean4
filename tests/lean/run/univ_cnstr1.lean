constant {u₁ u₂ v} M : (Type (max u₁ u₂) → Type v) → Type
attribute [class] M

constant {u} L : Type u → Type u

constant {u₁ u₂} I : M.{u₁ u₂ (max u₁ u₂)} L.{max u₁ u₂}

attribute [instance] I

constant {u₁ u₂ v} R : ∀ {m : Type (max u₁ u₂) → Type v} [M m] {A : Type u₁} (a : A), m (ulift.{u₂} A)

noncomputable example : L (ulift.{3} unit) :=
R ()
