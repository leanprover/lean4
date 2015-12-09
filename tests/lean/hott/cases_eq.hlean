open eq

theorem trans {A : Type} {a b c : A} (h₁ : a = b) (h₂ : b = c) : a = c :=
begin
  cases h₁, cases h₂, apply rfl
end

theorem symm {A : Type} {a b : A} (h₁ : a = b) : b = a :=
begin
  cases h₁, apply rfl
end

theorem congr2 {A B : Type} (f : A → B) {a₁ a₂ : A} (h : a₁ = a₂) : f a₁ = f a₂ :=
begin
  cases h, apply rfl
end

definition inv_pV_2 {A : Type} {x y z : A} (p : x = y) (q : z = y) : (p ⬝ q⁻¹)⁻¹ = q ⬝ p⁻¹ :=
begin
  cases p, cases q, apply rfl
end
