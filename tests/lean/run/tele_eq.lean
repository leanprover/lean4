constant A₁ : Type
constant A₂ : A₁ → Type
constant A₃ : Π (a₁ : A₁), A₂ a₁ → Type

structure foo :=
mk :: (a₁ : A₁) (a₂ : A₂ a₁) (a₃ : A₃ a₁ a₂)

theorem foo.eq {a₁ b₁ : A₁} {a₂ : A₂ a₁} {b₂ : A₂ b₁} {a₃ : A₃ a₁ a₂} {b₃ : A₃ b₁ b₂}
               (H₁ : a₁ = b₁) (H₂ : a₂ == b₂) (H₃ : a₃ == b₃)
               : foo.mk a₁ a₂ a₃ = foo.mk b₁ b₂ b₃ :=
begin
  cases H₁,
  cases H₂,
  cases H₃,
  apply rfl
end

reveal foo.eq
print definition foo.eq
