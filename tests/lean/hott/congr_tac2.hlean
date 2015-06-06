open nat is_trunc

example (f : Π (a b : nat), a = b → nat) (a₁ a₂ b₁ b₂ : nat) (h₁ : a₁ = b₁) (h₂ : a₂ = b₂) : a₁ = a₂ → b₁ = b₂ → f a₁ b₁ h₁ = f a₂ b₂ h₂ :=
begin
  intros,
  congruence,
  repeat assumption
end
