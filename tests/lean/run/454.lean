constants (A : Type₁) (P : A → Type₁) (H : Π{a b : A}, P a → P b) (a b : A) (K : P a)

theorem foo : P b :=
begin
  apply H, {apply K}
end
