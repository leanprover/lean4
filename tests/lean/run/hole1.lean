example : ∀ a b : nat, a + b = b + a :=
λ a b, {! _+_ !}

example : ∀ a b : nat, a + b = b + a :=
begin
  intros h,
  exact  λ x, {! _+_ !}
end
