example (a b c : nat) (h₁ : a = b) (h₂ : b = c) : a = c :=
begin
  exact (eq.trans h₁ _)
end
