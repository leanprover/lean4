example (a b c : nat) (h₁ : a = b) (h₂ : b = c) : b = c :=
begin
  (exact h₁ | exact h₂)
end
