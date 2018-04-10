def f (x : nat) := x

example (a b : nat) (h₁ : a = b) (h₂ : a = 0) : b = f 0 :=
begin
  simp [h₁] at a h₂,
  simp [h₂, f]
end
