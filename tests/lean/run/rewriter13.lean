open nat

example (x y : nat) (H1 : sigma.pr1 ⟨x, y⟩ = 0) : x = 0 :=
begin
  rewrite ▸* at H1,
  rewrite H1
end
