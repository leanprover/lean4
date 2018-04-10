example (a b : nat) : a + b = b + a :=
begin
  dsimp [has_add.add],
  guard_target nat.add a b = nat.add b a,
  apply add_comm
end

example (f g : nat → nat) : (f ∘ g) = (λ x, f (g x)) :=
begin
  fail_if_success {dsimp},
  dsimp {unfold_reducible := tt},
  guard_target (λ x, f (g x)) = (λ x, f (g x)),
  refl
end
