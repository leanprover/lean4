example (a b : Prop) (H : b ∧ a) : a ∧ b :=
begin
  assert  H : a
end

example (a : Prop) (Ha : a) : a :=
begin
  exact Ha,
  assert  H : a
end
