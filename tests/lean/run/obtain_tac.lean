example (a b : Prop) : a ∧ b → b ∧ a :=
begin
  intro Hab,
  obtain Ha Hb, from Hab,
  show b ∧ a, from and.intro Hb Ha
end
