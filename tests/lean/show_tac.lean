example (a b : Prop) : a ∧ b → b ∧ a :=
begin
  intro Hab,
  have Ha : a, from and.elim_left  Hab,
  have Hb : b, from and.elim_right Hab,
  show b ∧ a, from and.intro _ Ha
end
