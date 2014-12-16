import logic

example : ∃ a : num, a = a :=
begin
  fapply exists.intro,
  exact 0,
  apply rfl,
end
