example {A : Type} (a b c : A) : a = b → b = c → a = c :=
begin
  intro h₁ h₂,
  with_options [pp.implicit true, pp.notation false] state; state,
  with_options [pp.all true, pp.max_depth 1] state,
  with_options [pp.notation false] state,
  with_options [pp.notation false] (state; state),
  substvars
end

example {A : Type} (a b c : A) : a = b → b = c → a = c :=
begin
  intros,
  with_options [] id, -- error
end
