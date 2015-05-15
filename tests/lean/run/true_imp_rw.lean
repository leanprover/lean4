import logic

example (a b c : Prop) (h : a) : true → true → a :=
begin
  rewrite *true_imp,
  exact h
end
