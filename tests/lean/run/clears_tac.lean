import logic

example {a b c : Prop} : a → b → c → a ∧ b :=
begin
  intros [Ha, Hb, Hc],
  clears [Hc, c],
  apply  (and.intro Ha Hb),
end

example {a b c : Prop} : a → b → c → c ∧ b :=
begin
  intros [Ha, Hb, Hc],
  clears [Ha, a],
  apply  (and.intro Hc Hb),
end
