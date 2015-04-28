import data.nat

example (a b c : Prop) : a → b → c → a ∧ b ∧ c :=
begin
  intro Ha, intro Hb, intro Hc,
  apply and.intro Ha,
  apply and.intro Hb Hc
end

example (a b c : Prop) : a → b → c → a ∧ b ∧ c :=
by intro Ha; intro Hb; intro Hc; apply and.intro Ha; apply and.intro Hb Hc

open nat

example (a b c : nat) : a = b → b = 0 + c → a = c + 0:=
begin
  intro ab, intro bc,
  change a = c,
  rewrite zero_add at bc,
  rewrite -bc,
  exact ab
end
