import logic
open tactic

theorem tst1 (a b : Prop) : a → b → b :=
by intro Ha; intro Hb; apply Hb

theorem tst2 (a b : Prop) : a → b → a ∧ b :=
by intro Ha; intro Hb; rapply and.intro; apply Hb; apply Ha

theorem tst3 (a b : Prop) : a → b → a ∧ b :=
begin
 intro Ha,
 intro Hb,
 apply and.intro,
 apply Ha,
 apply Hb,
end

theorem tst4 (a b : Prop) : a → b → a ∧ b :=
begin
  intros [Ha, Hb],
  rapply and.intro,
  apply Hb,
  apply Ha
end

theorem tst5 (a b : Prop) : a → b → a ∧ b :=
begin
  intros,
  apply and.intro,
  eassumption,
  eassumption
end
