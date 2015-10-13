import data.list

example (a b c : Prop) : a → b → c → a ∧ b ∧ c :=
begin
  intro Ha Hb Hc,
  split,
  assumption,
  split,
  repeat assumption
end

example (a b c : Type) : a → b → c → a × b × c :=
begin
  intro Ha Hb Hc,
  repeat (split | assumption)
end

example (a b : Type) : a → sum a b :=
begin
  intro Ha,
  left,
  assumption
end

example (a b : Type) : b → sum a b :=
begin
  intro Ha,
  right,
  assumption
end

example (a b : Prop) : a → a ∨ b :=
begin
  intro Ha,
  left,
  assumption
end

example (a b : Prop) : b → a ∨ b :=
begin
  intro Ha,
  right,
  assumption
end

open nat

example (a : nat) : a > 0 → ∃ x : nat, x > 0 :=
begin
  intro Ha,
  existsi a,
  apply Ha
end

example : list nat :=
begin
  constructor 1
end

example : list nat :=
begin
  constructor 2,
  constructor 1,
  constructor 1
end
