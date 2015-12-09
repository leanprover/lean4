open prod

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

open nat

example (a : nat) : a > 0 → Σ(x : ℕ), x > 0 :=
begin
  intro Ha,
  existsi a,
  apply Ha
end

example : nat :=
begin
  constructor 1
end

example : nat :=
begin
  constructor 2,
  constructor 2,
  constructor 1
end
