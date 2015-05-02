open nat

example (a b c : nat) : a = 0 → b = 1 + a → a = b → false :=
begin
  intro a0 b1 ab,
  subst a0 b1,
  state,
  contradiction
end

example (a b c : nat) : a = 0 → b = 1 + a → a = b → false :=
begin
  intro a0 b1 ab,
  subst a0, subst b1,
  state,
  contradiction
end

example (a b c : nat) : a = 0 → 1 + a = b → a = b → false :=
begin
  intro a0 b1 ab,
  subst a0 b1,
  state,
  contradiction
end

example (a b c : nat) : a = 0 → 1 + a = b → a = b → false :=
begin
  intros,
  subst a b,
  state,
  contradiction
end
