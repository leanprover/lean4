example (f : nat → nat) (a b : nat) : f a = a → f (f a) = a :=
begin
  intro h₁,
  subst h₁ -- ERROR
end

open nat

example (f : nat → nat) (a b : nat) : f a = a → a = 0 → f (f a) = a :=
begin
  intro h₁ h₂,
  subst a, -- should use h₂
  rewrite +h₁
end
