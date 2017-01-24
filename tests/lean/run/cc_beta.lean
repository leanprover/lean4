example (f : nat → nat → nat) (a b c : nat) :
  f a = (λ x, x) → f a b = b :=
begin [smt]
  intros,
end

example (f g : nat → nat → nat) (a b c : nat) :
  f a = g c → f a = (λ x, x) → g c b = b :=
begin [smt]
  intros,
end

constant F : nat → nat → nat
constant G : nat → nat → nat

example (a b c : nat) :
  F a = (λ x, x) → F a b = b :=
begin [smt]
  intros,
end

example (a b c : nat) :
  F a = G c → F a = (λ x, x) → G c b = b :=
begin [smt]
  intros,
end

example (f : nat → nat → nat) (a b c : nat) :
  f a b ≠ b → f a = (λ x, x) → false :=
begin [smt]
  intros,
end

example (f g : nat → nat → nat) (a b c : nat) :
  g c b ≠ b → f a = g c → f a = (λ x, x) → false :=
begin [smt]
  intros,
end

example (f g : nat → nat → nat) (a b c : nat) :
  f a = g c → g c b ≠ b → f a = (λ x, x) → false :=
begin [smt]
  intros,
end

example (a b c : nat) :
  F a b ≠ b → F a = (λ x, x) → false :=
begin [smt]
  intros,
end

example (a b c : nat) :
  G c b ≠ b → F a = G c → F a = (λ x, x) → false :=
begin [smt]
  intros,
end

example (f : nat → nat → nat) (g : nat → nat → nat → nat) (a b c d : nat) :
  g c d b ≠ b → f a = g c a → f a = (λ x, x) → d = a → false :=
begin [smt]
  intros,
end

example (f : nat → nat → nat) (g : nat → nat → nat → nat) (a b c d : nat) :
  d = a → g c d b ≠ b → f a = g c a → f a = (λ x, x) → false :=
begin [smt]
  intros,
end
