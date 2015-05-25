open nat

example (A B : Type) (a : A) (b : B) (h₁ : A = B) (h₂ : eq.rec_on h₁ a = b) : b = eq.rec_on h₁ a :=
begin
  substvars
end

example (A B : Type) (a : A) (b : B) (h₁ : A = B) (h₂ : eq.rec_on h₁ a = b) : b = eq.rec_on h₁ a :=
begin
  substvars
end

example (a b c : nat) (a0 : a = 0) (b1 : b = 1 + a) (ab : a = b) : empty :=
begin
  substvars,
  contradiction
end

example (a : nat) : a = 0 → a = 1 → empty :=
begin
  intro a0 a1,
  substvars,
  contradiction
end

example (a b c : nat) : a = 0 → b = 1 + a → a = b → empty :=
begin
  intro a0 b1 ab,
  substvars,
  state,
  contradiction
end
example (a b c : nat) : a = 0 → b = 1 + a → a = b → empty :=
begin
  intro a0 b1 ab,
  substvars,
  contradiction
end

example (a b c : nat) : a = 0 → 1 + a = b → a = b → empty :=
begin
  intro a0 b1 ab,
  substvars,
  contradiction
end

example (a b c : nat) : a = 0 → 1 + a = b → a = b → empty :=
begin
  intros,
  substvars,
  contradiction
end
