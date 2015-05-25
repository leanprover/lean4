open nat

example (A B : Type) (a : A) (b : B) (h₁ : A = B) (h₂ : eq.rec_on h₁ a = b) : b = eq.rec_on h₁ a :=
begin
  subst h₁ h₂
end

example (A B : Type) (a : A) (b : B) (h₁ : A = B) (h₂ : eq.rec_on h₁ a = b) : b = eq.rec_on h₁ a :=
begin
  subst B h₂
end

example (a b c : nat) (a0 : a = 0) (b1 : b = 1 + a) (ab : a = b) : empty :=
begin
  subst a0,
  subst b1,
  contradiction
end

example (a : nat) : a = 0 → a = 1 → empty :=
begin
  intro a0 a1,
  subst a0,
  contradiction
end

example (a b c : nat) : a = 0 → b = 1 + a → a = b → empty :=
begin
  intro a0 b1 ab,
  subst a0,
  rewrite b1 at *,
  state,
  contradiction
end

example (a b c : nat) : a = 0 → b = 1 + a → a = b → empty :=
begin
  intro a0 b1 ab,
  subst a0, subst b1,
  state,
  contradiction
end

example (a b c : nat) : a = 0 → 1 + a = b → a = b → empty :=
begin
  intro a0 b1 ab,
  subst a0 b1,
  state,
  contradiction
end

example (a b c : nat) : a = 0 → 1 + a = b → a = b → empty :=
begin
  intros,
  subst a b,
  state,
  contradiction
end
