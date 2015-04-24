open nat

example (a b : nat) (P : nat → Prop) (H₁ : a = b) (H₂ : P a) : P b :=
begin
  rewrite H₁ at *,
  exact H₂
end

example (a b : nat) (P : nat → Prop) (H₀ : a = 0 → b = 1) (H₁ : a = 0) (H₂ : P b) : P 1 :=
begin
  rewrite (H₀ H₁) at *,
  exact H₂
end

example (a c : nat) (P : nat → Prop) (H₁ : P a) (b : nat) (H₂ : a = b) (H₃ : b = c) : P c :=
begin
  rewrite H₂ at H₁,
  exact (eq.rec_on H₃ H₁)
end

example (a c : nat) (f : nat → nat → nat) (P : nat → Prop) (H₁ : P a) (b : nat) (d : nat) (H₂ : a = f b d) (H₃ : f b d = c)
        : P c :=
begin
  rewrite H₂ at H₁,
  exact (eq.rec_on H₃ H₁)
end
