def f (a : nat) := (a, a)

example (a : nat) (h : (f a).1 ≠ a) : false :=
begin
  unfold_projs at h {md := semireducible},
  contradiction
end

example (a b : nat) (h₁ : a = b) (h₂ : (a, a).1 ≠ b) : false :=
begin
  unfold_projs at h₁ h₂,
  contradiction
end

example (a b : nat) (h₁ : a = b) (h₂ : a ≠ b) : (false, true).1 :=
begin
  unfold_projs at *,
  contradiction
end

example (a b : nat) (h₁ : a = b) (h₂ : a ≠ b) : false :=
begin
  fail_if_success {unfold_projs at *},
  contradiction
end
