def foo (a b : nat) : Prop :=
a = 0 ∧ b = 0

attribute [simp] foo

example (p : nat → Prop) (a b : nat) : foo a b → p (a + b) → p 0 :=
begin
  intros h₁ h₂,
  simp_all
end
