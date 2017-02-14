example (f : nat → nat) (p : nat → Prop)
        (h₁ : ∀ x, f (nat.succ x) = 1)
        (h₂ : ¬ p 0)
        (a : nat)
        (h₃ : p (f a)) : f (f a) = 1 :=
begin
  cases f a,
  contradiction,
  apply h₁
end
