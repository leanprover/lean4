open bool nat

definition is_eq (a b : nat) : bool :=
nat.rec_on a
  (λ b, nat.cases_on b tt (λb₁, ff))
  (λ a₁ r₁ b, nat.cases_on b ff (λb₁, r₁ b₁))
  b

example : is_eq 3 3 = tt :=
rfl

example : is_eq 3 5 = ff :=
rfl

theorem eq.to_is_eq (a b : nat) (H : a = b) : is_eq a b = tt :=
have aux : is_eq a a = tt, from
  nat.rec_on a
    rfl
    (λ (a₁ : nat) (ih : is_eq a₁ a₁ = tt), ih),
H ▸ aux
