import data.nat.basic data.bool
open bool nat eq.ops
attribute nat.rec_on [reducible]

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
  nat.induction_on a
    rfl
    (λ (a₁ : nat) (ih : is_eq a₁ a₁ = tt), ih),
H ▸ aux

theorem is_eq.to_eq (a b : nat) : is_eq a b = tt → a = b :=
nat.induction_on a
  (λb, nat.cases_on b (λh, rfl) (λb₁ H, absurd H !ff_ne_tt))
  (λa₁ (ih : ∀b, is_eq a₁ b = tt → a₁ = b) (b : nat),
    nat.cases_on b
      (λ (H  : is_eq (succ a₁) zero = tt), absurd H !ff_ne_tt)
      (λb₁ (H : is_eq (succ a₁) (succ b₁) = tt),
         have aux : a₁ = b₁, from ih b₁ H,
         aux ▸ rfl))
  b
