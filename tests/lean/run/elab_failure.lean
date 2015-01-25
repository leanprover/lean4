import data.nat.basic data.bool
open bool nat
attribute nat.rec_on [reducible]
definition is_eq (a b : nat) : bool :=
nat.rec_on a
  (λ b, nat.cases_on b tt (λb₁, ff))
  (λ a₁ r₁ b, nat.cases_on b ff (λb₁, r₁ b₁))
  b

example (a₁ : nat) (b : nat) : true :=
@nat.cases_on (λ (n : nat), true) b
  true.intro
  (λ (b₁ : _),
     have aux : is_eq a₁ b₁ = is_eq (succ a₁) (succ b₁), from rfl,
     true.intro)
