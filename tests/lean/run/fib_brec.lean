import data.nat.basic data.prod
open prod

namespace nat
  namespace manual
  definition brec_on {C : nat → Type} (n : nat) (F : Π (n : nat), @nat.below C n → C n) : C n :=
  have general : C n × @nat.below C n, from
    nat.rec_on n
      (pair (F zero poly_unit.star) poly_unit.star)
      (λ (n₁ : nat) (r₁ : C n₁ × @nat.below C n₁),
         have b : @nat.below C (succ n₁), from
           r₁,
         have c : C (succ n₁), from
           F (succ n₁) b,
         pair c b),
  pr₁ general
  end manual

  definition fib (n : nat) :=
  nat.brec_on n (λ (n : nat),
    nat.cases_on n
      (λ (b₀ : nat.below 0), succ 0)
      (λ (n₁ : nat), nat.cases_on n₁
          (λ b₁ : nat.below (succ 0), succ zero)
          (λ (n₂ : nat) (b₂ : nat.below (succ (succ n₂))), pr₁ b₂ + pr₁ (pr₂ b₂))))

  theorem fib_0 : fib 0 = 1 :=
  rfl

  theorem fib_1 : fib 1 = 1 :=
  rfl

  theorem fib_s_s (n : nat) : fib (succ (succ n)) = fib (succ n) + fib n :=
  rfl

  example : fib 5 = 8 :=
  rfl

  example : fib 9 = 55 :=
  rfl
end nat
