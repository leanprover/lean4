import data.nat.basic data.prod
open prod

namespace nat
  definition brec_on {C : nat → Type} (n : nat) (F : Π (n : nat), @below C n → C n) : C n :=
  have general : C n × @below C n, from
    rec_on n
      (pair (F zero unit.star) unit.star)
      (λ (n₁ : nat) (r₁ : C n₁ × @below C n₁),
         have b : @below C (succ n₁), from
           r₁,
         have c : C (succ n₁), from
           F (succ n₁) b,
         pair c b),
  pr₁ general

  definition fib (n : nat) :=
  brec_on n (λ (n : nat),
    cases_on n
      (λ (b₀ : below zero), succ zero)
      (λ (n₁ : nat), cases_on n₁
          (λ b₁ : below (succ zero), succ zero)
          (λ (n₂ : nat) (b₂ : below (succ (succ n₂))), pr₁ b₂ + pr₁ (pr₂ b₂))))

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
