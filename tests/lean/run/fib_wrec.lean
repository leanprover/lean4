import data.nat
open nat eq.ops

definition fib.F (n : nat) : (Π (m : nat), m < n → nat) → nat :=
nat.cases_on n
  (λ (f : Π (m : nat), m < zero → nat), succ zero)
  (λ (n₁ : nat), nat.cases_on n₁
    (λ (f : Π (m : nat), m < (succ zero) → nat), succ zero)
    (λ (n₂ : nat) (f : Π (m : nat), m < (succ (succ n₂)) → nat),
       have l₁ : succ n₂ < succ (succ n₂), from lt.base (succ n₂),
       have l₂ : n₂ < succ (succ n₂), from nat.lt_trans (lt.base n₂) l₁,
         f (succ n₂) l₁ + f n₂ l₂))

definition fib (n : nat) :=
well_founded.fix fib.F n

theorem fib.zero_eq : fib 0 = 1 :=
well_founded.fix_eq fib.F 0

theorem fib.one_eq  : fib 1 = 1 :=
well_founded.fix_eq fib.F 1

theorem fib.succ_succ_eq (n : nat) : fib (succ (succ n)) = fib (succ n) + fib n :=
well_founded.fix_eq fib.F (succ (succ n))

example : fib 5 = 8 :=
rfl

example : fib 6 = 13 :=
rfl
