open nat
open eq.ops

inductive even : nat → Type :=
| even_zero        : even zero
| even_succ_of_odd : ∀ {a}, odd a  → even (succ a)
with odd : nat → Type :=
| odd_succ_of_even : ∀ {a}, even a → odd (succ a)

example : even 1 → empty :=
begin
  intro He1,
  cases He1 with [a, Ho0],
  cases Ho0
end

example : even 3 → empty :=
begin
  intro He3,
  cases He3 with [a, Ho2],
  cases Ho2 with [a, He1],
  cases He1 with [a, Ho0],
  cases Ho0
end
