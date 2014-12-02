open nat
open eq.ops

inductive even : nat → Prop :=
even_zero        : even zero,
even_succ_of_odd : ∀ {a}, odd a  → even (succ a)
with odd : nat → Prop :=
odd_succ_of_even : ∀ {a}, even a → odd (succ a)

example : even 1 → false :=
begin
  intro H,
  cases H with (a, ho),
  assert (Hz : odd zero),
  apply (a_eq ▸ ho),
  inversion Hz
end
