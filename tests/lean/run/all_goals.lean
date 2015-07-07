import data.nat
open nat

attribute nat.add [unfold 2]
attribute nat.rec_on [unfold 2]

example (a b c : nat) : a + 0 = 0 + a ∧ b + 0 = 0 + b :=
begin
  apply and.intro,
  all_goals esimp[of_num],
  all_goals (state; rewrite zero_add)
end
