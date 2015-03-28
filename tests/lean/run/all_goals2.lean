import data.nat
open nat

attribute nat.add [unfold-c 2]
attribute nat.rec_on [unfold-c 2]

namespace tactic
  definition then_all (t1 t2 : tactic) : tactic :=
  focus (t1 ; all_goals t2)
  infixl `;;`:15 := tactic.then_all
end tactic

open tactic
example (a b c : nat) : (a + 0 = 0 + a ∧ b + 0 = 0 + b) ∧ c = c :=

begin
  apply and.intro,
  apply and.intro ;; (esimp[of_num]; state; rewrite zero_add),
  apply rfl
end
