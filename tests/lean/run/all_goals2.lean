import data.nat
open nat

attribute nat.add [unfold 2]
attribute nat.rec_on [unfold 2]

infixl `;`:15 := tactic.and_then

namespace tactic
  definition then_all (t1 t2 : tactic) : tactic :=
  focus (t1 ; all_goals t2)
end tactic

tactic_infixl `;;`:15 := tactic.then_all

open tactic
example (a b c : nat) : (a + 0 = 0 + a ∧ b + 0 = 0 + b) ∧ c = c :=

begin
  apply and.intro,
  apply and.intro ;; (esimp[of_num]; state; rewrite zero_add),
  apply rfl
end
