import data.list
open list

example (p : Prop) (a b c : nat) : [a, b, c] = [] → p :=
by blast

lemma l1 (a b c d e f : nat) : [a, b, c] = [d, e, f] → a = d ∧ b = e ∧ c = f :=
by blast

reveal l1
print l1
