import data.list
open list
set_option blast.strategy "preprocess"

example (p : Prop) (a b c : nat) : [a, b, c] = [] → p :=
by blast

set_option blast.strategy "simple"

lemma l1 (a b c d e f : nat) : [a, b, c] = [d, e, f] → a = d ∧ b = e ∧ c = f :=
by blast

reveal l1
print l1
