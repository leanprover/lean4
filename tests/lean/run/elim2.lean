import logic
open tactic
constant p : num → num → num → Prop
axiom H1 : ∃ x y z, p x y z
axiom H2 : ∀ {x y z : num}, p x y z → p x x x
theorem tst : ∃ x, p x x x
:= obtain a b c H, from H1,
     by (apply exists.intro; apply H2; eassumption)
