import standard
using num tactic
variable p : num → num → num → Bool
axiom H1 : ∃ x y z, p x y z
axiom H2 : ∀ {x y z : num}, p x y z → p x x x
theorem tst : ∃ x, p x x x
:= obtains a b c H [fact], from H1,
     by (apply exists_intro; apply H2; eassumption)
