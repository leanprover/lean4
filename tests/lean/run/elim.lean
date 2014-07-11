import standard
using num
variable p : num → num → num → Bool
axiom H1 : ∃ x y z, p x y z
axiom H2 : ∀ {x y z : num}, p x y z → p x x x
theorem tst : ∃ x, p x x x
:= obtains a b c H, from H1, exists_intro a (H2 H)
