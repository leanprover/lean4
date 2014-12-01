prelude set_option pp.notation false
definition Prop := Type.{0}
constant eq {A : Type} : A → A → Prop
infixl `=`:50 := eq

constant N : Type.{1}
constant z : N
constant o : N
constant b : N

notation 0 := z
notation 1 := o

check 1
check 0

constant G : Type.{1}
constant gz : G
constant a  : G

notation 0 := gz

check 0 = a
check b = 0
