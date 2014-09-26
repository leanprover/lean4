set_option pp.notation false
definition Prop := Type.{0}
variable eq {A : Type} : A → A → Prop
infixl `=`:50 := eq

variable N : Type.{1}
variable z : N
variable o : N
variable b : N

notation 0 := z
notation 1 := o

check 1
check 0

variable G : Type.{1}
variable gz : G
variable a  : G

notation 0 := gz

check 0 = a
check b = 0
