set_option pp.implicit true
set_option pp.notation false
definition ideq : Π {A : Type} {a b : A}, a = b → a = b,
ideq H := H
