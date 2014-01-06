import Int.
variable list : Type -> Type
variable nil  {A : Type} : list A
variable cons {A : Type} (head : A) (tail : list A) : list A
definition n1 : list Int := cons (nat_to_int 10) nil
definition n2 : list Nat := cons 10 nil
definition n3 : list Int := cons 10 nil
definition n4 : list Int := nil
definition n5 : _ := cons 10 nil

set::option pp::coercion true
set::option pp::implicit true
print environment 1.