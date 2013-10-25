Variable list : Type -> Type
Variable nil  {A : Type} : list A
Variable cons {A : Type} (head : A) (tail : list A) : list A
Definition n1 : list Int := cons (nat_to_int 10) nil
Definition n2 : list Nat := cons 10 nil
Definition n3 : list Int := cons 10 nil
Definition n4 : list Int := nil
Definition n5 : _ := cons 10 nil

Set pp::coercion true
Set pp::implicit true
Show Environment 1.