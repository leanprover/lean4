import Int.
variable list : Type -> Type
variable nil  {A : Type} : list A
variable cons {A : Type} (head : A) (tail : list A) : list A
variables a b : Int
variables n m : Nat
definition l1 : list Int := cons a (cons b (cons n nil))
definition l2 : list Int := cons a (cons n (cons b nil))
check cons a (cons b (cons n nil))
