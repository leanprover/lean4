Import Int.
Variable list : Type -> Type
Variable nil  {A : Type} : list A
Variable cons {A : Type} (head : A) (tail : list A) : list A
Variables a b : Int
Variables n m : Nat
Definition l1 : list Int := cons a (cons b (cons n nil))
Definition l2 : list Int := cons a (cons n (cons b nil))
Check cons a (cons b (cons n nil))
