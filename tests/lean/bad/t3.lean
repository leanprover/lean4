Variable list : Type -> Type
Variable nil  {A : Type} : list A
Variable cons {A : Type} (head : A) (tail : list A) : list A
Variables a b : Int
Variables n m : Nat
(*
Here are other examples showing that coercions and implicit arguments
do not "interact well with each other" in the current implementation.
*)
Definition l1 : list Int := cons a (cons b (cons n nil))
Definition l2 : list Int := cons a (cons n (cons b nil))
Check cons a (cons b (cons n nil))
