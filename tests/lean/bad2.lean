Variable list : Type -> Type
Variable nil  {A : Type} : list A
Variable cons {A : Type} (head : A) (tail : list A) : list A
Definition n1 : list Int := cons (nat_to_int 10) nil
Definition n2 : list Nat := cons 10 nil
(*
The following example demonstrates that the expected type (list Int)
does not influece whether coercions are used or not.
*)
Definition n3 : list Int := cons 10 nil

(*
Here are some workarounds for the example above.
The 'let' construct is one of the main tools for providing
hints.
*)
Definition n3a : list Int :=
           let a : Int := 10
           in cons a nil

(* Solution b: we manually provide the coercion *)
Definition n3b : list Int := cons (nat_to_int 10) nil

(* The folowing example works *)
Definition n4 : list Int := nil

(*
The following example demonstrates that we do not do type inference.
In the current implementation, we first elaborate the type and
then the body.
*)
Definition n5 : _ := cons 10 nil

Set pp::coercion true
Set pp::implicit true
Show Environment 1.