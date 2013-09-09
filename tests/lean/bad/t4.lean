Variable f {A : Type} (a : A) : A
Variable a : Int
Definition tst : Bool := (fun x, (f x) > 10) a
(*
The definition above should create the following problem for the new elaborator engine:

Definition tst : Int := (fun x : _, ((choice Nat::lt Int::lt Real::lt) (f _ x) ((choice id nat_to_int real_to_int) 10))) a

The first choice is generated because > is an overloaded notation.

The second choice is generated because we have coercions from nat->int
and nat->real, and it is unclear which one we need until we select the overload.
*)

(* Workaround: again add coercion manually *)
Definition tst : Bool := (fun x, (f x) > (nat_to_int 10)) a
