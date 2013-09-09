Variable f {A : Type} (a b : A) : Bool
Variable a : Int
Variable b : Real
Definition tst : Bool := (fun x y, f x y) a b
(*
The example above demonstrates that may not be easy to eagerly create
choice constructs that cover all needed coercions.

The variables `a` and `b` have type Int and Real respectively.
Since the type of the function is not known at compilation time, we
add choice constructs that accomodate possible coercions.
So, we get the problem:

Definition tst : Bool := (fun (x : _) (y : _), f _ x y)
                         ((choice id int_to_real a))
                         b
*)
Definition tst1 : Bool := (fun x y, f x y) (int_to_real a) b
Set pp::coercion true
Set pp::implicit true
Show Environment 1
(*
It is unclear how to implement a simple elaboration problem generator that will produce
a problem that has the following solution.
*)
Definition tst2 : Bool := (fun x y, f (int_to_real x) y) a b
Show Environment 1
