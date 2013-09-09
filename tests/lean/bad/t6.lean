Variable f {A : Type} (a : A) : A
Variable a : Int
Variable b : Real
Definition tst : Bool := (fun x y, (f x) > (f y)) a b
(*
In the current version, the example above does not work without user's help.
We can compile this example into the following elaborator problem:

Definition tst : Bool := (fun (x : _) (y : _),
                           ((choice Nat::lt Int::lt Real::lt)
                            ((choice id nat_to_int nat_to_real int_to_real) (f _ x))
                            ((choice id nat_to_int nat_to_real int_to_real) (f _ y))))
                         a b

The first choice construct is generated because > is overloaded notation.

The second and third choices are selected because Nat::lt, Int::lt and
Real::lt expect Nat, Int and Real arguments respectively.
The type of the expressions (f _ x) and (f _ y) is unknown at problem generation time.
So, we create a choice with all relevant coercions. The choice `id` represents "no coercion" is
needed.
*)
Definition tst : Bool := (fun x y, (int_to_real (f x)) > (f y)) a b
