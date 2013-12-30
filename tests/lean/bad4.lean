Import int.
Variable f {A : Type} (a : A) : A
Variable a : Int
Definition tst : Bool := (fun x, (f x) > 10) a
