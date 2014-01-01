Import Int.
Import Real.
Variable f {A : Type} (a : A) : A
Variable a : Int
Variable b : Real
Definition tst : Bool := (fun x y, (f x) > (f y)) a b
