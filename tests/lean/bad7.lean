Import Real.
Variable f {A : Type} (a b : A) : Bool
Variable a : Int
Variable b : Real
Definition tst : Bool := (fun x y, f x y) a b
Show Environment 1
