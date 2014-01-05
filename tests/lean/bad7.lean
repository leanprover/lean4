import Real.
variable f {A : Type} (a b : A) : Bool
variable a : Int
variable b : Real
definition tst : Bool := (fun x y, f x y) a b
print environment 1
