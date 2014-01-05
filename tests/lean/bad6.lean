import Int.
import Real.
variable f {A : Type} (a : A) : A
variable a : Int
variable b : Real
definition tst : Bool := (fun x y, (f x) > (f y)) a b
