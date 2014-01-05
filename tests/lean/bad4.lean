import Int.
variable f {A : Type} (a : A) : A
variable a : Int
definition tst : Bool := (fun x, (f x) > 10) a
