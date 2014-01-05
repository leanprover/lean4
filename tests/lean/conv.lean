import Int.
definition id (A : Type) : (Type U) := A.
variable p : (Int -> Int) -> Bool.
check fun (x : id Int), x.
variable f : (id Int) -> (id Int).
check p f.

definition c (A : (Type 3)) : (Type 3) := (Type 1).
variable g : (c (Type 2)) -> Bool.
variable a : (c (Type 1)).
check g a.

definition c2 {T : Type} (A : (Type 3)) (a : T) : (Type 3) := (Type 1)
variable b : Int
check @c2
variable g2 : (c2 (Type 2) b) -> Bool
check g2
variable a2 : (c2 (Type 1) b).
check g2 a2
check fun x : (c2 (Type 1) b), g2 x