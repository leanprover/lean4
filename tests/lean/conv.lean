Import int.
Definition id (A : Type) : (Type U) := A.
Variable p : (Int -> Int) -> Bool.
Check fun (x : id Int), x.
Variable f : (id Int) -> (id Int).
Check p f.

Definition c (A : (Type 3)) : (Type 3) := (Type 1).
Variable g : (c (Type 2)) -> Bool.
Variable a : (c (Type 1)).
Check g a.

Definition c2 {T : Type} (A : (Type 3)) (a : T) : (Type 3) := (Type 1)
Variable b : Int
Check @c2
Variable g2 : (c2 (Type 2) b) -> Bool
Check g2
Variable a2 : (c2 (Type 1) b).
Check g2 a2
Check fun x : (c2 (Type 1) b), g2 x