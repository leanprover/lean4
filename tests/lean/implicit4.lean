Variable f {A : Type}     (a1 a2 : A) {B : Type} (b1 b2 : B) : A
Variable g {A1 A2 : Type} (a1 : A1) (a2 : A2) {B : Type} (b : B) : A1
Variable p (a1 a2 : Int)  {B : Type} (b1 b2 b3 : B) : B
Variable h {A1 A2 : Type} (a1 : A1) (a2 : A2) (a3 : A2) : A1
Infix ++ : f
Infix ++ : g
Infix ++ : p
Infix ++ : h