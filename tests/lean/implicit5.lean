Variable f {A : Type} (a1 a2 : A) : A
Variable g : Int -> Int -> Int
Variable h : Int -> Int -> Real -> Int
Variable p {A B : Type} (a1 a2 : A) (b : B) : A
Infix ++ : f
Infix ++ : g
Infix ++ : h
Infix ++ : p
Variable p2 {A B : Type} (a1 a2 : A) (b : B) {C : Type} (c : C) : A
Infix ++ : p2
