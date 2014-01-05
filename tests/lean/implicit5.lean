import Int.
import Real.
variable f {A : Type} (a1 a2 : A) : A
variable g : Int -> Int -> Int
variable h : Int -> Int -> Real -> Int
variable p {A B : Type} (a1 a2 : A) (b : B) : A
infix ++ : f
infix ++ : g
infix ++ : h
infix ++ : p
variable p2 {A B : Type} (a1 a2 : A) (b : B) {C : Type} (c : C) : A
infix ++ : p2
