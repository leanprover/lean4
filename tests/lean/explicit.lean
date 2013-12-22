Variable f {A : Type} : A -> A -> A
Variable module::g {A : Type} : A -> A -> A
Check @f
Check module::@g
Variable h::1 {A B : Type} : A -> B -> A
Check h::1::explicit
Variable @h : Int -> Int
Variable h {A B : Type} : A -> B -> A