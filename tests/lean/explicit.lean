import Int.
variable f {A : Type} : A -> A -> A
variable module::g {A : Type} : A -> A -> A
check @f
check module::@g
variable h::1 {A B : Type} : A -> B -> A
check h::1::explicit
variable @h : Int -> Int
variable h {A B : Type} : A -> B -> A