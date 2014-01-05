variable f {A : Type} (a b : A) : A
variable N : Type
variable n1 : N
variable n2 : N
setoption lean::pp::implicit true
print f n1 n2
print f (fun x : N -> N, x) (fun y : _, y)
variable EqNice {A : Type} (lhs rhs : A) : Bool
infix 50 === : EqNice
print n1 === n2
check f n1 n2
check @Congr
print f n1 n2
variable a : N
variable b : N
variable c : N
variable g : N -> N
axiom H1 : a = b && b = c
theorem Pr : (g a) = (g c) :=
    Congr (Refl g) (Trans (Conjunct1 H1) (Conjunct2 H1))
print environment 2
