variable f {A : Type} (a b : A) : A
variable N : Type
variable n1 : N
variable n2 : N
set_option lean::pp::implicit true
print f n1 n2
print f (fun x : N -> N, x) (fun y : _, y)
variable EqNice {A : Type} (lhs rhs : A) : Bool
infix 50 === : EqNice
print n1 === n2
check f n1 n2
check @congr
print f n1 n2
variable a : N
variable b : N
variable c : N
variable g : N -> N
axiom H1 : a = b && b = c
theorem Pr : (g a) = (g c) :=
    congr (refl g) (trans (and_eliml H1) (and_elimr H1))
print environment 2
