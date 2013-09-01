Variable f {A : Type} (a b : A) : A
Variable N : Type
Variable n1 : N
Variable n2 : N
Set lean::pp::implicit true
Show f n1 n2
Show f (fun x : N -> N, x) (fun y : _, y)
Variable EqNice {A : Type} (lhs rhs : A) : Bool
Infix 50 === : EqNice
Show n1 === n2
Check f n1 n2
Check Congr::explicit
Show f n1 n2
Variable a : N
Variable b : N
Variable c : N
Variable g : N -> N
Axiom H1 : a = b && b = c
Theorem Pr : (g a) = (g c) :=
    Congr (Refl g) (Trans (Conjunct1 H1) (Conjunct2 H1))
Show Environment 2
