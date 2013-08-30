
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
Check Congr
Show f n1 n2
Theorem CongrI {A : Type u} {B : A → Type u} {f g : Π x : A, B x} {a b : A} (H1 : f = g) (H2 : a = b) : (f a) = (g b) :=
        Congr A B f g a b H1 H2
Theorem TransI {A : Type u} {a b c : A} (H1 : a = b) (H2 : b = c) : a = c :=
        Trans A a b c H1 H2
Theorem ReflI  {A : Type u} (a : A) : a = a :=
        Refl A a
Theorem SymmI  {A : Type u} {a b : A} (H : a = b) : b = a :=
        Symm A a b H
Theorem Conj1I {a b : Bool} (H : a && b) : a :=
        Conjunct1 a b H
Theorem Conj2I {a b : Bool} (H : a && b) : b :=
        Conjunct2 a b H
Variable a : N
Variable b : N
Variable c : N
Variable g : N -> N
Axiom H1 : a = b && b = c
Theorem Pr : (g a) = (g c) :=
    CongrI (ReflI g) (TransI (Conj1I H1) (Conj2I H1))
Show Environment 1


