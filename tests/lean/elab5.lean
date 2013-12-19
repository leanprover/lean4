Variable C {A B : Type} (H : A = B) (a : A) : B

Variable D {A A' : Type} {B : A -> Type} {B' : A' -> Type} (H : (Pi x : A, B x) = (Pi x : A', B' x)) : A = A'

Variable R {A A' : Type} {B : A -> Type} {B' : A' -> Type} (H : (Pi x : A, B x) = (Pi x : A', B' x)) (a : A) :
             (B a) = (B' (C (D H) a))

Theorem R2 : Pi (A1 A2 B1 B2 : Type), ((A1 -> B1) = (A2 -> B2)) -> A1 -> (B1 = B2) :=
    fun A1 A2 B1 B2 H a, R H a

SetOption pp::implicit true
Show Environment 7.
