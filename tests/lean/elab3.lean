Variable C : Pi (A B : Type) (H : A = B) (a : A), B

Variable D : Pi (A A' : Type) (B : A -> Type) (B' : A' -> Type) (H : (Pi x : A, B x) = (Pi x : A', B' x)), A = A'

Variable R : Pi (A A' : Type) (B : A -> Type) (B' : A' -> Type) (H : (Pi x : A, B x) = (Pi x : A', B' x)) (a : A),
             (B a) = (B' (C A A' (D A A' B B' H) a))

Theorem R2 : Pi (A1 A2 B1 B2 : Type) (H : (A1 -> B1) = (A2 -> B2)) (a : A1), B1 = B2 :=
    fun A1 A2 B1 B2 H a,
        R _ _ _ _ H a

print Environment 1.