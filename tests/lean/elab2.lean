
Variable C : Pi (A B : Type) (H : A = B) (a : A), B

Variable D : Pi (A A' : Type) (B : A -> Type) (B' : A' -> Type) (H : (Pi x : A, B x) = (Pi x : A', B' x)), A = A'

Variable R : Pi (A A' : Type) (B : A -> Type) (B' : A' -> Type) (H : (Pi x : A, B x) = (Pi x : A', B' x)) (a : A),
             (B a) = (B' (C A A' (D A A' B B' H) a))

Theorem R2 (A A' B B' : Type) (H : (A -> B) = (A' -> B')) (a : A) : B = B' := R _ _ _ _ H a

Show Environment 1

Theorem R3 : Pi (A1 A2 B1 B2 : Type) (H : (A1 -> B1) = (A2 -> B2)) (a : A1), B1 = B2 :=
    fun (A1 A2 B1 B2 : Type) (H : (A1 -> B1) = (A2 -> B2)) (a : A1),
        R _ _ _ _ H a

Theorem R4 : Pi (A1 A2 B1 B2 : Type) (H : (A1 -> B1) = (A2 -> B2)) (a : A1), B1 = B2 :=
    fun (A1 A2 B1 B2 : Type) (H : (A1 -> B1) = (A2 -> B2)) (a : _),
        R _ _ _ _ H a

Theorem R5 : Pi (A1 A2 B1 B2 : Type) (H : (A1 -> B1) = (A2 -> B2)) (a : A1), B1 = B2 :=
    fun (A1 A2 B1 B2 : Type) (H : _) (a : _),
        R _ _ _ _ H a

Show Environment 1
