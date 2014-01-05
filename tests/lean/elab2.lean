variable C : Pi (A B : Type) (H : A = B) (a : A), B

variable D : Pi (A A' : Type) (B : A -> Type) (B' : A' -> Type) (H : (Pi x : A, B x) = (Pi x : A', B' x)), A = A'

variable R : Pi (A A' : Type) (B : A -> Type) (B' : A' -> Type) (H : (Pi x : A, B x) = (Pi x : A', B' x)) (a : A),
             (B a) = (B' (C A A' (D A A' B B' H) a))

theorem R2 (A A' B B' : Type) (H : (A -> B) = (A' -> B')) (a : A) : B = B' := R _ _ _ _ H a

print environment 1

theorem R3 : Pi (A1 A2 B1 B2 : Type) (H : (A1 -> B1) = (A2 -> B2)) (a : A1), B1 = B2 :=
    fun (A1 A2 B1 B2 : Type) (H : (A1 -> B1) = (A2 -> B2)) (a : A1),
        R _ _ _ _ H a

theorem R4 : Pi (A1 A2 B1 B2 : Type) (H : (A1 -> B1) = (A2 -> B2)) (a : A1), B1 = B2 :=
    fun (A1 A2 B1 B2 : Type) (H : (A1 -> B1) = (A2 -> B2)) (a : _),
        R _ _ _ _ H a

theorem R5 : Pi (A1 A2 B1 B2 : Type) (H : (A1 -> B1) = (A2 -> B2)) (a : A1), B1 = B2 :=
    fun (A1 A2 B1 B2 : Type) (H : _) (a : _),
        R _ _ _ _ H a

print environment 1
