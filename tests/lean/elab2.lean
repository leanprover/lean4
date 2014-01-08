variable C : forall (A B : Type) (H : A = B) (a : A), B

variable D : forall (A A' : Type) (B : A -> Type) (B' : A' -> Type) (H : (forall x : A, B x) = (forall x : A', B' x)), A = A'

variable R : forall (A A' : Type) (B : A -> Type) (B' : A' -> Type) (H : (forall x : A, B x) = (forall x : A', B' x)) (a : A),
             (B a) = (B' (C A A' (D A A' B B' H) a))

theorem R2 (A A' B B' : Type) (H : (A -> B) = (A' -> B')) (a : A) : B = B' := R _ _ _ _ H a

print environment 1

theorem R3 : forall (A1 A2 B1 B2 : Type) (H : (A1 -> B1) = (A2 -> B2)) (a : A1), B1 = B2 :=
    fun (A1 A2 B1 B2 : Type) (H : (A1 -> B1) = (A2 -> B2)) (a : A1),
        R _ _ _ _ H a

theorem R4 : forall (A1 A2 B1 B2 : Type) (H : (A1 -> B1) = (A2 -> B2)) (a : A1), B1 = B2 :=
    fun (A1 A2 B1 B2 : Type) (H : (A1 -> B1) = (A2 -> B2)) (a : _),
        R _ _ _ _ H a

theorem R5 : forall (A1 A2 B1 B2 : Type) (H : (A1 -> B1) = (A2 -> B2)) (a : A1), B1 = B2 :=
    fun (A1 A2 B1 B2 : Type) (H : _) (a : _),
        R _ _ _ _ H a

print environment 1
