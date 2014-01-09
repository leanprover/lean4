variable C {A B : Type} (H : A = B) (a : A) : B

variable D {A A' : Type} {B : A -> Type} {B' : A' -> Type} (H : (forall x : A, B x) = (forall x : A', B' x)) : A = A'

variable R {A A' : Type} {B : A -> Type} {B' : A' -> Type} (H : (forall x : A, B x) = (forall x : A', B' x)) (a : A) :
             (B a) = (B' (C (D H) a))

theorem R2 : forall (A1 A2 B1 B2 : Type) (H : (A1 -> B1) = (A2 -> B2)) (a : A1), B1 = B2 :=
    fun A1 A2 B1 B2 H a, R H a

set_option pp::implicit true
print environment 7.
