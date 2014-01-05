-- "Type casting" library.

-- The cast operator allows us to cast an element of type A
-- into B if we provide a proof that types A and B are equal.
Variable cast {A B : (Type U)} : A == B → A → B.

-- The CastEq axiom states that for any cast of x is equal to x.
Axiom CastEq  {A B : (Type U)} (H : A == B) (x : A) : x == cast H x.

-- The CastApp axiom "propagates" the cast over application
Axiom CastApp {A A' : (Type U)} {B : A → (Type U)} {B' : A' → (Type U)}
              (H1 : (Π x : A, B x) == (Π x : A', B' x)) (H2 : A == A')
              (f : Π x : A, B x) (x : A) :
    cast H1 f (cast H2 x) == f x.

-- If two (dependent) function spaces are equal, then their domains are equal.
Axiom DomInj {A A' : (Type U)} {B : A → (Type U)} {B' : A' → (Type U)}
             (H : (Π x : A, B x) == (Π x : A', B' x)) :
    A == A'.

-- If two (dependent) function spaces are equal, then their ranges are equal.
Axiom RanInj {A A' : (Type U)} {B : A → (Type U)} {B' : A' → (Type U)}
             (H : (Π x : A, B x) == (Π x : A', B' x)) (a : A) :
    B a == B' (cast (DomInj H) a).
