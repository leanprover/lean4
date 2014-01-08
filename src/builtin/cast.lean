-- "Type casting" library.

-- The cast operator allows us to cast an element of type A
-- into B if we provide a proof that types A and B are equal.
variable cast {A B : (Type U)} : A == B → A → B.

-- The CastEq axiom states that for any cast of x is equal to x.
axiom cast::eq {A B : (Type U)} (H : A == B) (x : A) : x == cast H x.

-- The CastApp axiom "propagates" the cast over application
axiom cast::app {A A' : (Type U)} {B : A → (Type U)} {B' : A' → (Type U)}
              (H1 : (∀ x : A, B x) == (∀ x : A', B' x)) (H2 : A == A')
              (f : ∀ x : A, B x) (x : A) :
    cast H1 f (cast H2 x) == f x.

-- If two (dependent) function spaces are equal, then their domains are equal.
axiom dominj {A A' : (Type U)} {B : A → (Type U)} {B' : A' → (Type U)}
             (H : (∀ x : A, B x) == (∀ x : A', B' x)) :
    A == A'.

-- If two (dependent) function spaces are equal, then their ranges are equal.
axiom raninj {A A' : (Type U)} {B : A → (Type U)} {B' : A' → (Type U)}
             (H : (∀ x : A, B x) == (∀ x : A', B' x)) (a : A) :
    B a == B' (cast (dominj H) a).
