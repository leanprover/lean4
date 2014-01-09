-- "Type casting" library.

-- Heterogeneous substitution
axiom hsubst {A B : TypeU} {a : A} {b : B} (P : ∀ (T : TypeU), T -> Bool) : P A a → a == b → P B b

universe M >= 1
universe U >= M + 1
definition TypeM := (Type M)

-- Type equality axiom, if two values are equal, then their types are equal
theorem type_eq {A B : TypeM} {a : A} {b : B} (H : a == b) : A == B
:= hsubst (λ (T : TypeU) (x : T), A == T) (refl A) H

-- Heterogenous symmetry
theorem hsymm {A B : TypeU} {a : A} {b : B} (H : a == b) : b == a
:= hsubst (λ (T : TypeU) (x : T), x == a) (refl a) H

-- Heterogenous transitivity
theorem htrans {A B C : TypeU} {a : A} {b : B} {c : C} (H1 : a == b) (H2 : b == c) : a == c
:= hsubst (λ (T : TypeU) (x : T), a == x) H1 H2

-- The cast operator allows us to cast an element of type A
-- into B if we provide a proof that types A and B are equal.
variable cast {A B : TypeU} : A == B → A → B

-- The CastEq axiom states that for any cast of x is equal to x.
axiom cast_eq {A B : TypeU} (H : A == B) (x : A) : x == cast H x

-- The CastApp axiom "propagates" the cast over application
axiom cast_app {A A' : TypeU} {B : A → TypeU} {B' : A' → TypeU}
                (H1 : (∀ x : A, B x) == (∀ x : A', B' x)) (H2 : A == A')
                (f : ∀ x : A, B x) (x : A) :
    cast H1 f (cast H2 x) == f x

-- Heterogeneous congruence
theorem hcongr
            {A A' : TypeM} {B : A → TypeM} {B' : A' → TypeM}
            {f : ∀ x : A, B x} {g : ∀ x : A', B' x} {a : A} {b : A'}
            (H1 : f == g)
            (H2 : a == b)
         : f a == g b
:= let L1 : A  == A'                             := type_eq H2,
       L2 : A' == A                              := symm L1,
       b' : A                                    := cast L2 b,
       L3 : b == b'                              := cast_eq L2 b,
       L4 : a == b'                              := htrans H2 L3,
       L5 : f a == f b'                          := congr2 f L4,
       S1 : (∀ x : A', B' x) == (∀ x : A, B x) := symm (type_eq H1),
       g' : (∀ x : A, B x)                      := cast S1 g,
       L6 : g == g'                              := cast_eq S1 g,
       L7 : f == g'                              := htrans H1 L6,
       L8 : f b' == g' b'                        := congr1 b' L7,
       L9 : f a == g' b'                         := htrans L5 L8,
      L10 : g' b' == g b                         := cast_app S1 L2 g b
   in htrans L9 L10

exit -- Stop here, the following axiom is not sound

-- The following axiom is unsound when we treat Pi and
-- forall as the "same thing". The main problem is the
-- rule that says (Pi x : A, B) has type Bool if B has type Bool instead of
-- max(typeof(A), typeof(B))
--
-- Here is the problematic axiom
-- If two (dependent) function spaces are equal, then their domains are equal.
axiom dominj {A A' : (Type U)} {B : A → (Type U)} {B' : A' → (Type U)}
             (H : (∀ x : A, B x) == (∀ x : A', B' x)) :
      A == A'

-- Here is a derivation of false using the dominj axiom
theorem unsat : false :=
let L1 : (∀ x : true, true)                         := (λ x : true,  trivial),
    L2 : (∀ x : false, true)                        := (λ x : false, trivial),
    -- When we keep Pi/forall as different things, the following two steps can't be used
    L3 : (∀ x : true, true) = true                  := eqt_intro L1,
    L4 : (∀ x : false, true) = true                 := eqt_intro L2,
    L5 : (∀ x : true, true) = (∀ x : false, true)  := trans L3 (symm L4),
    L6 : true = false                                := dominj L5
in L6
