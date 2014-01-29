-- Heterogenous equality
variable heq {A B : TypeU} : A → B → Bool
infixl 50 == : heq

axiom heq_eq {A : TypeU} (a b : A) : a == b ↔ a = b

theorem to_eq {A : TypeU} {a b : A} (H : a == b) : a = b
:= (heq_eq a b) ◂ H

theorem to_heq {A : TypeU} {a b : A} (H : a = b) : a == b
:= (symm (heq_eq a b)) ◂ H

theorem hrefl {A : TypeU} (a : A) : a == a
:= to_heq (refl a)

theorem heqt_elim {a : Bool} (H : a == true) : a
:= eqt_elim (to_eq H)

axiom hsymm {A B : TypeU} {a : A} {b : B} : a == b → b == a

axiom htrans {A B C : TypeU} {a : A} {b : B} {c : C} : a == b → b == c → a == c

axiom hcongr {A A' : TypeU} {B : A → TypeU} {B' : A' → TypeU} {f : ∀ x, B x} {f' : ∀ x, B' x} {a : A} {a' : A'} :
      f == f' → a == a' → f a == f' a'

universe M ≥ 1
universe U ≥ M + 1
definition TypeM := (Type M)

-- In the following definitions the type of A and A' cannot be TypeU
-- because A = A' would be @eq (Type U+1) A A', and
-- the type of eq is (∀T : (Type U), T → T → bool).
-- So, we define M a universe smaller than U.

axiom hfunext {A A' : TypeM} {B : A → TypeU} {B' : A' → TypeU} {f : ∀ x, B x} {f' : ∀ x, B' x} :
      A = A' → (∀ x x', x == x' → f x == f' x') → f == f'

theorem hsfunext {A : TypeM} {B B' : A → TypeU} {f : ∀ x, B x} {f' : ∀ x, B' x} :
      (∀ x, f x == f' x) → f == f'
:= λ Hb,
     hfunext (refl A) (λ (x x' : A) (Hx : x == x'),
                   let s1 : f x   == f' x  := Hb x,
                       s2 : f' x  == f' x' := hcongr (hrefl f') Hx
                   in htrans s1 s2)

axiom hallext {A A' : TypeM} {B : A → Bool} {B' : A' → Bool} :
      A = A' → (∀ x x', x == x' → B x = B' x') → (∀ x, B x) = (∀ x, B' x)

-- The following axiom is not very useful, since the resultant
-- equality is actually (@eq TypeM (∀ x, B x) (∀ x, B' x)).
-- This is the case even if A, A', B and B' live in smaller universes (e.g., Type)
-- To support this kind of axiom, it seems we have two options:
--    1) Universe level parameters like Agda
--    2) Axiom schema/template, where we create instances of hpiext for different universes.
--       BTW, this is essentially what Coq does since the levels are implicit in Coq.
-- axiom hpiext {A A' : TypeM} {B : A → TypeM} {B' : A' → TypeM} :
--      A = A' → (∀ x x', x == x' → B x = B' x') → (∀ x, B x) = (∀ x, B' x)
