-- Axioms and theorems for casting and heterogenous equality
import macros

-- In the following definitions the type of A and B cannot be (Type U)
-- because A = B would be @eq (Type U+1) A B, and
-- the type of eq is (∀T : (Type U), T → T → bool).
-- So, we define M a universe smaller than U.
universe M ≥ 1
definition TypeM := (Type M)

variable cast {A B : (Type M)} : A = B → A → B

axiom cast_heq {A B : (Type M)} (H : A = B) (a : A) : cast H a == a

axiom hsymm {A B : (Type U)} {a : A} {b : B} : a == b → b == a

axiom htrans {A B C : (Type U)} {a : A} {b : B} {c : C} : a == b → b == c → a == c

axiom hcongr {A A' : (Type U)} {B : A → (Type U)} {B' : A' → (Type U)} {f : ∀ x, B x} {f' : ∀ x, B' x} {a : A} {a' : A'} :
      f == f' → a == a' → f a == f' a'

axiom hfunext {A A' : (Type M)} {B : A → (Type U)} {B' : A' → (Type U)} {f : ∀ x, B x} {f' : ∀ x, B' x} :
      A = A' → (∀ x x', x == x' → f x == f' x') → f == f'

theorem hsfunext {A : (Type M)} {B B' : A → (Type U)} {f : ∀ x, B x} {f' : ∀ x, B' x} :
      (∀ x, f x == f' x) → f == f'
:= λ Hb,
     hfunext (refl A) (λ (x x' : A) (Hx : x == x'),
                   let s1 : f x   == f' x  := Hb x,
                       s2 : f' x  == f' x' := hcongr (hrefl f') Hx
                   in htrans s1 s2)

theorem hallext {A A' : (Type M)} {B : A → Bool} {B' : A' → Bool}
                (Ha : A = A') (Hb : ∀ x x', x == x' → B x = B' x') : (∀ x, B x) = (∀ x, B' x)
:= boolext
     (assume (H : ∀ x : A, B x),
        take x' : A', (Hb (cast (symm Ha) x') x' (cast_heq (symm Ha) x')) ◂ (H (cast (symm Ha) x')))
     (assume (H : ∀ x' : A', B' x'),
        take x : A, (symm (Hb x (cast Ha x) (hsymm (cast_heq Ha x)))) ◂ (H (cast Ha x)))

theorem cast_app {A A' : (Type M)} {B : A → (Type M)} {B' : A' → (Type M)}
                 (f : ∀ x, B x) (a : A) (Ha : A = A') (Hb : (∀ x, B x) = (∀ x, B' x)) :
      cast Hb f (cast Ha a) == f a
:= let s1 : cast Hb f == f  := cast_heq Hb f,
       s2 : cast Ha a == a  := cast_heq Ha a
   in hcongr s1 s2

-- The following theorems can be used as rewriting rules

theorem cast_eq {A : (Type M)} (H : A = A) (a : A) : cast H a = a
:= to_eq (cast_heq H a)

theorem cast_trans {A B C : (Type M)} (Hab : A = B) (Hbc : B = C) (a : A) : cast Hbc (cast Hab a) = cast (trans Hab Hbc) a
:= let s1 : cast Hbc (cast Hab a)  == cast Hab a              :=  cast_heq Hbc (cast Hab a),
       s2 : cast Hab a             == a                       :=  cast_heq Hab a,
       s3 : cast (trans Hab Hbc) a == a                       :=  cast_heq (trans Hab Hbc) a,
       s4 : cast Hbc (cast Hab a)  == cast (trans Hab Hbc) a  :=  htrans (htrans s1 s2) (hsymm s3)
   in to_eq s4

theorem cast_pull {A : (Type M)} {B B' : A → (Type M)}
                 (f : ∀ x, B x) (a : A) (Hb : (∀ x, B x) = (∀ x, B' x)) (Hba : (B a) = (B' a)) :
      cast Hb f a = cast Hba (f a)
:= let s1 : cast Hb f a    == f a    :=  hcongr (cast_heq Hb f) (hrefl a),
       s2 : cast Hba (f a) == f a    :=  cast_heq Hba (f a)
   in to_eq (htrans s1 (hsymm s2))

-- The following axiom is not very useful, since the resultant
-- equality is actually (@eq TypeM (∀ x, B x) (∀ x, B' x)).
-- This is the case even if A, A', B and B' live in smaller universes (e.g., Type)
-- To support this kind of axiom, it seems we have two options:
--    1) Universe level parameters like Agda
--    2) Axiom schema/template, where we create instances of hpiext for different universes.
--       BTW, this is essentially what Coq does since the levels are implicit in Coq.
-- axiom hpiext {A A' : TypeM} {B : A → TypeM} {B' : A' → TypeM} :
--      A = A' → (∀ x x', x == x' → B x = B' x') → (∀ x, B x) = (∀ x, B' x)
