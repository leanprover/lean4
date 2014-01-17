import macros

-- Heterogenous equality
variable heq {A B : TypeU} : A → B → Bool
infixl 50 == : heq

universe H ≥ 1
universe U ≥ H + 1
definition TypeH := (Type H)

axiom heq_eq {A : TypeH} (a : A) : a == a ↔ a = a

definition to_eq {A : TypeH} {a : A} (H : a == a) : a = a
:= (heq_eq a) ◂ H

definition to_heq {A : TypeH} {a : A} (H : a = a) : a == a
:= (symm (heq_eq a)) ◂ H

theorem hrefl {A : TypeH} (a : A) : a == a
:= to_heq (refl a)

axiom hsymm {A B : TypeH} {a : A} {b : B} : a == b → b == a

axiom htrans {A B C : TypeH} {a : A} {b : B} {c : C} : a == b → b == c → a == c

axiom hcongr {A A' : TypeH} {B : A → TypeH} {B' : A' → TypeH} {f : ∀ x, B x} {f' : ∀ x, B' x} {a : A} {a' : A'} :
      f == f' → a == a' → f a == f' a'

axiom hfunext {A A' : TypeH} {B : A → TypeH} {B' : A' → TypeH} {f : ∀ x, B x} {f' : ∀ x, B' x} :
      A = A' → (∀ x x', f x == f' x') → f == f'

axiom hpiext {A A' : TypeH} {B : A → TypeH} {B' : A' → TypeH} :
      A = A' → (∀ x x', B x == B' x') → (∀ x, B x) == (∀ x, B' x)

axiom hallext {A A' : TypeH} {B : A → Bool} {B' : A' → Bool} :
      A = A' → (∀ x x', B x == B' x') → (∀ x, B x) == (∀ x, B' x)

variable cast {A B : TypeH} : A = B → A → B

axiom cast_eq {A B : TypeH} (H : A = B) (a : A) : a == cast H a

theorem cast_app {A A' : TypeH} {B : A → TypeH} {B' : A' → TypeH} {f : ∀ x, B x} {a : A} (Ha : A = A') (Hb : (∀ x, B x) = (∀ x, B' x)) :
      cast Hb f (cast Ha a) == f a
:= let s1 : cast Hb f == f  := hsymm (cast_eq Hb f),
       s2 : cast Ha a == a  := hsymm (cast_eq Ha a)
   in hcongr s1 s2


