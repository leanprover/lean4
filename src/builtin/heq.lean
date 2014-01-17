import macros

-- Heterogenous equality
variable heq {A B : TypeU} : A → B → Bool
infixl 50 == : heq

universe H ≥ 1
universe U ≥ H + 1
definition TypeH := (Type H)

axiom heq_eq {A : TypeH} (a b : A) : a == b ↔ a = b

definition to_eq {A : TypeH} {a b : A} (H : a == b) : a = b
:= (heq_eq a b) ◂ H

definition to_heq {A : TypeH} {a b : A} (H : a = b) : a == b
:= (symm (heq_eq a b)) ◂ H

theorem hrefl {A : TypeH} (a : A) : a == a
:= to_heq (refl a)

axiom hsymm {A B : TypeH} {a : A} {b : B} : a == b → b == a

axiom htrans {A B C : TypeH} {a : A} {b : B} {c : C} : a == b → b == c → a == c

axiom hcongr {A A' : TypeH} {B : A → TypeH} {B' : A' → TypeH} {f : ∀ x, B x} {f' : ∀ x, B' x} {a : A} {a' : A'} :
      f == f' → a == a' → f a == f' a'

axiom hfunext {A A' : TypeH} {B : A → TypeH} {B' : A' → TypeH} {f : ∀ x, B x} {f' : ∀ x, B' x} :
      A = A' → (∀ x x', x == x' → f x == f' x') → f == f'

axiom hpiext {A A' : TypeH} {B : A → TypeH} {B' : A' → TypeH} :
      A = A' → (∀ x x', x == x' → B x == B' x') → (∀ x, B x) == (∀ x, B' x)

axiom hallext {A A' : TypeH} {B : A → Bool} {B' : A' → Bool} :
      A = A' → (∀ x x', x == x' → B x == B' x') → (∀ x, B x) == (∀ x, B' x)
