prelude

definition id₁ [reducible] {A : Type} (a : A) := a
definition id₂ [reducible] {A : Type} (a : A) := a

definition id₄ [quasireducible] {A : Type} (a : A) := a
definition id₃ [quasireducible] {A : Type} (a : A) := a

definition id₅ [irreducible] {A : Type} (a : A) := a
definition id₆ [irreducible] {A : Type} (a : A) := a

definition pr [reducible] {A B : Type} (a : A) (b : B) := a
definition pr2 {A B : Type} (a : A) (b : B) := a

print [reducible]
print "-----------"
print [quasireducible]
print "-----------"
print [irreducible]
