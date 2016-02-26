prelude

definition id₁ [reducible] {A : Type} (a : A) := a
definition id₂ [reducible] {A : Type} (a : A) := a

definition id₅ [irreducible] {A : Type} (a : A) := a
definition id₆ [irreducible] {A : Type} (a : A) := a

definition pr [reducible] {A B : Type} (a : A) (b : B) := a
definition pr2 {A B : Type} (a : A) (b : B) := a

print [reducible]
print "-----------"
print [irreducible]
