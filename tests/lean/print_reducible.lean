prelude

attribute [reducible]
definition id₁ {A : Type} (a : A) := a
attribute [reducible]
definition id₂ {A : Type} (a : A) := a

attribute [irreducible]
definition id₅ {A : Type} (a : A) := a
attribute [irreducible]
definition id₆ {A : Type} (a : A) := a

attribute [reducible]
definition pr {A B : Type} (a : A) (b : B) := a
definition pr2 {A B : Type} (a : A) (b : B) := a

#print [reducible]
#print "-----------"
#print [irreducible]
