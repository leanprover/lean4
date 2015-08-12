import data.nat data.examples.vector data.list.basic

attribute nat [recursor]

attribute nat.rec [recursor]

attribute nat.rec_on [recursor]

attribute nat.strong_induction_on [recursor]

attribute nat.cases_on [recursor]

attribute vector.cases_on [recursor]

attribute vector.brec_on [recursor]

axiom badrec1 : Π (A : Type) (C : A → Type) (a : A) (l : list A), C a

attribute badrec1 [recursor]

axiom badrec2 : Π (A : Type) (M : list A → Type) (l : list A) (a : nat), M l

attribute badrec2 [recursor]

open list
axiom myrec : Π (A : Type) (M : list A → Type) (l : list A), M [] → (∀ a, M [a]) → (∀ a₁ a₂, M [a₁, a₂]) → M l

attribute myrec [recursor]

set_option pp.implicit true
set_option pp.universes true

check @myrec

print [recursor] myrec
print [recursor] nat.induction_on
check @vector.induction_on
print [recursor] vector.induction_on
check @Exists.rec
print [recursor] Exists.rec
