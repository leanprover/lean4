import algebra.category
open category

inductive my_functor {obC obD : Type} (C : category obC) (D : category obD) : Type :=
mk : Π (obF : obC → obD) (morF : Π{A B : obC}, mor A B → mor (obF A) (obF B)),
    (Π {A : obC}, morF (ID A) = ID (obF A)) →
    (Π {A B C : obC} {f : mor A B} {g : mor B C}, morF (g ∘ f) = morF g ∘ morF f) →
     my_functor C D

definition my_object [coercion] {obC obD : Type} {C : category obC} {D : category obD} (F : my_functor C D) : obC → obD :=
my_functor.rec (λ obF morF Hid Hcomp, obF) F

definition my_morphism [coercion] {obC obD : Type} {C : category obC} {D : category obD} (F : my_functor C D) :
      Π{A B : obC}, mor A B → mor (my_object F A) (my_object F B) :=
my_functor.rec (λ obF morF Hid Hcomp, morF) F

constants obC obD : Type
constants a b : obC
constant C : category obC
instance C
constant D : category obD
constant F : my_functor C D
constant m : mor a b
check F a
check F m
