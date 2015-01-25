import algebra.category.basic
open category

inductive my_functor {obC obD : Type} (C : category obC) (D : category obD) : Type :=
mk : Π (obF : obC → obD) (homF : Π{A B : obC}, hom A B → hom (obF A) (obF B)),
    (Π {A : obC}, homF (ID A) = ID (obF A)) →
    (Π {A B C : obC} {f : hom A B} {g : hom B C}, homF (g ∘ f) = homF g ∘ homF f) →
     my_functor C D

definition my_object [coercion] {obC obD : Type} {C : category obC} {D : category obD} (F : my_functor C D) : obC → obD :=
my_functor.rec (λ obF homF Hid Hcomp, obF) F

definition my_homphism [coercion] {obC obD : Type} {C : category obC} {D : category obD} (F : my_functor C D) :
      Π{A B : obC}, hom A B → hom (my_object F A) (my_object F B) :=
my_functor.rec (λ obF homF Hid Hcomp, homF) F

constants obC obD : Type
constants a b : obC
constant C : category obC
attribute C [instance]
constant D : category obD
constant F : my_functor C D
constant m : hom a b
check F a
check F m
