import logic

inductive category (ob : Type) (mor : ob → ob → Type) : Type :=
mk : Π (comp : Π⦃A B C : ob⦄, mor B C → mor A B → mor A C)
           (id : Π {A : ob}, mor A A),
            (Π {A B C D : ob} {f : mor A B} {g : mor B C} {h : mor C D},
            comp h (comp g f) = comp (comp h g) f) →
           (Π {A B : ob} {f : mor A B}, comp f id = f) →
           (Π {A B : ob} {f : mor A B}, comp id f = f) →
            category ob mor
class category

namespace category
section sec_cat
  parameter A : Type
  inductive foo :=
  mk : A → foo

  class foo
  parameters {ob : Type} {mor : ob → ob → Type} {Cat : category ob mor}
  abbreviation compose := rec (λ comp id assoc idr idl, comp) Cat
  abbreviation id := rec (λ comp id assoc idr idl, id) Cat
  infixr `∘`:60 := compose
end sec_cat
end category
