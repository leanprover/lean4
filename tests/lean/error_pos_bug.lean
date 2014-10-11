inductive category (ob : Type) : Type :=
mk : Π (hom : ob → ob → Type)
       (comp : Π⦃a b c : ob⦄, hom b c → hom a b → hom a c),
       category ob

inductive Category : Type := mk : Π (ob : Type), category ob → Category

definition MK (a b c : Category) : _ :=
Category.mk a (category.mk b c)
