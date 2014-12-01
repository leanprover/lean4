prelude
-- category

definition Prop := Type.{0}
constant eq {A : Type} : A → A → Prop
infix `=`:50 := eq

constant ob  : Type.{1}
constant mor : ob → ob → Type.{1}

inductive category : Type :=
mk : Π (id : Π (A : ob), mor A A),
     (Π (A B : ob) (f : mor A A), id A = f) → category

definition id (Cat : category) := category.rec (λ id idl, id) Cat
constant Cat : category

set_option unifier.computation true
print "-----------------"
theorem id_left (A : ob) (f : mor A A) : @eq (mor A A) (id Cat A) f :=
@category.rec
  (λ (C : category), Π (A B : ob) (f : mor A A), @eq (mor A A) (id C A) f)
  (λ id idl, idl)
  Cat A A f
