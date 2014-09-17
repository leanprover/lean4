-- category

definition Prop := Type.{0}
variable eq {A : Type} : A → A → Prop
infix `=`:50 := eq

variable ob  : Type.{1}
variable mor : ob → ob → Type.{1}

inductive category : Type :=
mk : Π (id : Π (A : ob), mor A A),
     (Π (A B : ob) (f : mor A A), id A = f) → category

definition id (Cat : category) := category.rec (λ id idl, id) Cat
variable Cat : category

theorem id_left (A : ob) (f : mor A A) : @eq (mor A A) (id Cat A) f :=
@category.rec (λ (C : category), @eq (mor A A) (id C A) f)
  (λ (id  : Π (T : ob), mor T T)
     (idl : Π (T : ob), _),
     idl A A f)
  Cat
