universe v u u'

class CategoryStruct (C : Type u) :=
  (Hom : C → C → Type v)
  (id : ∀ X, Hom X X)
  (comp : ∀ {X Y Z : C}, Hom X Y → Hom Y Z → Hom X Z)

class Category (C : Type u) extends CategoryStruct.{v} C :=
  (comp_id : ∀ {X Y : C} (f : Hom X Y), comp f (id Y) = f)

open CategoryStruct
open Category

attribute [simp] comp_id

instance (C : Type u) [Category.{v} C] : Category.{v} (ULift.{u'} C) where
  Hom := λ X Y => Hom X.down Y.down
  id := λ X => id X.down
  comp := λ f g => comp f g
  comp_id := λ f => by simp
