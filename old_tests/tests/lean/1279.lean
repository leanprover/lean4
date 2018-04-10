structure Category : Type 2 :=
  (Obj : Type)
  (Hom : Obj → Obj → Type)
  (compose : Π ⦃A B C : Obj⦄, Hom A B → Hom B C → Hom A C)

open Category

structure Functor (source target : Category) : Type :=
  (onObjects     : Obj source → Obj target)
  (onMorphisms   : Π ⦃A B : Obj source⦄, Hom source A B → Hom target (onObjects A) (onObjects B))
  (functoriality : Π ⦃A B C : Obj source⦄ (f : Hom source A B) (g : Hom source B C),
                    onMorphisms (compose source g f) = compose target (onMorphisms g) (onMorphisms f))
