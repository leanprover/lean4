structure Category :=
  (Obj : Type)
  (Hom : Obj -> Obj -> Type)

structure Isomorphism ( C: Category ) { A B : C^.Obj } :=
  (morphism : C^.Hom A B)

instance Isomorphism_coercion_to_morphism { C : Category } { A B C^.Obj } : has_coe (Isomorphism C A B) (C^.Hom A B) :=
  (coe: Isomorphism.morphism)

instance Isomorphism_coercion_to_morphism_fixed { C : Category } { A B : C^.Obj } : has_coe (Isomorphism C) (C^.Hom A B) :=
{coe := Isomorphism.morphism}
