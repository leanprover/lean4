meta def blast : tactic unit := using_smt $ return ()

structure { u v } Category :=
  (Obj : Type u )
  (Hom : Obj -> Obj -> Type v)
  (identity : Π X : Obj, Hom X X)
  (compose  : Π ⦃X Y Z : Obj⦄, Hom X Y → Hom Y Z → Hom X Z)
  (left_identity  : ∀ ⦃X Y : Obj⦄ (f : Hom X Y), compose (identity _) f = f)

#check @Category.mk.inj_eq

structure Functor (C : Category) (D : Category) :=
  (onObjects   : C^.Obj → D^.Obj)
  (onMorphisms : Π ⦃X Y : C^.Obj⦄,
                C^.Hom X Y → D^.Hom (onObjects X) (onObjects Y))

structure NaturalTransformation { C D : Category } ( F G : Functor C D ) :=
  (components: Π X : C^.Obj, D^.Hom (F^.onObjects X) (G^.onObjects X))

definition IdentityNaturalTransformation { C D : Category } (F : Functor C D) : NaturalTransformation F F :=
  {
    components := λ X, D^.identity (F^.onObjects X)
  }

definition vertical_composition_of_NaturalTransformations
  { C D : Category }
  { F G H : Functor C D }
  ( α : NaturalTransformation F G )
  ( β : NaturalTransformation G H ) : NaturalTransformation F H :=
  {
    components := λ X, D^.compose (α^.components X) (β^.components X)
  }

-- We'll want to be able to prove that two natural transformations are equal if they are componentwise equal.
lemma NaturalTransformations_componentwise_equal
  { C D : Category }
  { F G : Functor C D }
  ( α β : NaturalTransformation F G )
  ( w : ∀ X : C^.Obj, α^.components X = β^.components X ) : α = β :=
  begin
    induction α with αc,
    induction β with βc,
    have hc : αc = βc := funext w,
    subst hc
  end

@[simp]
lemma vertical_composition_of_NaturalTransformations_components
  { C D : Category }
  { F G H : Functor C D }
  { α : NaturalTransformation F G }
  { β : NaturalTransformation G H }
  { X : C^.Obj } :
  (vertical_composition_of_NaturalTransformations α β)^.components X = D^.compose (α^.components X) (β^.components X) :=
by blast

@[simp]
lemma IdentityNaturalTransformation_components
  { C D : Category }
  { F : Functor C D }
  { X : C^.Obj } :
  (IdentityNaturalTransformation F)^.components X = D^.identity (F^.onObjects X) :=
by blast

definition FunctorCategory ( C D : Category ) : Category :=
{
  Obj := Functor C D,
  Hom := λ F G, NaturalTransformation F G,
  identity := λ F, IdentityNaturalTransformation F,
  compose  := @vertical_composition_of_NaturalTransformations C D,

  left_identity  := begin
                     intros F G f,
                     apply NaturalTransformations_componentwise_equal,
                     intros,
                     simp [ D^.left_identity ]
                    end
}
