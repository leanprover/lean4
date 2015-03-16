import .basic .functor

open category is_trunc eq function sigma sigma.ops

namespace category
  structure strict_precategory[class] (ob : Type) extends precategory ob :=
    (is_hset_ob : is_hset ob)

  attribute strict_precategory.is_hset_ob [instance]

  definition strict_precategory.mk' [reducible] (ob : Type) (C : precategory ob)
    (H : is_hset ob) : strict_precategory ob :=
  precategory.rec_on C strict_precategory.mk H

  structure Strict_precategory : Type :=
    (carrier : Type)
    (struct : strict_precategory carrier)

  attribute Strict_precategory.struct [instance] [coercion]

  definition Strict_precategory.to_Precategory [coercion] [reducible]
    (C : Strict_precategory) : Precategory :=
  Precategory.mk (Strict_precategory.carrier C) C

  open functor

  definition precat_strict_precat : precategory Strict_precategory :=
  precategory.mk (λ a b, functor a b)
     (λ a b, @functor.is_hset_functor a b _)
     (λ a b c g f, functor.compose g f)
     (λ a, functor.id)
     (λ a b c d h g f, !functor.assoc)
     (λ a b f, !functor.id_left)
     (λ a b f, !functor.id_right)

  definition Precat_of_strict_precats := precategory.Mk precat_strict_precat

  namespace ops

    abbreviation SPreCat := Precat_of_strict_precats
    --attribute precat_strict_precat [instance]

  end ops

end category
