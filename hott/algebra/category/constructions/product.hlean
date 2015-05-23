/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jakob von Raumer

Functor product precategory and (TODO) category
-/

import ..category ..functor

open eq prod is_trunc functor

namespace category
  definition precategory_product [reducible] {obC obD : Type}
    (C : precategory obC) (D : precategory obD) : precategory (obC × obD) :=
  precategory.mk' (λ a b, hom (pr1 a) (pr1 b) × hom (pr2 a) (pr2 b))
                  (λ a b c g f, (pr1 g ∘ pr1 f , pr2 g ∘ pr2 f))
                  (λ a, (id, id))
                  (λ a b c d h g f, pair_eq !assoc    !assoc   )
                  (λ a b c d h g f, pair_eq !assoc'   !assoc'  )
                  (λ a b f,         prod_eq !id_left  !id_left )
                  (λ a b f,         prod_eq !id_right !id_right)
                  (λ a,             prod_eq !id_id    !id_id)
                  _

  definition Precategory_product [reducible] (C D : Precategory) : Precategory :=
  precategory.Mk (precategory_product C D)

  infixr `×c`:30 := Precategory_product

  definition prod_functor [reducible] {C C' D D' : Precategory}
    (F : C ⇒ D) (G : C' ⇒ D') : C ×c C' ⇒ D ×c D' :=
  functor.mk (λ a, pair (F (pr1 a)) (G (pr2 a)))
             (λ a b f, pair (F (pr1 f)) (G (pr2 f)))
             (λ a, pair_eq !respect_id !respect_id)
             (λ a b c g f, pair_eq !respect_comp !respect_comp)

  infixr `×f`:30 := prod_functor

end category
