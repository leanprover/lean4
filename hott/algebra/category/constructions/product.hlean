/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jakob von Raumer

Product precategory and (TODO) category
-/

import ..category ..functor hit.trunc

open eq prod is_trunc functor sigma trunc

namespace category
  definition precategory_prod [constructor] [reducible] {obC obD : Type}
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
  definition Precategory_prod [reducible] [constructor] (C D : Precategory) : Precategory :=
  precategory.Mk (precategory_prod C D)

  infixr `×c`:30 := Precategory_prod

  definition pr1_functor [constructor] {C D : Precategory} : C ×c D ⇒ C :=
  functor.mk pr1
             (λa b, pr1)
             (λa, idp)
             (λa b c g f, idp)

  definition pr2_functor [constructor] {C D : Precategory} : C ×c D ⇒ D :=
  functor.mk pr2
             (λa b, pr2)
             (λa, idp)
             (λa b c g f, idp)

  definition functor_prod [constructor] [reducible] {C D X : Precategory}
    (F : X ⇒ C) (G : X ⇒ D) : X ⇒ C ×c D :=
  functor.mk (λ a,     pair (F a) (G a))
             (λ a b f, pair (F f) (G f))
             (λ a,         abstract pair_eq !respect_id   !respect_id   end)
             (λ a b c g f, abstract pair_eq !respect_comp !respect_comp end)

  definition pr1_functor_prod {C D X : Precategory} (F : X ⇒ C) (G : X ⇒ D)
    : pr1_functor ∘f functor_prod F G = F :=
  functor_eq (λx, idp)
             (λx y f, !id_leftright)

  definition pr2_functor_prod {C D X : Precategory} (F : X ⇒ C) (G : X ⇒ D)
    : pr2_functor ∘f functor_prod F G = G :=
  functor_eq (λx, idp)
             (λx y f, !id_leftright)

  -- definition universal_property_prod {C D X : Precategory} (F : X ⇒ C) (G : X ⇒ D)
  --   : is_contr (Σ(H : X ⇒ C ×c D), pr1_functor ∘f H = F × pr2_functor ∘f H = G) :=
  -- is_contr.mk
  --   ⟨functor_prod F G, (pr1_functor_prod F G, pr2_functor_prod F G)⟩
  --   begin
  --     intro v, induction v with H w, induction w with p q,
  --     symmetry, fapply sigma_eq: esimp,
  --     { fapply functor_eq,
  --       { intro x, apply prod_eq: esimp,
  --         { exact ap010 to_fun_ob p x},
  --         { exact ap010 to_fun_ob q x}},
  --       { intro x y f, apply prod_eq: esimp,
  --         { exact sorry},
  --         { exact sorry}}},
  --     { exact sorry}
  --   end

  definition prod_functor_prod [constructor] {C C' D D' : Precategory}
    (F : C ⇒ D) (G : C' ⇒ D') : C ×c C' ⇒ D ×c D' :=
  functor_prod (F ∘f pr1_functor) (G ∘f pr2_functor)

  infixr `×f`:30 := prod_functor

end category
