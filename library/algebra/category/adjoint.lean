-- Copyright (c) 2014 Floris van Doorn. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Floris van Doorn

import .constructions

open eq eq.ops category functor natural_transformation category.ops prod category.product

namespace adjoint
--representable functor

  definition foo (C : Category) : C ×c C ⇒ C ×c C := functor.id

  -- definition Hom (C : Category) : Cᵒᵖ ×c C ⇒ type :=
  -- functor.mk (λ a, hom (pr1 a) (pr2 a))
  --            (λ a b f h, pr2 f ∘ h ∘ pr1 f)
  --            (λ a, funext (λh, !id_left ⬝ !id_right))
  --            (λ a b c g f, funext (λh,
  --   show (pr2 g ∘ pr2 f) ∘ h ∘ (pr1 f ∘ pr1 g) = pr2 g ∘ (pr2 f ∘ h ∘ pr1 f) ∘ pr1 g, from sorry))
  --I'm lazy, waiting for automation to fill this

  variables (C D : Category)

  -- private definition aux_prod_cat [instance] : category (obD × obD) := prod_category (opposite.opposite D) D

--   definition adjoint.{l} (F : C ⇒ D) (G : D ⇒ C) := 
--   --@natural_transformation _ Type.{l} (Dᵒᵖ ×c D) type_category.{l+1} (Hom D) (Hom D)
-- sorry
--(@functor.compose _ _ _ _ _ _ (Hom D) (@product.prod_functor _ _ _ _ _ _ (Dᵒᵖ) D sorry sorry))
                       --(Hom C ∘f sorry)
  --product.prod_functor (opposite.opposite_functor F) (functor.ID D)
end adjoint
