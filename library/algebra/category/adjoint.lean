-- Copyright (c) 2014 Floris van Doorn. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Floris van Doorn

import .basic .constructions

open eq eq.ops category functor natural_transformation category.ops prod category.product

namespace adjoint
--representable functor

  definition foo {obC : Type} (C : category obC) : C ×c C ⇒ C ×c C := functor.id

  definition Hom {obC : Type} (C : category obC) : Cᵒᵖ ×c C ⇒ type :=
  @functor.mk _ _ _ _ (λ a, hom (pr1 a) (pr2 a))
	     (λ a b f h, pr2 f ∘ h ∘ pr1 f)
	     (λ a, funext (λh, !id_left ⬝ !id_right))
	     (λ a b c g f, funext (λh,
    show (pr2 g ∘ pr2 f) ∘ h ∘ (pr1 f ∘ pr1 g) = pr2 g ∘ (pr2 f ∘ h ∘ pr1 f) ∘ pr1 g, from sorry))
  --I'm lazy, waiting for automation to fill this

  section
  parameters {obC obD : Type} (C : category obC) {D : category obD}

  definition adjoint (F : C ⇒ D) (G : D ⇒ C) :=
  natural_transformation (Hom D ∘f sorry)
			 --(Hom C ∘f sorry)
--product.prod_functor (opposite.opposite_functor F) (functor.ID D)

  end
end adjoint
