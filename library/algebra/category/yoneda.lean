-- Copyright (c) 2014 Floris van Doorn. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Floris van Doorn

import .basic .constructions

open eq eq.ops category functor category.ops prod

namespace yoneda
--representable functor
  section
  variables {ob : Type} {C : category ob}
  set_option pp.universes true
  check @type_category
  section
    variables {a a' b b' : ob} (f : @hom ob C a' a) (g : @hom ob C b b')
--    definition Hom_fun_fun :
  end
  definition Hom : Cᵒᵖ ×c C ⇒ type :=
  @functor.mk _ _ _ _ (λ a, hom (pr1 a) (pr2 a))
	     (λ a b f h, pr2 f ∘ h ∘ pr1 f)
	     (λ a, funext (λh, !id_left ⬝ !id_right))
	     (λ a b c g f, funext (λh,
    show (pr2 g ∘ pr2 f) ∘ h ∘ (pr1 f ∘ pr1 g) = pr2 g ∘ (pr2 f ∘ h ∘ pr1 f) ∘ pr1 g, from sorry))
  --I'm lazy, waiting for automation to fill this



  end
end yoneda
