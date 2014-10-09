-- Copyright (c) 2014 Floris van Doorn. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Floris van Doorn

import .basic
import data.sigma

open eq eq.ops category functor natural_transformation

namespace limits
--representable functor
  section
  parameters {obI ob : Type} {I : category obI} {C : category ob} {D : I ⇒ C}

  definition constant_diagram (a : ob) : I ⇒ C :=
  mk (λ i, a)
     (λ i j u, id)
     (λ i, rfl)
     (λ i j k v u, symm !id_compose)

  definition cone := Σ(a : ob), constant_diagram a ⟹ D
  -- definition cone_category : category cone :=
  -- mk (λa b, sorry)
  --    (λ a b c g f, sorry)
  --    (λ a, sorry)
  --    (λ a b c d h g f, sorry)
  --    (λ a b f, sorry)
  --    (λ a b f, sorry)

  end
end limits
  -- functor.mk (λ a, sorry)
  --            (λ a b f, sorry)
  --            (λ a, sorry)
  --            (λ a b c g f, sorry)
