/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn
-/

import .natural_transformation
import data.sigma

open eq eq.ops category functor natural_transformation

namespace limits
--representable functor
  section
  variables {I C : Category} {D : I ⇒ C}

  definition constant_diagram (a : C) : I ⇒ C :=
  mk (λ i, a)
     (λ i j u, id)
     (λ i, rfl)
     (λ i j k v u, symm !id_compose)

  definition cone := Σ(a : C), constant_diagram a ⟹ D
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
