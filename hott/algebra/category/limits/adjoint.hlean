/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

colimit_functor ⊣ Δ ⊣ limit_functor
-/

import .colimits ..functor.adjoint2

open functor category is_trunc prod

namespace category

  definition limit_functor_adjoint [constructor] (D I : Precategory) [H : has_limits_of_shape D I] :
    limit_functor D I ⊣ constant_diagram D I :=
  adjoint.mk'
  begin
    fapply natural_iso.MK: esimp,
    { intro Fd f, induction Fd with F d, esimp at *,
      exact sorry},
    { exact sorry},
    { exact sorry},
    { exact sorry},
    { exact sorry}
  end

  -- set_option pp.universes true
  -- print Precategory_functor
  -- print limit_functor_adjoint
  -- print adjoint.mk'
end category
