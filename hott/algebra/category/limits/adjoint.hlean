/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

colimit_functor ⊣ Δ ⊣ limit_functor
-/

import .colimits ..functor.adjoint

open eq functor category is_trunc prod nat_trans

namespace category

  definition limit_functor_adjoint [constructor] (D I : Precategory) [H : has_limits_of_shape D I] :
    constant_diagram D I ⊣ limit_functor D I :=
  adjoint.mk'
  begin
    fapply natural_iso.MK,
    { intro dF η, induction dF with d F, esimp at *,
      fapply hom_limit,
      { exact natural_map η},
      { intro i j f, exact !naturality ⬝ !id_right}},
    { esimp, intro dF dF' fθ, induction dF with d F, induction dF' with d' F',
      induction fθ with f θ, esimp at *, apply eq_of_homotopy, intro η,
      apply eq_hom_limit, intro i,
      rewrite [assoc, limit_hom_limit_commute,
              -assoc, assoc (limit_morphism F i), hom_limit_commute]},
    { esimp, intro dF f, induction dF with d F, esimp at *,
      refine !limit_nat_trans ∘n constant_nat_trans I f},
    { esimp, intro dF, induction dF with d F, esimp, apply eq_of_homotopy, intro η,
      apply nat_trans_eq, intro i, esimp, apply hom_limit_commute},
    { esimp, intro dF, induction dF with d F, esimp, apply eq_of_homotopy, intro f,
      symmetry, apply eq_hom_limit, intro i, reflexivity}
  end


end category
