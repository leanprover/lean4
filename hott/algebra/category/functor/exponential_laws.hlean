/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jakob von Raumer

Exponential laws
-/

import .functor.equivalence .functor.curry
       .constructions.terminal .constructions.initial .constructions.product .constructions.sum

open eq category functor is_trunc nat_trans iso unit prod sum prod.ops


namespace category

  /- C ^ 0 ≅ 1 -/

  definition functor_zero_iso_one [constructor] (C : Precategory) : C ^c 0 ≅c 1 :=
  begin
    fapply isomorphism.MK,
    { apply terminal_functor},
    { apply point, apply initial_functor},
    { fapply functor_eq: intros; esimp at *,
      { apply eq_of_is_contr},
      { apply nat_trans_eq, intro u, induction u}},
    { fapply functor_eq: intros; esimp at *,
      { induction x, reflexivity},
      { induction f, reflexivity}},
  end

  /- 0 ^ C ≅ 0 if C is inhabited -/

  definition zero_functor_functor_zero [constructor] (C : Precategory) (c : C) : 0 ^c C ⇒ 0 :=
  begin
    fapply functor.mk: esimp,
    { intro F, exact F c},
    { intro F, apply empty.elim (F c)},
    { intro F, apply empty.elim (F c)},
    { intro F, apply empty.elim (F c)},
  end

  definition zero_functor_iso_zero [constructor] (C : Precategory) (c : C) : 0 ^c C ≅c 0 :=
  begin
    fapply isomorphism.MK,
    { exact zero_functor_functor_zero C c},
    { apply initial_functor},
    { fapply functor_eq: esimp,
      { intro F, apply empty.elim (F c)},
      { intro F, apply empty.elim (F c)}},
    { fapply functor_eq: esimp,
      { intro u, apply empty.elim u},
      { apply empty.elim}},
  end


  /- C ^ 1 ≅ C -/

  definition functor_one_iso [constructor] (C : Precategory) : C ^c 1 ≅c C :=
  begin
    fapply isomorphism.MK,
    { exact !eval_functor star},
    { apply functor_curry, apply pr1_functor},
    { fapply functor_eq: esimp,
      { intro F, fapply functor_eq: esimp,
        { intro u, induction u, reflexivity},
        { intro u v f, induction u, induction v, induction f, esimp, rewrite [+id_id,-respect_id]}},
      { intro F G η, apply nat_trans_eq, intro u, esimp,
        rewrite [natural_map_hom_of_eq _ u, natural_map_inv_of_eq _ u,▸*,+ap010_functor_eq _ _ u],
        induction u, rewrite [▸*, id_leftright], }},
    { fapply functor_eq: esimp,
      { intro c d f, rewrite [▸*, id_leftright] }},
  end

  /- 1 ^ C ≅ 1 -/

  definition one_functor_iso_one [constructor] (C : Precategory) : 1 ^c C ≅c 1 :=
  begin
    fapply isomorphism.MK,
    { apply terminal_functor},
    { apply functor_curry, apply pr1_functor},
    { fapply functor_eq: esimp,
      { intro F, fapply functor_eq: esimp,
        { intro c, apply unit.eta},
        { intro c d f, apply unit.eta}},
      { intro F G η, fapply nat_trans_eq, esimp, intro c, apply unit.eta}},
    { fapply functor_eq: esimp,
      { intro u, apply unit.eta},
      { intro u v f, apply unit.eta}},
  end

  /- C ^ (D + E) ≅ C ^ D × C ^ E -/

  definition functor_sum_right [constructor] (C D E : Precategory)
    : C ^c (D +c E) ⇒ C ^c D ×c C ^c E :=
  begin
    apply functor_prod,
    { apply precomposition_functor, apply inl_functor},
    { apply precomposition_functor, apply inr_functor}
  end

  definition functor_sum_left [constructor] (C D E : Precategory)
    : C ^c D ×c C ^c E ⇒ C ^c (D +c E) :=
  begin
    fapply functor.mk: esimp,
    { intro V, exact V.1 +f V.2},
    { intro V W ν, apply sum_nat_trans, exact ν.1, exact ν.2},
    { intro V, apply nat_trans_eq, intro a, induction a: reflexivity},
    { intro U V W ν μ, apply nat_trans_eq, intro a, induction a: reflexivity}
      -- REPORT: cannot abstract
  end

  /- TODO: optimize -/
  definition functor_sum_iso [constructor] (C D E : Precategory)
    : C ^c (D +c E) ≅c C ^c D ×c C ^c E :=
  begin
    fapply isomorphism.MK,
    { apply functor_sum_right},
    { apply functor_sum_left},
    { fapply functor_eq: esimp,
      { exact sum_functor_eta},
      { intro F G η, fapply nat_trans_eq, intro a, esimp,
        rewrite [@natural_map_hom_of_eq _ _ _ G _ a, @natural_map_inv_of_eq _ _ _ F _ a,
                 ↑sum_functor_eta,+ap010_functor_eq _ _ a],
        induction a: esimp: apply id_leftright}},
    { fapply functor_eq: esimp,
      { intro V, induction V with F G, apply prod_eq: esimp,
        apply sum_functor_inl, apply sum_functor_inr},
      { intro V W ν, induction V with F G, induction W with F' G', induction ν with η θ,
        apply prod_eq: apply nat_trans_eq,
        { intro d, rewrite [▸*,@pr1_hom_of_eq (C ^c D) (C ^c E), @pr1_inv_of_eq (C ^c D) (C ^c E),
            @natural_map_hom_of_eq _ _ _ F' _ d, @natural_map_inv_of_eq _ _ _ F _ d,
            ↑sum_functor_inl,+ap010_functor_eq _ _ d, ▸*], apply id_leftright},
        { intro e, rewrite [▸*,@pr2_hom_of_eq (C ^c D) (C ^c E), @pr2_inv_of_eq (C ^c D) (C ^c E),
            @natural_map_hom_of_eq _ _ _ G' _ e, @natural_map_inv_of_eq _ _ _ G _ e,
            ↑sum_functor_inr,+ap010_functor_eq _ _ e, ▸*], apply id_leftright}}},
  end

  /- (C × D) ^ E ≅ C ^ E × D ^ E -/

  definition prod_functor_right [constructor] (C D E : Precategory)
    : (C ×c D) ^c E ⇒ C ^c E ×c D ^c E :=
  begin
    apply functor_prod,
    { apply postcomposition_functor, apply pr1_functor},
    { apply postcomposition_functor, apply pr2_functor}
  end

  definition prod_functor_left [constructor] (C D E : Precategory)
    : C ^c E ×c D ^c E ⇒ (C ×c D) ^c E :=
  begin
    fapply functor.mk: esimp,
    { intro V, exact V.1 ×f V.2},
    { intro V W ν, exact prod_nat_trans ν.1 ν.2},
    { intro V, apply nat_trans_eq, intro e, reflexivity},
    { intro U V W ν μ, apply nat_trans_eq, intro e, reflexivity}
  end

  definition prod_functor_iso [constructor] (C D E : Precategory)
    : (C ×c D) ^c E ≅c C ^c E ×c D ^c E :=
  begin
    fapply isomorphism.MK,
    { apply prod_functor_right},
    { apply prod_functor_left},
    { fapply functor_eq: esimp,
      { exact prod_functor_eta},
      { intro F G η, fapply nat_trans_eq, intro e, esimp,
        rewrite [@natural_map_hom_of_eq _ _ _ G, @natural_map_inv_of_eq _ _ _ F,↑prod_functor_eta,
          +ap010_functor_eq, +hom_of_eq_inv, ▸*, pr1_hom_of_eq, pr2_hom_of_eq,
          pr1_inv_of_eq, pr2_inv_of_eq, ▸*, +id_leftright, prod.eta]}},
    { fapply functor_eq: esimp,
      { intro V, apply prod_eq: esimp, apply pr1_functor_prod, apply pr2_functor_prod},
      { intro V W ν, rewrite [@pr1_hom_of_eq (C ^c E) (D ^c E), @pr2_hom_of_eq (C ^c E) (D ^c E),
          @pr1_inv_of_eq (C ^c E) (D ^c E), @pr2_inv_of_eq (C ^c E) (D ^c E)],
        apply prod_eq: apply nat_trans_eq: intro v: esimp,
        { rewrite [@natural_map_hom_of_eq _ _ _ W.1, @natural_map_inv_of_eq _ _ _ V.1, ▸*,
            ↑pr1_functor_prod,+ap010_functor_eq, ▸*, id_leftright]},
        { rewrite [@natural_map_hom_of_eq _ _ _ W.2, @natural_map_inv_of_eq _ _ _ V.2, ▸*,
            ↑pr2_functor_prod,+ap010_functor_eq, ▸*, id_leftright]}}},
  end

  /- (C ^ D) ^ E ≅ C ^ (E × D) -/

  definition functor_functor_right [constructor] (C D E : Precategory)
    : (C ^c D) ^c E ⇒ C ^c (E ×c D) :=
  begin
    fapply functor.mk: esimp,
    { exact functor_uncurry},
    { apply @nat_trans_uncurry},
    { intro F, apply nat_trans_eq, intro e, reflexivity},
    { intro F G H η θ, apply nat_trans_eq, intro e, reflexivity}
  end

  definition functor_functor_left [constructor] (C D E : Precategory)
    : C ^c (E ×c D) ⇒ (C ^c D) ^c E :=
  begin
    fapply functor.mk: esimp,
    { exact functor_curry},
    { apply @nat_trans_curry},
    { intro F, apply nat_trans_eq, intro e, reflexivity},
    { intro F G H η θ, apply nat_trans_eq, intro e, reflexivity}
  end

  definition functor_functor_iso [constructor] (C D E : Precategory)
    : (C ^c D) ^c E ≅c C ^c (E ×c D) :=
  begin
    fapply isomorphism.MK: esimp,
    { apply functor_functor_right},
    { apply functor_functor_left},
    { fapply functor_eq: esimp,
      { exact functor_curry_functor_uncurry},
      { intro F G η, fapply nat_trans_eq, intro e, esimp,
        rewrite [@natural_map_hom_of_eq _ _ _ G, @natural_map_inv_of_eq _ _ _ F,
          ↑functor_curry_functor_uncurry, +@ap010_functor_eq E (C ^c D)],
        apply nat_trans_eq, intro d, rewrite [▸*, hom_of_eq_inv,
          @natural_map_hom_of_eq _ _ _ (G e), @natural_map_inv_of_eq _ _ _ (F e),
          ↑functor_curry_functor_uncurry_ob, +@ap010_functor_eq D C, ▸*, id_leftright]}},
    { fapply functor_eq: esimp,
      { intro F, apply functor_uncurry_functor_curry},
      { intro F G η, fapply nat_trans_eq, esimp, intro v, induction v with c d,
        rewrite [@natural_map_hom_of_eq _ _ _ G, @natural_map_inv_of_eq _ _ _ F,
          ↑functor_uncurry_functor_curry, +@ap010_functor_eq, ▸*], apply id_leftright}},
  end


end category
