/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Adjoint functors
-/

import .attributes

open category functor nat_trans eq is_trunc iso equiv prod trunc function pi is_equiv

namespace category

  -- TODO(?): define a structure "adjoint" and then define
  -- structure is_left_adjoint (F : C ⇒ D) :=
  --   (G : D ⇒ C) -- G
  --   (is_adjoint : adjoint F G)

  --   infix `⊣`:55 := adjoint

  structure is_left_adjoint [class] {C D : Precategory} (F : C ⇒ D) :=
    (G : D ⇒ C)
    (η : 1 ⟹ G ∘f F)
    (ε : F ∘f G ⟹ 1)
    (H : Π(c : C), ε (F c) ∘ F (η c) = ID (F c))
    (K : Π(d : D), G (ε d) ∘ η (G d) = ID (G d))

  abbreviation right_adjoint  [unfold 4] := @is_left_adjoint.G
  abbreviation unit           [unfold 4] := @is_left_adjoint.η
  abbreviation counit         [unfold 4] := @is_left_adjoint.ε
  abbreviation counit_unit_eq [unfold 4] := @is_left_adjoint.H
  abbreviation unit_counit_eq [unfold 4] := @is_left_adjoint.K

  theorem is_hprop_is_left_adjoint [instance] {C : Category} {D : Precategory} (F : C ⇒ D)
    : is_hprop (is_left_adjoint F) :=
  begin
    apply is_hprop.mk,
    intro G G', cases G with G η ε H K, cases G' with G' η' ε' H' K',
    assert lem₁ : Π(p : G = G'), p ▸ η = η' → p ▸ ε = ε'
      → is_left_adjoint.mk G η ε H K = is_left_adjoint.mk G' η' ε' H' K',
    { intros p q r, induction p, induction q, induction r, esimp,
      apply apd011 (is_left_adjoint.mk G η ε) !is_hprop.elim !is_hprop.elim},
    assert lem₂ : Π (d : carrier D),
                    (to_fun_hom G (natural_map ε' d) ∘
                    natural_map η (to_fun_ob G' d)) ∘
                    to_fun_hom G' (natural_map ε d) ∘
                    natural_map η' (to_fun_ob G d) = id,
    { intro d, esimp,
      rewrite [assoc],
      rewrite [-assoc (G (ε' d))],
      esimp, rewrite [nf_fn_eq_fn_nf_pt' G' ε η d],
      esimp, rewrite [assoc],
      esimp, rewrite [-assoc],
      rewrite [↑functor.compose, -respect_comp G],
      rewrite [nf_fn_eq_fn_nf_pt ε ε' d,nf_fn_eq_fn_nf_pt η' η (G d),▸*],
      rewrite [respect_comp G],
      rewrite [assoc,▸*,-assoc (G (ε d))],
      rewrite [↑functor.compose, -respect_comp G],
      rewrite [H' (G d)],
      rewrite [respect_id,▸*,id_right],
      apply K},
    assert lem₃ : Π (d : carrier D),
                    (to_fun_hom G' (natural_map ε d) ∘
                    natural_map η' (to_fun_ob G d)) ∘
                    to_fun_hom G (natural_map ε' d) ∘
                    natural_map η (to_fun_ob G' d) = id,
    { intro d, esimp,
      rewrite [assoc, -assoc (G' (ε d))],
      esimp, rewrite [nf_fn_eq_fn_nf_pt' G ε' η' d],
      esimp, rewrite [assoc], esimp, rewrite [-assoc],
      rewrite [↑functor.compose, -respect_comp G'],
      rewrite [nf_fn_eq_fn_nf_pt ε' ε d,nf_fn_eq_fn_nf_pt η η' (G' d)],
      esimp,
      rewrite [respect_comp G'],
      rewrite [assoc,▸*,-assoc (G' (ε' d))],
      rewrite [↑functor.compose, -respect_comp G'],
      rewrite [H (G' d)],
      rewrite [respect_id,▸*,id_right],
      apply K'},
    fapply lem₁,
    { fapply functor.eq_of_pointwise_iso,
      { fapply change_natural_map,
        { exact (G' ∘fn1 ε) ∘n !assoc_natural_rev ∘n (η' ∘1nf G)},
        { intro d, exact (G' (ε d) ∘ η' (G d))},
        { intro d, exact ap (λx, _ ∘ x) !id_left}},
      { intro d, fconstructor,
        { exact (G (ε' d) ∘ η (G' d))},
        { exact lem₂ d },
        { exact lem₃ d }}},
    { clear lem₁, refine transport_hom_of_eq_right _ η ⬝ _,
      krewrite hom_of_eq_compose_right,
      rewrite functor.hom_of_eq_eq_of_pointwise_iso,
      apply nat_trans_eq, intro c, esimp,
      refine !assoc⁻¹ ⬝ ap (λx, _ ∘ x) (nf_fn_eq_fn_nf_pt η η' c) ⬝ !assoc ⬝ _,
      esimp, rewrite [-respect_comp G',H c,respect_id G',▸*,id_left]},
   { clear lem₁, refine transport_hom_of_eq_left _ ε ⬝ _,
     krewrite inv_of_eq_compose_left,
     rewrite functor.inv_of_eq_eq_of_pointwise_iso,
     apply nat_trans_eq, intro d, esimp,
     krewrite [respect_comp],
     rewrite [assoc,nf_fn_eq_fn_nf_pt ε' ε d,-assoc,▸*,H (G' d),id_right]}
   end

end category
