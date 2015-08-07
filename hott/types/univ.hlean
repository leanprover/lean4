/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Theorems about the universe
-/

-- see also init.ua

import .bool .trunc .lift

open is_trunc bool lift unit eq pi equiv equiv.ops sum

namespace univ

  universe variable u
  variables {A B : Type.{u}} {a : A} {b : B}

  /- Pathovers -/

  definition eq_of_pathover_ua {f : A ≃ B} (p : a =[ua f] b) : f a = b :=
  !cast_ua⁻¹ ⬝ tr_eq_of_pathover p

  definition pathover_ua {f : A ≃ B} (p : f a = b) : a =[ua f] b :=
  pathover_of_tr_eq (!cast_ua ⬝ p)

  definition pathover_ua_equiv (f : A ≃ B) : (a =[ua f] b) ≃ (f a = b) :=
  equiv.MK eq_of_pathover_ua
           pathover_ua
           abstract begin
             intro p, unfold [pathover_ua,eq_of_pathover_ua],
             rewrite [to_right_inv !pathover_equiv_tr_eq, inv_con_cancel_left]
           end end
           abstract begin
             intro p, unfold [pathover_ua,eq_of_pathover_ua],
             rewrite [con_inv_cancel_left, to_left_inv !pathover_equiv_tr_eq]
           end end

  /- Properties which can be disproven for the universe -/

  definition not_is_hset_type0 : ¬is_hset Type₀ :=
  assume H : is_hset Type₀,
  absurd !is_hset.elim eq_bnot_ne_idp

  definition not_is_hset_type.{v} : ¬is_hset Type.{v} :=
  assume H : is_hset Type,
  absurd (is_trunc_is_embedding_closed lift star) not_is_hset_type0

  --set_option pp.notation false
  definition not_double_negation_elimination0 : ¬Π(A : Type₀), ¬¬A → A :=
  begin
    intro f,
    have u : ¬¬bool, by exact (λg, g tt),
    let H1 := apdo f eq_bnot,
    let H2 := apo10 H1 u,
    have p : eq_bnot ▸ u = u, from !is_hprop.elim,
    rewrite p at H2,
    let H3 := eq_of_pathover_ua H2, esimp at H3, --TODO: use apply ... at after #700
    exact absurd H3 (bnot_ne (f bool u)),
  end

  definition not_double_negation_elimination : ¬Π(A : Type), ¬¬A → A :=
  begin
    intro f,
    apply not_double_negation_elimination0,
    intro A nna, refine down (f _ _),
    intro na,
    have ¬A, begin intro a, exact absurd (up a) na end,
    exact absurd this nna
  end

  definition not_excluded_middle : ¬Π(A : Type), A + ¬A :=
  begin
    intro f,
    apply not_double_negation_elimination,
    intro A nna,
    induction (f A) with a na,
      exact a,
      exact absurd na nna
  end


end univ
