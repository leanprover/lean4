-- Copyright (c) 2015 Jakob von Raumer. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Jakob von Raumer
-- Truncation properties of truncatedness

import types.pi

open truncation sigma sigma.ops pi function eq equiv

namespace truncation

  definition is_contr.sigma_char (A : Type) :
    (Σ (center : A), Π (a : A), center = a) ≃ (is_contr A) :=
  begin
    fapply equiv.mk,
      intro S, apply is_contr.mk, exact S.2,
    fapply is_equiv.adjointify,
        intro H, apply sigma.mk, exact (@contr A H),
      intro H, apply (is_trunc.rec_on H), intro Hint,
      apply (contr_internal.rec_on Hint), intros (H1, H2),
      apply idp,
    intro S, apply (sigma.rec_on S), intros (H1, H2),
    apply idp,
  end

  set_option pp.implicit true
  definition is_trunc.pi_char (n : trunc_index) (A : Type) :
    (Π (x y : A), is_trunc n (x = y)) ≃ (is_trunc (n .+1) A) :=
  begin
    fapply equiv.mk,
      intro H, apply is_trunc_succ, exact H,
    fapply is_equiv.adjointify,
        intros (H, x, y), apply succ_is_trunc, exact H,
      intro H, apply (is_trunc.rec_on H), intro Hint, apply idp,
    intro P,
   exact sorry,
  end

  definition is_trunc_is_hprop {n : trunc_index} :
    Π (A : Type), is_hprop (is_trunc n A) :=
  begin
    apply (trunc_index.rec_on n),
      intro A,
      apply trunc_equiv, apply equiv.to_is_equiv,
      apply is_contr.sigma_char,
      apply (@is_hprop.mk), intros,
      fapply sigma.path, apply x.2,
      apply (@is_hprop.elim),
      apply trunc_pi, intro a,
      apply is_hprop.mk, intros (w, z),
      assert (H : is_hset A),
        apply trunc_succ, apply trunc_succ,
        apply is_contr.mk, exact y.2,
      fapply (@is_hset.elim A _ _ _ w z),
    intros (n', IH, A),
    apply trunc_equiv,
      apply equiv.to_is_equiv,
      apply is_trunc.pi_char,
    apply trunc_pi, intro a,
    apply trunc_pi, intro b,
    apply (IH (a = b)),
  end

end truncation
