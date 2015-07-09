/-
Copyright (c) 2015 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Floris van Doorn

Proof of the theorem that (is_trunc n A) is a mere proposition
We prove this here to avoid circular dependency of files
We want to use this in .equiv; .equiv is imported by .function and .function is imported by .trunc
-/

import .pi

open equiv sigma sigma.ops eq function pi

namespace is_trunc
  definition is_contr.sigma_char (A : Type) :
    (Σ (center : A), Π (a : A), center = a) ≃ (is_contr A) :=
  begin
    fapply equiv.MK,
    { intro S, exact (is_contr.mk S.1 S.2)},
    { intro H, cases H with H', cases H' with ce co, exact ⟨ce, co⟩},
    { intro H, cases H with H', cases H' with ce co, exact idp},
    { intro S, cases S, apply idp}
  end

  definition is_trunc.pi_char (n : trunc_index) (A : Type) :
    (Π (x y : A), is_trunc n (x = y)) ≃ (is_trunc (n .+1) A) :=
  begin
    fapply equiv.MK,
    { intro H, apply is_trunc_succ_intro},
    { intro H x y, apply is_trunc_eq},
    { intro H, cases H, apply idp},
    { intro P, apply eq_of_homotopy, intro a, apply eq_of_homotopy, intro b,
      esimp [is_trunc_eq], esimp[compose,is_trunc_succ_intro],
      generalize (P a b), intro H, cases H, apply idp},
  end

  definition is_hprop_is_trunc [instance] (n : trunc_index) :
    Π (A : Type), is_hprop (is_trunc n A) :=
  begin
    induction n,
    { intro A,
      apply is_trunc_is_equiv_closed,
      { apply equiv.to_is_equiv, apply is_contr.sigma_char},
      apply is_hprop.mk, intros,
      fapply sigma_eq, apply x.2,
      apply is_hprop.elimo},
    { intro A,
      apply is_trunc_is_equiv_closed,
      apply equiv.to_is_equiv,
      apply is_trunc.pi_char},
  end
end is_trunc
