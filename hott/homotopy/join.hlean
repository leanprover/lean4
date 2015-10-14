/-
Copyright (c) 2015 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer

Declaration of a join as a special case of a pushout
-/

import hit.pushout .susp

open eq prod equiv pushout is_trunc bool

namespace join

  definition join (A B : Type) : Type := @pushout (A × B) A B pr1 pr2

  definition jglue {A B : Type} (a : A) (b : B) := @glue (A × B) A B pr1 pr2 (a, b)

  protected definition is_contr (A B : Type) [HA : is_contr A] :
    is_contr (join A B) :=
  begin
    fapply is_contr.mk, exact inl (center A),
    intro x, induction x with a b, apply ap inl, apply center_eq,
    apply jglue, induction x with a b, apply pathover_of_tr_eq,
    apply concat, apply transport_eq_Fr, esimp, rewrite ap_id,
    generalize center_eq a, intro p, cases p, apply idp_con,
  end

  protected definition bool (A : Type) : join bool A ≃ susp A :=
  begin
    fapply equiv.MK, intro ba, induction ba with b a,
      induction b, exact susp.south, exact susp.north, exact susp.north,
      induction x with b a, esimp,
      induction b, apply inverse, apply susp.merid, exact a, reflexivity,
    intro s, induction s with m,
      exact inl tt, exact inl ff, exact (jglue tt m) ⬝ (jglue ff m)⁻¹,
    intros, induction b with m, do 2 reflexivity, esimp,
      apply eq_pathover, apply hconcat, apply hdeg_square, apply concat,
      apply ap_compose' (pushout.elim _ _ _), apply concat,
        apply ap (ap (pushout.elim _ _ _)), apply susp.elim_merid, apply ap_con,
      apply hconcat, apply vconcat, apply hdeg_square, apply elim_glue,
        apply hdeg_square, apply ap_inv, esimp,
      apply hconcat, apply hdeg_square, apply concat, apply idp_con,
        apply concat, apply ap inverse, apply elim_glue, apply inv_inv,
      apply hinverse, apply hdeg_square, apply ap_id,
    intro x, induction x with b a, induction b, do 2 reflexivity,
      esimp, apply jglue, induction x with b a, induction b, esimp,
      apply eq_pathover, rewrite ap_id,
      apply eq_hconcat, apply concat, apply ap_compose' (susp.elim _ _ _),
        apply concat, apply ap (ap _) !elim_glue,
        apply concat, apply ap_inv, 
        apply concat, apply ap inverse !susp.elim_merid,
        apply concat, apply con_inv, apply ap (λ x, x ⬝ _) !inv_inv,
      apply square_of_eq_top, apply inverse, 
        apply concat, apply ap (λ x, x ⬝ _) !con.assoc,
        rewrite [con.left_inv, con_idp], apply con.right_inv,
      esimp, apply eq_pathover, rewrite ap_id,
      apply eq_hconcat, apply concat, apply ap_compose' (susp.elim _ _ _),
        apply concat, apply ap (ap _) !elim_glue, esimp, reflexivity,
      apply square_of_eq_top, rewrite idp_con, apply !con.right_inv⁻¹,   
  end

  set_option unifier.max_steps 40000
  protected definition assoc (A B C : Type) :
    join (join A B) C ≃ join A (join B C) :=
  begin
    fapply equiv.MK,
    { intro x, induction x with ab c, induction ab with a b,
      exact inl a, exact inr (inl b),
      induction x with a b, apply jglue, exact inr (inr c),
      induction x with ab c, induction ab with a b, apply jglue,
      apply ap inr, apply jglue, induction x with a b, 
      let H := apdo (jglue a) (jglue b c), esimp at H, esimp,
      let H' := transpose (square_of_pathover H), esimp at H',
      rewrite ap_constant at H', apply eq_pathover, 
      krewrite [elim_glue, ap_constant], esimp,
      apply square_of_eq, apply concat, rotate 1, exact eq_of_square H',
      rewrite [con_idp, idp_con],
    },
    { intro x, induction x with a bc, exact inl (inl a),
      induction bc with b c, exact inl (inr b), exact inr c,
      induction x with b c, apply jglue, esimp,
      induction x with a bc, induction bc with b c,
      apply ap inl, apply jglue, apply jglue, induction x with b c,
      let H := apdo (λ x, jglue x c) (jglue a b), esimp at H, esimp,
      let H' := transpose (square_of_pathover H), esimp at H',
      rewrite ap_constant at H', apply eq_pathover,
      krewrite [elim_glue, ap_constant], esimp,
      apply square_of_eq, apply concat, exact eq_of_square H',
      rewrite [con_idp, idp_con],
    },
    { intro x, induction x with a bc, reflexivity,
      induction bc with b c, reflexivity, reflexivity,
      induction x with b c, esimp, apply eq_pathover,
      apply hdeg_square, esimp,
      apply concat, apply ap_compose' (pushout.elim _ _ _),
      apply concat, apply ap (ap _), apply elim_glue, esimp,
      apply concat, apply elim_glue, esimp,
      induction x with a bc, induction bc with b c, esimp,
      apply eq_pathover, apply hdeg_square, esimp,
      apply concat, apply ap_compose' (pushout.elim _ _ _),
      apply concat, apply ap (ap _), krewrite elim_glue, reflexivity,
      apply inverse, apply concat, apply ap_id,
      apply inverse, apply concat, apply inverse, 
      apply ap_compose' (pushout.elim _ _ _), apply elim_glue,
      esimp, apply eq_pathover, apply hdeg_square,
      apply concat, apply ap_compose' (pushout.elim _ _ _),
      apply concat, apply ap (ap _), krewrite elim_glue, reflexivity,
      apply inverse, apply concat, apply ap_id,
      apply inverse, apply concat,
      --apply ap_compose' (pushout.elim _ _ _),
    },
  end
  check elim_glue
  check pushout.elim

end join
