/-
Copyright (c) 2015 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: types.trunc
Authors: Jakob von Raumer, Floris van Doorn

Properties of is_trunc
-/

import types.pi types.path

open sigma sigma.ops pi function eq equiv path funext

namespace is_trunc

  definition is_contr.sigma_char (A : Type) :
    (Σ (center : A), Π (a : A), center = a) ≃ (is_contr A) :=
  begin
    fapply equiv.mk,
     {intro S, apply is_contr.mk, exact S.2},
     {fapply is_equiv.adjointify,
       {intro H, apply sigma.mk, exact (@contr A H)},
       {intro H, apply (is_trunc.rec_on H), intro Hint,
        apply (contr_internal.rec_on Hint), intros (H1, H2),
        apply idp},
       {intro S, cases S, apply idp}}
  end

  definition is_trunc.pi_char (n : trunc_index) (A : Type) :
    (Π (x y : A), is_trunc n (x = y)) ≃ (is_trunc (n .+1) A) :=
  begin
    fapply equiv.mk,
      {intro H, apply is_trunc_succ_intro},
      {fapply is_equiv.adjointify,
        {intros (H, x, y), apply is_trunc_eq},
        {intro H, apply (is_trunc.rec_on H), intro Hint, apply idp},
        {intro P,
         unfold compose, apply eq_of_homotopy,
         exact sorry}},
  end

  definition is_hprop_is_trunc {n : trunc_index} :
    Π (A : Type), is_hprop (is_trunc n A) :=
  begin
    apply (trunc_index.rec_on n),
      {intro A,
       apply is_trunc_is_equiv_closed, apply equiv.to_is_equiv,
       apply is_contr.sigma_char,
       apply (@is_hprop.mk), intros,
       fapply sigma_eq, apply x.2,
       apply (@is_hprop.elim),
       apply is_trunc_pi, intro a,
       apply is_hprop.mk, intros (w, z),
       assert (H : is_hset A),
         {apply is_trunc_succ, apply is_trunc_succ,
          apply is_contr.mk, exact y.2},
       fapply (@is_hset.elim A _ _ _ w z)},
     {intros (n', IH, A),
      apply is_trunc_is_equiv_closed,
        apply equiv.to_is_equiv,
        apply is_trunc.pi_char},
  end

  definition is_trunc_succ_of_imp_is_trunc_succ {A : Type} {n : trunc_index} (H : A → is_trunc (n.+1) A)
      : is_trunc (n.+1) A :=
  @is_trunc_succ_intro _ _ (λx y, @is_trunc_eq _ _ (H x) x y)

  definition is_trunc_of_imp_is_trunc_of_leq {A : Type} {n : trunc_index} (Hn : -1 ≤ n)
      (H : A → is_trunc n A) : is_trunc n A :=
  trunc_index.rec_on n (λHn H, empty.rec _ Hn)
                       (λn IH Hn, is_trunc_succ_of_imp_is_trunc_succ)
                       Hn H

  definition is_hset_of_axiom_K {A : Type} (K : Π{a : A} (p : a = a), p = idp) : is_hset A :=
  is_hset.mk _ (λa b p q, eq.rec_on q K p)

  theorem is_hset_of_relation.{u} {A : Type.{u}} (R : A → A → Type.{u})
    (mere : Π(a b : A), is_hprop (R a b)) (refl : Π(a : A), R a a)
    (imp : Π{a b : A}, R a b → a = b) : is_hset A :=
  is_hset_of_axiom_K
    (λa p,
      have H2 : transport (λx, R a x → a = x) p (@imp a a) = @imp a a, from !apD,
      have H3 : Π(r : R a a), transport (λx, a = x) p (imp r)
                              = imp (transport (λx, R a x) p r), from
        to_fun (symm !heq_pi) H2,
      have H4 : imp (refl a) ⬝ p = imp (refl a), from
        calc
          imp (refl a) ⬝ p = transport (λx, a = x) p (imp (refl a)) : transport_paths_r
            ... = imp (transport (λx, R a x) p (refl a)) : H3
            ... = imp (refl a) : is_hprop.elim,
      cancel_left (imp (refl a)) _ _ H4)

  definition relation_equiv_eq {A : Type} (R : A → A → Type)
    (mere : Π(a b : A), is_hprop (R a b)) (refl : Π(a : A), R a a)
    (imp : Π{a b : A}, R a b → a = b) (a b : A) : R a b ≃ a = b :=
  @equiv_of_is_hprop _ _ _
    (@is_trunc_eq _ _ (is_hset_of_relation R mere refl @imp) a b)
    imp
    (λp, p ▹ refl a)

  local attribute not [reducible]
  definition is_hset_of_double_neg_elim {A : Type} (H : Π(a b : A), ¬¬a = b → a = b)
    : is_hset A :=
  is_hset_of_relation (λa b, ¬¬a = b) _ (λa n, n idp) H

  section
  open decidable
  definition is_hset_of_decidable_eq (A : Type)
    [H : Π(a b : A), decidable (a = b)] : is_hset A :=
  is_hset_of_double_neg_elim (λa b, by_contradiction)
  end

  definition is_trunc_of_axiom_K_of_leq {A : Type} (n : trunc_index) (H : -1 ≤ n)
    (K : Π(a : A), is_trunc n (a = a)) : is_trunc (n.+1) A :=
  @is_trunc_succ_intro _ _ (λa b, is_trunc_of_imp_is_trunc_of_leq H (λp, eq.rec_on p !K))

end is_trunc
